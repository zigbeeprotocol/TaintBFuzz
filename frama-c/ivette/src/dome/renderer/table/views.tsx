/* ************************************************************************ */
/*                                                                          */
/*   This file is part of Frama-C.                                          */
/*                                                                          */
/*   Copyright (C) 2007-2022                                                */
/*     CEA (Commissariat à l'énergie atomique et aux énergies               */
/*          alternatives)                                                   */
/*                                                                          */
/*   you can redistribute it and/or modify it under the terms of the GNU    */
/*   Lesser General Public License as published by the Free Software        */
/*   Foundation, version 2.1.                                               */
/*                                                                          */
/*   It is distributed in the hope that it will be useful,                  */
/*   but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/*   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          */
/*   GNU Lesser General Public License for more details.                    */
/*                                                                          */
/*   See the GNU Lesser General Public License version 2.1                  */
/*   for more details (enclosed in the file licenses/LGPLv2.1).             */
/*                                                                          */
/* ************************************************************************ */

/* eslint-disable @typescript-eslint/no-explicit-any */

// --------------------------------------------------------------------------
// --- Tables
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/table/views
 */

import React, { ReactNode } from 'react';
import { forEach, debounce, throttle } from 'lodash';
import isEqual from 'react-fast-compare';
import * as Dome from 'dome';
import * as Json from 'dome/data/json';
import * as Settings from 'dome/data/settings';
import { DraggableCore } from 'react-draggable';
import {
  AutoSizer, Size,
  SortDirection, SortDirectionType,
  Index, IndexRange,
  Table as VTable,
  Column as VColumn,
  TableHeaderRowProps,
  TableHeaderProps,
  TableCellDataGetter,
  TableCellProps,
  TableCellRenderer,
  RowMouseEventHandlerParams,
} from 'react-virtualized';

import { SVG as SVGraw } from 'dome/controls/icons';
import { Trigger, Client, Sorting, SortingInfo, Model } from './models';

import './style.css';

const D = new Dome.Debug('Dome.table');
const SVG = SVGraw as (props: { id: string; size?: number }) => JSX.Element;

// --------------------------------------------------------------------------
// --- Rendering Interfaces
// --------------------------------------------------------------------------

/** Cell data renderer. */
export type Renderer<Cell> = (data: Cell) => null | JSX.Element;

/**
   Associates, for each field `{ fd: Cell }` in `Row`, a renderer
   for type `Cell`.
 */
export type RenderByFields<Row> = {
  [fd in keyof Row]?: Renderer<Row[fd]>;
};

// --------------------------------------------------------------------------
// --- Table Columns
// --------------------------------------------------------------------------

/**
   Column position.
   You may use hierarchical index to order columns.
   See [[ColumnGroup]].
 */
export type index = number | number[];

/**
   Column Properties.

   __Warning:__ callback properties, namely `getter`, `render`
   and `onContextMenu`, shall be as stable as possible to prevent
   the table from constantly re-rendering.
   Use constant callbacks whenever possible, or memoize them with
   `React.useCallback()` hook.

   @template Row - table row data of some table entries
   @template Cell - type of cell data to render in this column
 */
export interface ColumnProps<Row, Cell> {
  /** Column identifier. */
  id: string;
  /** Header icon. */
  icon?: string;
  /** Header label. */
  label?: string;
  /** Header title. */
  title?: string;
  /**
     Column position.
     By default, column will appear according to their mounting order.
     See also [[ColumnGroup]].
   */
  index?: index;
  /** CSS vertical alignment on cells. */
  align?: 'left' | 'center' | 'right';
  /** Column base width in pixels (default 60px). */
  width?: number;
  /** Extensible column (not by default). */
  fill?: boolean;
  /** Fixed width column (not by default). */
  fixed?: boolean;
  /**
     Data Key for this column. Defaults to `id`. It is used for:
     - triggering ordering events to the model, if enabled.
     - using by-fields table renderers, if provided.
   */
  dataKey?: string;
  /**
     Disable model sorting, even if enabled by the model
     for this column `dataKey`. Not by default.
   */
  disableSort?: boolean;
  /**
     Default column visibility. With `'never'` or `'always'` the column
     visibility is forced and can not be modified by the user. Otherwize,
     the user can change visibility through the column header context menu.
   */
  visible?: boolean | 'never' | 'always';
  /**
     Data getter for this column.
     Shall be constant or protected by `React.useCallback`.
   */
  getter?: (row: Row, dataKey: string) => Cell | undefined;
  /**
     Override table by-fields cell renderers.
     Shall be constant or protected by `React.useCallback`.
   */
  render?: Renderer<Cell>;
  /**
     Override table right-click callback.
     Shall be constant or protected by `React.useCallback`.
   */
  onContextMenu?: (row: Row, index: number, dataKey: string) => void;
}

// --------------------------------------------------------------------------
// --- Table Properties
// --------------------------------------------------------------------------

/**
   @template Key - unique identifiers of table entries
   @template Row - data associated to each key in the table entries
 */
export interface TableProps<Key, Row> {
  /** Data proxy. */
  model: Model<Key, Row>;
  /** Sorting Proxy. */
  sorting?: Sorting;
  /** Rendering by Fields. */
  rendering?: RenderByFields<Row>;
  /** Window settings to store the size and visibility of columns. */
  settings?: string;
  /** Selected row (identified by key). */
  selection?: Key;
  /** Selection callback. */
  onSelection?: (row: Row, key: Key, index: number) => void;
  /** Context menu callback. */
  onContextMenu?: (row: Row, index: number) => void;
  /** Fallback for rendering an empty table. */
  renderEmpty?: () => null | JSX.Element;
  /** Shall only contains `<Column<Row> … />` elements. */
  children?: React.ReactElement | React.ReactElement[];
}

// --------------------------------------------------------------------------
// --- React-Virtualized Interfaces
// --------------------------------------------------------------------------

type divRef = React.RefObject<HTMLDivElement>;
type tableRef = React.RefObject<VTable>;

interface ColumnData {
  icon?: string;
  label?: string;
  title?: string;
  headerMenu: () => void;
  headerRef: divRef;
}

interface PopupItem {
  label: string;
  checked?: boolean;
  enabled?: boolean;
  display?: boolean;
  onClick?: Trigger;
}

type PopupMenu = ('separator' | PopupItem)[];

type Cmap<A> = Map<string, A>;
type ColProps<R> = ColumnProps<R, any>;
type Cprops = ColProps<any>;

// --------------------------------------------------------------------------
// --- Column Utilities
// --------------------------------------------------------------------------

const isVisible = (visible: Cmap<boolean>, col: Cprops): boolean => {
  const defaultVisible = col.visible ?? true;
  switch (defaultVisible) {
    case 'never': return false;
    case 'always': return false;
    default:
      return visible.get(col.id) ?? defaultVisible;
  }
};

const defaultGetter = (row: any, dataKey: string): any => {
  if (typeof row === 'object') return row[dataKey];
  return undefined;
};

const defaultRenderer = (d: any): JSX.Element => (
  <div className="dome-xTable-renderer dome-text-label">
    {String(d)}
  </div>
);

function makeRowGetter<Key, Row>(model?: Model<Key, Row>) {
  return ({ index }: Index) => model && model.getRowAt(index);
}

function makeDataGetter(
  dataKey: string,
  getter: ((row: any, dataKey: string) => any) = defaultGetter,
): TableCellDataGetter {
  return (({ rowData }) => {
    try {
      if (rowData !== undefined) return getter(rowData, dataKey);
    } catch (err) {
      D.error(
        'custom getter error',
        'rowData:', rowData,
        'dataKey:', dataKey,
        err,
      );
    }
    return undefined;
  });
}

function makeDataRenderer(
  render: ((data: any) => ReactNode) = defaultRenderer,
  onContextMenu?: (row: any, index: number, dataKey: string) => void,
): TableCellRenderer {
  return function TableCell(props: TableCellProps) {
    const { cellData } = props;
    try {
      const contents = cellData ? render(cellData) : null;
      if (onContextMenu) {
        const callback = (evt: React.MouseEvent): void => {
          evt.stopPropagation();
          onContextMenu(props.rowData, props.rowIndex, props.dataKey);
        };
        return (<div onContextMenu={callback}>{contents}</div>);
      }
      return contents;
    } catch (err) {
      D.error(
        'custom renderer error',
        'dataKey:', props.dataKey,
        'cellData:', cellData,
        err,
      );
      return null;
    }
  };
}

// --------------------------------------------------------------------------
// --- Table Settings
// --------------------------------------------------------------------------

type TableSettings = {
  resize?: Json.dict<number>;
  visible?: Json.dict<boolean>;
};

const jTableSettings = Json.jObject({
  resize: Json.jDict(Json.jNumber),
  visible: Json.jDict(Json.jBoolean),
});

// --------------------------------------------------------------------------
// --- Table State
// --------------------------------------------------------------------------

class TableState<Key, Row> {

  settings?: string; // User settings
  signal?: Trigger; // Full reload
  width?: number; // Current table width
  offset?: number; // Current resizing offset
  resizing?: number; // Currently dragging resizer
  resize: Cmap<number> = new Map(); // Current resizing wrt. dragging
  visible: Cmap<boolean> = new Map(); // Current
  headerRef: Cmap<divRef> = new Map(); // Once, build on demand
  columnWith: Cmap<number> = new Map(); // DOM column element width without dragging
  tableRef: tableRef = React.createRef(); // Once, global
  getter: Cmap<TableCellDataGetter> = new Map(); // Computed from registry
  render: Cmap<TableCellRenderer> = new Map(); // Computed from registry and getterFields
  rowGetter: (info: Index) => Row | undefined; // Computed from last fetching
  rendering?: RenderByFields<Row>; // Last user props used for computing renderers
  model?: Model<Key, Row>; // Last user proxy used for computing getter
  sorting?: Sorting; // Last user proxy used for sorting
  client?: Client; // Client of last fetching
  columns: ColProps<Row>[] = []; // Currently known columns
  scrolledKey?: Key; // Lastly scrolled key
  selectedIndex?: number; // Current selected index
  sortBy?: string; // last sorting dataKey
  sortDirection?: SortDirectionType; // last sorting direction
  onContextMenu?: (row: Row, index: number) => void; // context menu callback
  range?: IndexRange;
  rowCount = 0;

  constructor() {
    this.unwind = this.unwind.bind(this);
    this.forceUpdate = throttle(this.forceUpdate.bind(this), 200);
    this.updateGrid = throttle(this.updateGrid.bind(this), 200);
    this.fullReload = this.fullReload.bind(this);
    this.onRowsRendered = this.onRowsRendered.bind(this);
    this.rowClassName = this.rowClassName.bind(this);
    this.onHeaderMenu = this.onHeaderMenu.bind(this);
    this.onRowClick = this.onRowClick.bind(this);
    this.onRowRightClick = this.onRowRightClick.bind(this);
    this.onKeyDown = this.onKeyDown.bind(this);
    this.onSorting = this.onSorting.bind(this);
    this.rebuild = debounce(this.rebuild.bind(this), 5);
    this.rowGetter = makeRowGetter();
  }

  // --- Static Callbacks

  unwind(): void {
    this.signal = undefined;
    this.onSelection = undefined;
    this.onContextMenu = undefined;
  }

  forceUpdate(): void {
    const s = this.signal;
    if (s) { this.signal = undefined; s(); }
  }

  updateGrid(): void {
    this.tableRef.current?.forceUpdateGrid();
  }

  fullReload(): void {
    this.scrolledKey = undefined;
    this.forceUpdate();
    this.updateGrid();
  }

  getRef(id: string): divRef {
    const href = this.headerRef.get(id);
    if (href) return href;
    const nref: divRef = React.createRef();
    this.headerRef.set(id, nref);
    return nref;
  }

  // --- Computing Column Size

  computeWidth(id: string): number | undefined {
    const cwidth = this.columnWith;
    if (this.resizing !== undefined) return cwidth.get(id);
    const elt = this.headerRef.get(id)?.current?.parentElement;
    const cw = elt?.getBoundingClientRect()?.width;
    if (cw) cwidth.set(id, cw);
    return cw;
  }

  startResizing(idx: number): void {
    this.resizing = idx;
    this.offset = 0;
    this.forceUpdate();
  }

  stopResizing(): void {
    this.resizing = undefined;
    this.offset = undefined;
    this.columnWith.clear();
    this.updateSettings();
  }

  // Debounced
  setResizeOffset(lcol: string, rcol: string, offset: number): void {
    const colws = this.columnWith;
    const cwl = colws.get(lcol);
    const cwr = colws.get(rcol);
    const wl = cwl ? cwl + offset : 0;
    const wr = cwr ? cwr - offset : 0;
    if (wl > 25 && wr > 25) {
      const { resize } = this;
      resize.set(lcol, wl);
      resize.set(rcol, wr);
      this.offset = offset;
      this.forceUpdate(); // no settings yet, onStop only
    }
  }

  // --- Table settings

  updateSettings(): void {
    const userSettings = this.settings;
    if (userSettings) {
      const cws: Json.dict<number> = {};
      const cvs: Json.dict<boolean> = {};
      const { resize } = this;
      const { visible } = this;
      this.columns.forEach(({ id }) => {
        const cw = resize.get(id);
        const cv = visible.get(id);
        if (cw !== undefined) cws[id] = cw;
        if (cv !== undefined) cvs[id] = cv;
      });
      const theSettings: TableSettings = { resize: cws, visible: cvs };
      Settings.setWindowSettings(userSettings, theSettings);
    }
    this.forceUpdate();
  }

  importSettings(settings?: string): void {
    if (settings !== this.settings) {
      this.settings = settings;
      const { resize } = this;
      const { visible } = this;
      resize.clear();
      visible.clear();
      const theSettings: undefined | TableSettings =
        Settings.getWindowSettings(settings, jTableSettings, undefined);
      if (theSettings) {
        forEach(theSettings.resize, (cw, cid) => {
          if (typeof cw === 'number') this.resize.set(cid, cw);
        });
        forEach(theSettings.visible, (cv, cid) => {
          if (typeof cv === 'boolean') this.visible.set(cid, cv);
        });
        this.forceUpdate();
      }
    }
  }

  // --- User Table properties

  setSorting(sorting?: Sorting): void {
    const info = sorting?.getSorting();
    this.sortBy = info?.sortBy;
    this.sortDirection = info?.sortDirection;
    if (sorting !== this.sorting) {
      this.sorting = sorting;
      this.fullReload();
    }
  }

  setModel(model?: Model<Key, Row>): void {
    if (model !== this.model) {
      this.client?.unlink();
      this.model = model;
      if (model) {
        const client = model.link();
        client.onReload(this.fullReload);
        client.onUpdate(this.updateGrid);
        this.client = client;
      } else {
        this.client = undefined;
      }
      this.rowGetter = makeRowGetter(model);
      this.fullReload();
    }
  }

  setRendering(rendering?: RenderByFields<Row>): void {
    if (rendering !== this.rendering) {
      this.rendering = rendering;
      this.render.clear();
      this.fullReload();
    }
  }

  // ---- Selection Management

  onSelection?: (data: Row, key: Key, index: number) => void;

  onRowClick(info: RowMouseEventHandlerParams): void {
    const { index } = info;
    const data = info.rowData as (Row | undefined);
    const { model } = this;
    const key =
      (data !== undefined) ? model?.getKeyFor(index, data) : undefined;
    const { onSelection } = this;
    if (key !== undefined && data !== undefined && onSelection)
      onSelection(data, key, index);
  }

  onRowsRendered(info: IndexRange): void {
    this.range = info;
    this.client?.watch(info.startIndex, info.stopIndex);
  }

  rowClassName({ index }: Index): string {
    if (this.selectedIndex === index) return 'dome-xTable-selected';
    return (index & 1 ? 'dome-xTable-even' : 'dome-xTable-odd'); // eslint-disable-line no-bitwise
  }

  keyStepper(index: number): void {
    const { onSelection } = this;
    const key = this.model?.getKeyAt(index);
    const data = this.model?.getRowAt(index);
    if (key !== undefined && data !== undefined && onSelection) {
      onSelection(data, key, index);
    }
  }

  scrollToIndex(selection: Key | undefined): number | undefined {
    const index = selection && this.model?.getIndexOf(selection);
    this.selectedIndex = index;
    if (this.scrolledKey !== selection) {
      this.scrolledKey = selection;
      if (selection) return index;
    }
    return undefined;
  }

  onSorting(ord?: SortingInfo): void {
    const { sorting } = this;
    if (sorting) {
      sorting.setSorting(ord);
      this.sortBy = ord?.sortBy;
      this.sortDirection = ord?.sortDirection;
      this.forceUpdate();
    }
  }

  // ---- Row Events

  onRowRightClick({ event, rowData, index }: RowMouseEventHandlerParams): void {
    const callback = this.onContextMenu;
    if (callback) {
      event.stopPropagation();
      callback(rowData, index);
    }
  }

  onKeyDown(evt: React.KeyboardEvent): void {
    const index = this.selectedIndex;
    switch (evt.key) {
      case 'ArrowUp':
        if (index !== undefined) {
          this.keyStepper(index - 1);
          evt.preventDefault();
        }
        break;
      case 'ArrowDown':
        if (index !== undefined) {
          this.keyStepper(index + 1);
          evt.preventDefault();
        }
        break;
    }
  }

  // ---- Header Context Menu

  onHeaderMenu(): void {
    let hasOrder = false;
    let hasResize = false;
    let hasVisible = false;
    const { visible } = this;
    const { columns } = this;
    columns.forEach((col) => {
      if (!col.disableSort) hasOrder = true;
      if (!col.fixed) hasResize = true;
      if (col.visible !== 'never' && col.visible !== 'always')
        hasVisible = true;
    });
    const resetSizing = (): void => {
      this.resize.clear();
      this.updateSettings();
    };
    const resetColumns = (): void => {
      this.visible.clear();
      this.resize.clear();
      this.updateSettings();
    };
    const items: PopupMenu = [
      {
        label: 'Reset ordering',
        display: hasOrder && this.sorting,
        onClick: this.onSorting,
      },
      {
        label: 'Reset column widths',
        display: hasResize,
        onClick: resetSizing,
      },
      {
        label: 'Restore column defaults',
        display: hasVisible,
        onClick: resetColumns,
      },
      'separator',
    ];
    columns.forEach((col) => {
      switch (col.visible) {
        case 'never':
        case 'always':
          break;
        default: {
          const { id, label, title } = col;
          const checked = isVisible(visible, col);
          const onClick = (): void => {
            visible.set(id, !checked);
            this.updateSettings();
          };
          items.push({ label: label || title || id, checked, onClick });
        }
      }
    });
    Dome.popupMenu(items);
  }

  // --- Getter & Setters

  computeGetter(
    id: string,
    dataKey: string,
    props: Cprops
  ): TableCellDataGetter {
    const current = this.getter.get(id);
    if (current) return current;
    const dataGetter = makeDataGetter(dataKey, props.getter);
    this.getter.set(id, dataGetter);
    return dataGetter;
  }

  computeRender(
    id: string,
    dataKey: string,
    props: Cprops
  ): TableCellRenderer {
    const current = this.render.get(id);
    if (current) return current;
    let renderer = props.render;
    if (!renderer) {
      const rdr = this.rendering;
      if (rdr) renderer = (rdr as any)[dataKey];
    }
    const cellRenderer = makeDataRenderer(renderer, props.onContextMenu);
    this.render.set(id, cellRenderer);
    return cellRenderer;
  }

  // --- User Column Registry

  private registry = new Map<string, null | ColProps<Row>>();

  setRegistry(id: string, props: null | ColProps<Row>): void {
    this.registry.set(id, props);
    this.rebuild();
  }

  useColumn(
    props: ColProps<Row>,
    path: number[],
    index: number,
  ): Trigger {
    const { id } = props;
    const theIndex = props.index ?? index;
    const thePath = path.concat(theIndex);
    this.setRegistry(id, { ...props, index: thePath });
    return () => this.setRegistry(id, null);
  }

  rebuild(): void {
    const current = this.columns;
    const cols: ColProps<Row>[] = [];
    this.registry.forEach((col) => col && cols.push(col));
    if (!isEqual(current, cols)) {
      this.getter.clear();
      this.render.clear();
      this.columns = cols;
      this.fullReload();
    }
  }
}

// --------------------------------------------------------------------------
// --- Columns Components
// --------------------------------------------------------------------------

interface ColumnIndex {
  state: TableState<any, any>;
  path: number[];
  index: number;
}

const ColumnContext = React.createContext<undefined | ColumnIndex>(undefined);

/**
   Table Column.

   @template Row - table row data of some table entries
   @template Cell - type of cell data to render in this column
 */
export function Column<Row, Cell>(
  props: ColumnProps<Row, Cell>
): JSX.Element | null {
  const context = React.useContext(ColumnContext);
  React.useEffect(() => {
    if (context) {
      const { state, path, index } = context;
      state.useColumn(props, path, index);
    }
  });
  return null;
}

function spawnIndex(
  state: TableState<any, any>,
  path: number[],
  children: React.ReactElement | React.ReactElement[],
): JSX.Element {
  const indexChild = (elt: React.ReactElement, k: number): JSX.Element => (
    <ColumnContext.Provider value={{ state, path, index: k }}>
      {elt}
    </ColumnContext.Provider>
  );
  return <>{React.Children.map(children, indexChild)}</>;
}

export interface ColumnGroupProps {
  index?: index;
  children?: React.ReactElement | React.ReactElement[];
}

/** Column Groups.

   You should use this component in replacement of React fragments rendering
   several columns:

 * ```ts
 *  function MyCustomColumn(props) {
 *    ...
 *    return (
 *       <ColumnGroup>
 *          <Column id='A' index={3} ... />
 *          <Column id='B'           ... />
 *          <MyOtherCustomColumns    ... />
 *          <Column id='C' index={0} ... />
 *        </ColumnGroup>
 *      );
 *   }
 * ```

   When rendering a column or a column group, there is an implicit column
   indexing context which is provided by the parent Table component and
   propagated down to the virtual DOM.  This context provides each column and
   column group with a default index position, which can be locally adjusted
   with the `index` property.

   More precisely, if a column group is assigned to index `K` by the inherited
   context, its `i`-th child will inherit a refined indexing context
   corresponding to index `[...K, i]`. Then, inside this refined context, a
   column or column-group rendered from the `i`-th child of the column group
   with be assigned to a default index of `[...K, i]`, or a refined index of
   `[...K, ...index]` if it the sub-column or sub-column-group has an `index`
   property.

   This indexing context allows you to number columns locally inside a
   `<ColumnGroup />` without having to take into account its neighbours. This
   also means that columns rendered in a group never goes outside of this group.
   Column groups hence provide hierarchical column ordering.

   The immediate children of a Table component are implicitely rendered in a
   column group initialized at index `[i]` for the `i`-th child. To cancel
   this implicit root column group, just pack your columns inside a classical
   React fragment: `<Table … ><>{children}</></Table>`.
 */
export function ColumnGroup(props: ColumnGroupProps): JSX.Element | null {
  const context = React.useContext(ColumnContext);
  if (!context) return null;
  const { state, path, index: defaultIndex } = context;
  const newPath = path.concat(props.index ?? defaultIndex);
  const { children } = props;
  return children ? spawnIndex(state, newPath, children) : null;
}

// --------------------------------------------------------------------------
// --- Virtualized Column
// --------------------------------------------------------------------------

function makeColumn<Key, Row>(
  state: TableState<Key, Row>,
  props: ColProps<Row>,
  fill: boolean,
): JSX.Element {
  const { id } = props;
  const align = { textAlign: props.align };
  const dataKey = props.dataKey ?? id;
  const columnData: ColumnData = {
    icon: props.icon,
    label: props.label,
    title: props.title,
    headerMenu: state.onHeaderMenu,
    headerRef: state.getRef(id),
  };
  const width = state.resize.get(id) || props.width || 60;
  const flexGrow = fill ? 1 : 0;
  const { sorting } = state;
  const disableSort =
    props.disableSort || !sorting || !sorting.canSortBy(dataKey);
  const getter = state.computeGetter(id, dataKey, props);
  const render = state.computeRender(id, dataKey, props);
  return (
    <VColumn
      key={id}
      width={width}
      flexGrow={flexGrow}
      dataKey={dataKey}
      columnData={columnData}
      headerRenderer={headerRenderer}
      cellDataGetter={getter}
      cellRenderer={render}
      headerStyle={align}
      disableSort={disableSort}
      style={align}
    />
  );
}

const byIndex = (a: Cprops, b: Cprops): number => {
  const ak = a.index ?? 0;
  const bk = b.index ?? 0;
  if (ak < bk) return -1;
  if (bk < ak) return 1;
  return 0;
};

function makeCprops<Key, Row>(state: TableState<Key, Row>): Cprops[] {
  const cols: Cprops[] = [];
  state.columns.forEach((col) => {
    if (col && isVisible(state.visible, col)) {
      cols.push(col);
    }
  });
  cols.sort(byIndex);
  return cols;
}

function makeColumns<Key, Row>(
  state: TableState<Key, Row>,
  cols: Cprops[]
): JSX.Element[] {
  let fill: undefined | Cprops;
  let lastExt: undefined | Cprops;
  cols.forEach((col) => {
    if (col.fill && !fill) fill = col;
    if (!col.fixed) lastExt = col;
  });
  const n = cols.length;
  if (0 < n && !fill) fill = lastExt || cols[n - 1];
  return cols.map((col) => makeColumn(state, col, col === fill));
}

// --------------------------------------------------------------------------
// --- Table Utility Renderers
// --------------------------------------------------------------------------

const headerIcon = (icon?: string): JSX.Element | null => (
  icon ?
    (
      <div className="dome-xTable-header-icon">
        <SVG id={icon} />
      </div>
    ) : null
);

const headerLabel = (label?: string): JSX.Element | null => (
  label ?
    (
      <label className="dome-xTable-header-label dome-text-label">
        {label}
      </label>
    ) : null
);

const makeSorter = (id: string): JSX.Element => (
  <div className="dome-xTable-header-sorter">
    <SVG id={id} size={8} />
  </div>
);

const sorterASC = makeSorter('ANGLE.UP');
const sorterDESC = makeSorter('ANGLE.DOWN');

function headerRowRenderer(props: TableHeaderRowProps): JSX.Element {
  return (
    <div
      role="row"
      className={props.className}
      style={props.style}
    >
      {props.columns}
    </div>
  );
}

function headerRenderer(props: TableHeaderProps): JSX.Element {
  const data: ColumnData = props.columnData;
  const { sortBy, sortDirection, dataKey } = props;
  const { icon, label, title, headerRef, headerMenu } = data;
  const sorter =
    dataKey === sortBy
      ? (sortDirection === SortDirection.ASC ? sorterASC : sorterDESC)
      : undefined;
  return (
    <div
      className="dome-xTable-header"
      title={title}
      ref={headerRef}
      onContextMenu={headerMenu}
    >
      {headerIcon(icon)}
      {headerLabel(label)}
      {sorter}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- Column Resizer
// --------------------------------------------------------------------------

const DRAGGING = 'dome-xTable-resizer dome-color-dragging';
const DRAGZONE = 'dome-xTable-resizer dome-color-dragzone';

interface ResizerProps {
  dragging: boolean; // Currently dragging
  position: number; // drag-start offset
  offset: number; // current offset
  onStart: Trigger;
  onStop: Trigger;
  onDrag: (offset: number) => void;
}

const Resizer = (props: ResizerProps): JSX.Element => (
  <DraggableCore
    onStart={props.onStart}
    onStop={props.onStop}
    onDrag={(_elt, data) => props.onDrag(data.x - props.position)}
  >
    <div
      className={props.dragging ? DRAGGING : DRAGZONE}
      style={{ left: props.position + props.offset - 2 }}
    />
  </DraggableCore>
);

type ResizeInfo = { id: string; fixed: boolean; left?: string; right?: string };

function makeResizers(
  state: TableState<any, any>,
  columns: Cprops[],
): null | JSX.Element[] {
  if (columns.length < 2) return null;
  const resizing: ResizeInfo[] =
    columns.map(({ id, fixed = false }) => ({ id, fixed }));
  let k: number; let
    cid; // last non-fixed from left/right
  for (cid = undefined, k = 0; k < columns.length; k++) {
    const r = resizing[k];
    r.left = cid;
    if (!r.fixed) cid = r.id;
  }
  for (cid = undefined, k = columns.length - 1; 0 <= k; k--) {
    const r = resizing[k];
    r.right = cid;
    if (!r.fixed) cid = r.id;
  }
  const cwidth = columns.map((col) => state.computeWidth(col.id));
  let position = 0; const
    resizers = [];
  for (k = 0; k < columns.length - 1; k++) {
    const width = cwidth[k];
    if (!width) return null;
    position += width;
    const a = resizing[k];
    const b = resizing[k + 1];
    if ((!a.fixed || !b.fixed) && a.right && b.left) {
      const index = k; // Otherwize use dynamic value of k
      const rcol = a.right;
      const lcol = b.left;
      const offset = state.offset ?? 0;
      const dragging = state.resizing === index;
      const onStart = (): void => state.startResizing(index);
      const onStop = (): void => state.stopResizing();
      const onDrag =
        (ofs: number): void => state.setResizeOffset(lcol, rcol, ofs);
      const resizer = (
        <Resizer
          key={index}
          dragging={dragging}
          position={position}
          offset={offset}
          onStart={onStart}
          onStop={onStop}
          onDrag={onDrag}
        />
      );
      resizers.push(resizer);
    }
  }
  return resizers;
}

// --------------------------------------------------------------------------
// --- Virtualized Table View
// --------------------------------------------------------------------------

// Must be kept in sync with table.css
const CSS_HEADER_HEIGHT = 22;
const CSS_ROW_HEIGHT = 20;

// Modifies state in place
function makeTable<Key, Row>(
  props: TableProps<Key, Row>,
  state: TableState<Key, Row>,
  size: Size,
): JSX.Element {

  const { width, height } = size;
  const { model } = props;
  const itemCount = model.getRowCount();
  const tableHeight = CSS_HEADER_HEIGHT + CSS_ROW_HEIGHT * itemCount;
  const smallHeight = itemCount > 0 && tableHeight < height;
  const rowCount = (smallHeight ? itemCount + 1 : itemCount);
  const scrollTo = state.scrollToIndex(props.selection);
  const cprops = makeCprops(state);
  const columns = makeColumns(state, cprops);
  const resizers = makeResizers(state, cprops);

  state.rowCount = rowCount;
  if (state.width !== width) {
    state.width = width;
    setImmediate(state.forceUpdate);
  }

  return (
    <div onKeyDown={state.onKeyDown}>
      <VTable
        ref={state.tableRef}
        key="table"
        displayName="React-Virtualized-Table"
        width={width}
        height={height}
        rowCount={rowCount}
        noRowsRenderer={props.renderEmpty}
        rowGetter={state.rowGetter}
        rowClassName={state.rowClassName}
        rowHeight={CSS_ROW_HEIGHT}
        headerHeight={CSS_HEADER_HEIGHT}
        headerRowRenderer={headerRowRenderer}
        onRowsRendered={state.onRowsRendered}
        onRowClick={state.onRowClick}
        onRowRightClick={state.onRowRightClick}
        sortBy={state.sortBy}
        sortDirection={state.sortDirection}
        sort={state.onSorting}
        scrollToIndex={scrollTo}
        scrollToAlignment="auto"
      >
        {columns}
      </VTable>
      {resizers}
    </div>
  );
}

// --------------------------------------------------------------------------
// --- Table View
// --------------------------------------------------------------------------

/** Table View.

   This component is base on
   [React-Virtualized](https://bvaughn.github.io/react-virtualized)
   which offers a super-optimized lazy rendering process that scales on huge
   datasets.

   A table shall be connected to an instance of [[Model]] class to retrieve the
   data and get informed of data updates.

   The table children shall only be component finally rendering [[Column]]
   elements. You can use [[ColumnGroup]] and column index properties to manage
   column natural order precisely.

   Clicking on table headers trigger re-ordering callback on the model with the
   expected column and direction, unless disabled _via_ the column x
   specification. However, actual sorting (and corresponding feedback on table
   headers) would only take place if the model supports re-ordering and
   eventually triggers a reload.

   Right-clicking the table headers displays a popup-menu with actions to reset
   natural ordering, reset column widths and select column visibility.

   Tables do not control item selection state. Instead, you shall supply the
   selection state and callback _via_ properties, like any other controlled
   React components.

   @template Key - unique identifiers of table entries.
   @template Row - data associated to each key in the table entries.
 */

export function Table<Key, Row>(props: TableProps<Key, Row>): JSX.Element {

  const state = React.useMemo(() => new TableState<Key, Row>(), []);
  const [age, setAge] = React.useState(0);
  React.useEffect(() => {
    state.signal = () => setAge(age + 1);
    state.importSettings(props.settings);
    state.setModel(props.model);
    state.setSorting(props.sorting);
    state.setRendering(props.rendering);
    state.onSelection = props.onSelection;
    state.onContextMenu = props.onContextMenu;
    return state.unwind;
  });
  Settings.useGlobalSettingsEvent(state.importSettings);
  const columns = props.children ?? [];
  return (
    <div className="dome-xTable">
      <React.Fragment key="columns">
        {spawnIndex(state, [], columns)}
      </React.Fragment>
      <AutoSizer key="table">
        {(size: Size) => makeTable(props, state, size)}
      </AutoSizer>
    </div>
  );
}

// --------------------------------------------------------------------------
