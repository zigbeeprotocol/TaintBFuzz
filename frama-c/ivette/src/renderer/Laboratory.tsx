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

// --------------------------------------------------------------------------
// ---  Lab View Component
// --------------------------------------------------------------------------

import _ from 'lodash';
import React from 'react';
import * as Dome from 'dome';
import * as Json from 'dome/data/json';
import * as Settings from 'dome/data/settings';
import { Catch } from 'dome/errors';
import { DnD, DragSource } from 'dome/dnd';
import { SideBar, Section, Item } from 'dome/frame/sidebars';
import { RSplit } from 'dome/layout/splitters';
import * as Grids from 'dome/layout/grids';
import { Hbox, Hfill, Vfill } from 'dome/layout/boxes';
import { IconButton, Field } from 'dome/controls/buttons';
import { Label } from 'dome/controls/labels';
import { Icon } from 'dome/controls/icons';
import { RenderElement } from 'dome/layout/dispatch';

import './style.css';


const Debug = new Dome.Debug('labviews');

// --------------------------------------------------------------------------
// --- Types
// --------------------------------------------------------------------------

interface Item {
  /** Identifier. */
  id: string;
  /** Displayed name. */
  label: string;
  /** Tooltip description. */
  title?: string;
  /** Ordering index. */
  rank?: number;
}
interface View extends Item {
  origin?: string;
  order?: number[];
  builtin?: boolean;
  defaultView?: boolean;
}

type Group = Item

interface Component extends Item {
  group?: string;
  layout?: layout;
}

type layout = 'PLAIN' | 'HPANE' | 'VPANE'


// --------------------------------------------------------------------------
// --- Library Class
// --------------------------------------------------------------------------

let RANK = 0;
const UPDATE = new Dome.Event('labview.library');

class Library {
  modified: boolean;
  virtual: { [id: string]: (Item & { order?: number }) };
  collection: { [id: string]: (Item & { order?: number }) };
  items: Item[];

  constructor() {
    this.modified = false;
    this.virtual = {};
    this.collection = {};
    this.items = [];
  }

  commit(): void {
    if (!_.isEqual(this.collection, this.virtual)) {
      this.collection = { ...this.virtual };
      this.items = _.sortBy(this.collection, ['order', 'id']);
      this.modified = false;
      UPDATE.emit();
    }
  }

  addItem(props: Item): void {
    if (!this.modified) {
      this.modified = true;
      setImmediate(() => this.commit());
    }
    const order = props.rank ?? ++RANK;
    const collection = this.virtual;
    collection[props.id] = { ...props, order };
  }

}

const LIBRARY = new Library();

// --------------------------------------------------------------------------
// --- Library Components
// --------------------------------------------------------------------------

const isItemId = (fd: string, id: string): boolean =>
  id.startsWith(fd) && id[fd.length] === '.';
const getItemId = (fd: string, id: string): string | undefined =>
  isItemId(fd, id) ? id.substring(fd.length + 1) : undefined;
const getItems = (items: Item[], fd: string): Item[] =>
  items.filter((item) => isItemId(fd, item.id));

export function addLibraryItem<A extends Item>(
  fd: string,
  { id, ...props }: A
): void {
  const itemId = `${fd}.${id}`;
  LIBRARY.addItem({ ...props, id: itemId });
}

// --------------------------------------------------------------------------
// --- Grid Item
// --------------------------------------------------------------------------

interface TitleContext {
  id?: string;
  label?: string;
  title?: string;
}

interface GridItemProps extends Item {
  layout?: 'PLAIN' | 'HPANE' | 'VPANE';
  children?: React.ReactNode;
}

const TITLE = React.createContext<TitleContext>({});

export function useTitleContext(): TitleContext {
  return React.useContext(TITLE);
}

const GRIDITEM = {
  className: 'dome-container dome-xBoxes-vbox dome-xBoxes-box',
  handle: '.labview-handle',
  resize: 'both',
  fill: 'none',
  shrink: 'none',
  minWidth: 40,
  minHeight: 40,
  width: 120,
  height: 120,
};

const GRIDITEM_PLAIN = { fill: 'both' };
const GRIDITEM_HPANE = { fill: 'horizontal' };
const GRIDITEM_VPANE = { fill: 'vertical' };

const makeGridItem = (customize: unknown, onClose: (id: string) => void) =>
  function GridItem<A extends GridItemProps>(comp: A): JSX.Element {
    const { id: libId, label, title, layout = 'PLAIN', children } = comp;
    const id = getItemId('components', libId);
    let properties: { [key: string]: unknown } = { ...GRIDITEM };
    switch (layout) {
      case 'PLAIN':
        properties = { ...properties, ...GRIDITEM_PLAIN };
        break;
      case 'HPANE':
        properties = { ...properties, ...GRIDITEM_HPANE };
        break;
      case 'VPANE':
        properties = { ...properties, ...GRIDITEM_VPANE };
        break;
      case undefined:
        break;
      default:
        Debug.warn(`unexpected layout for ${id} component`, layout);
        break;
    }
    Object.keys(properties).forEach((key) => {
      const prop = (comp as A & { [key: string]: unknown })[key];
      if (prop) properties[key] = prop;
    });
    let CLOSING;
    if (customize) {
      CLOSING = (
        <IconButton
          className="labview-close"
          offset={-1}
          icon="CROSS"
          onClick={() => onClose(id as string)} // id may actually be undefined
        />
      );
    }
    return (
      <Grids.GridItem
        id={id}
        className={properties.className}
        handle={properties.handle}
        resize={properties.resize}
        fill={properties.fill}
        shrink={properties.shrink}
        minWidth={properties.minWidth}
        minHeight={properties.minHeight}
        width={properties.width}
        height={properties.height}
      >
        <Vfill className="labview-content">
          <Hbox className="labview-titlebar">
            <Hfill>
              <Catch label={id}>
                <RenderElement id={`labview.title.${id}`}>
                  <Label
                    className="labview-handle"
                    label={label}
                    title={title} />
                </RenderElement>
              </Catch>
            </Hfill>
            {CLOSING}
          </Hbox>
          <TITLE.Provider value={{ id, label, title }}>
            <Catch label={id}>{children}</Catch>
          </TITLE.Provider>
        </Vfill>
      </Grids.GridItem>
    );
  };

// --------------------------------------------------------------------------
// --- Customization Views
// --------------------------------------------------------------------------

type Shape = Json.json // Until Grids has a type Shape, use this one instead

interface CustomViewsProps {
  settings?: string,
  shape: Shape,
  setShape: (shape: Shape) => void,
  views: React.PropsWithChildren<View>[]
}

interface CustomViewsSettings {
  current?: string;
  shapes?: { [k: string]: Shape };
}

function CustomViews(props: CustomViewsProps): JSX.Element {
  const { settings, shape, setShape, views: libViews } = props;
  const [local, setLocal] = Settings.useWindowSettings<CustomViewsSettings>(
    settings,
    Json.identity as Json.Loose<CustomViewsSettings & Json.json>, // Clearly abusive conversion, a real decoder is needed
    {},
  );
  const [customs, setCustoms] =
    Settings.useLocalStorage<{ [id: string]: View }>(
      'frama-c.labview',
      Json.identity as Json.Loose<{ [id: string]: View } & Json.json>, // Clearly abusive conversion, a real decoder is needed
      {},
    );
  const [edited, setEdited] = React.useState<string>();
  const triggerDefault = React.useRef<View>();
  const { current, shapes = {} } = local;
  const theViews: { [id: string]: View } = {};

  _.forEach(libViews, (view) => {
    const {
      id: origin,
      order,
      label = '(Stock View)',
      title, defaultView,
    } = view;
    const id = `builtin.${origin}`;

    theViews[id] =
      { id, order, label, title, builtin: true, defaultView, origin };
  });

  _.forEach(customs, (view) => {
    const { id, order, label = '(Custom View)', title, origin } = view;
    if (id && !theViews[id]) {
      theViews[id] = { id, order, label, title, builtin: false, origin };
    }
  });

  const getStock =
    (origin: string | undefined): React.PropsWithChildren<View> => (
      (origin && _.find(libViews, (v) => v.id === origin)) ||
      _.find(libViews, (v) => !!v.defaultView) ||
      libViews[0]
    );

  const getDefaultShape = (view: View): Shape => {
    const stock = getStock(view && view.origin);
    return stock && Grids.makeChildrenShape(stock.children);
  };

  const SELECT = (id: string): void => {
    if (id && current !== id) {
      if (current) shapes[current] = shape;
      setLocal({ current: id, shapes });
      setShape(shapes[id] || getDefaultShape(theViews[id]));
    }
  };

  const POPUP = (id: string): void => {
    const view = theViews[id];
    if (!view) return;
    const isCurrent = current === id;
    const isCustom = !view.builtin;

    const DEFAULT = (): void => {
      shapes[id] = undefined;
      setLocal({ current: id, shapes });
      setShape(getDefaultShape(view));
    };

    const RENAME = () => void setEdited(id);

    const DUPLICATE = (): void => {
      const base = `custom.${view.origin}`;
      const stock = getStock(view.origin);
      let k = 1;
      let newId = base;
      while (theViews[newId]) {
        k += 1;
        newId = `${base}~${k}`;
      }
      let newOrder = view.order;
      if (newOrder && newOrder.concat) newOrder = newOrder.concat([k]);
      let newLabel = `Custom ${stock.label}`;
      if (k > 1) newLabel += `~${k}`;
      customs[newId] = {
        id: newId,
        label: newLabel,
        order: newOrder,
        title: `Derived from ${stock.label}`,
        origin: view.origin,
        builtin: false,
      };
      setCustoms(customs);
      if (current) shapes[current] = shape;
      setLocal({ current: newId, shapes });
      setEdited(newId);
    };

    const REMOVE = (): void => {
      delete customs[id];
      delete shapes[id];
      setCustoms(customs);
      const newCurrent = current === id ? undefined : current;
      setLocal({ current: newCurrent, shapes });
    };

    Dome.popupMenu([
      { label: 'Rename View', display: (!edited && isCustom), onClick: RENAME },
      { label: 'Restore Default', display: isCurrent, onClick: DEFAULT },
      { label: 'Duplicate View', onClick: DUPLICATE },
      'separator',
      { label: 'Remove View', display: isCustom, onClick: REMOVE },
    ]);
  };

  const makeViewItem = ({ id, label, title, builtin }: View): JSX.Element => {
    if (edited === id) {
      const RENAMED = (newLabel: string): void => {
        if (newLabel) {
          const custom = Json.jObj(customs[id] as Json.json) || {};
          if (custom) custom.label = newLabel;
          setCustoms(customs);
        }
        setEdited(undefined);
      };
      const FIELD = (
        <Field
          className="labview-field"
          placeholder="View Name"
          autoFocus
          value={label}
          title={title}
          onChange={RENAMED}
        />
      );
      return (
        <Item key={id} icon="DISPLAY">
          {FIELD}
        </Item>
      );
    }
    const FLAGS = [];
    if (builtin) FLAGS.push('LOCK');
    return (
      <Item
        key={id}
        icon="DISPLAY"
        label={label}
        title={title}
        selected={!!id && current === id}
        onSelection={() => SELECT(id)}
        onContextMenu={() => POPUP(id)}
      >
        {FLAGS.map((icn) => (
          <Icon
            key={icn}
            className="labview-icon"
            size={9}
            offset={1}
            id={icn}
          />
        ))}
      </Item>
    );
  };

  if (!current && !triggerDefault.current) {
    const theDefault = _.find(theViews, (item) => !!item.defaultView);
    triggerDefault.current = theDefault;
    if (theDefault) setTimeout(() => { SELECT(theDefault.id); });
  }

  return (
    <Section label="Views" defaultUnfold>
      {_.sortBy(theViews, ['order', 'id']).map(makeViewItem)}
    </Section>
  );
}

// --------------------------------------------------------------------------
// --- Customization Components
// --------------------------------------------------------------------------

const DRAGOVERLAY = { className: 'labview-stock' };

export interface CustomGroupProps {
  settings?: string;
  dnd?: DnD;
  shape?: Shape;
  setDragging: (id?: string) => void;
  id?: string;
  title?: string;
  label: string;
  components: Component[];
}

function CustomGroup({
  settings,
  dnd, shape, setDragging,
  id: sectionId,
  title: sectionTitle,
  label: sectionLabel,
  components,
}: CustomGroupProps): JSX.Element {
  const makeComponent = ({ id, label, title }: Component): JSX.Element => {
    const itemId = getItemId('components', id);
    const disabled = Grids.getShapeItem(shape, itemId) !== undefined;
    return (
      <DragSource
        key={id}
        dnd={dnd}
        disabled={disabled}
        overlay={disabled ? undefined : DRAGOVERLAY}
        onStart={() => setDragging(itemId)}
      >
        <Item
          icon="COMPONENT"
          disabled={disabled}
          label={label}
          title={title}
        />
      </DragSource>
    );
  };
  return (
    <Section
      key={sectionId}
      settings={settings && `${settings}.${sectionId}`}
      label={sectionLabel}
      title={sectionTitle}
      defaultUnfold={sectionId === 'groups.frama-c'}
    >
      {components.map(makeComponent)}
    </Section>
  );
}

// --------------------------------------------------------------------------
// --- Customization Panel
// --------------------------------------------------------------------------

interface CustomPanelProps {
  dnd?: DnD;
  settings?: string;
  shape?: Shape;
  setShape: (shape: Shape) => void;
  setDragging: (id?: string) => void;
}

function CustomizePanel(
  { dnd, settings, shape, setShape, setDragging }: CustomPanelProps,
): JSX.Element {
  Dome.useUpdate(UPDATE);
  const { items } = LIBRARY;
  const views = getItems(items, 'views') as View[];
  const groups = getItems(items, 'groups') as Group[];
  const components = getItems(items, 'components') as Component[];
  const settingFolds = settings && `${settings}.folds`;
  const settingViews = settings && `${settings}.views`;
  const contents: { [id: string]: Component[] } = {};

  groups.unshift({ id: 'nogroup', label: 'Components' });
  groups.forEach((g) => (contents[g.id] = []));

  components.forEach((c) => {
    const gid = c.group ? `groups.${c.group}` : 'nogroup';
    let content = contents[gid];
    if (content === undefined) content = contents.nogroup;
    content.push(c);
  });

  return (
    <SideBar>
      <CustomViews
        key="views"
        settings={settingViews}
        shape={shape}
        setShape={setShape}
        views={views}
      />
      {groups.map((g) => (
        <CustomGroup
          settings={settingFolds}
          key={g.id}
          id={g.id}
          label={g.label}
          title={g.title}
          dnd={dnd}
          setDragging={setDragging}
          shape={shape}
          components={contents[g.id]}
        />
      ))}
    </SideBar>
  );
}

// --------------------------------------------------------------------------
// --- LabView Container
// --------------------------------------------------------------------------

export interface LabViewProps {
  /** Show component panels. */
  customize?: boolean;
  /** Base settings identifier. */
  settings?: string;
}

/**
   Reconfigurable Component Display.
 */
export function LabView(props: LabViewProps): JSX.Element {
  // Parameters
  const { settings, customize = false } = props;
  const settingSplit = settings && `${settings}.split`;
  const settingShape = settings && `${settings}.shape`;
  const settingPanel = settings && `${settings}.panel`;
  // Hooks & State
  Dome.useUpdate(
    UPDATE,
    Dome.windowSettings,
    Dome.globalSettings,
  );
  const dnd = React.useMemo(() => new DnD(), []);
  const [shape, setShape] =
    Settings.useWindowSettings(settingShape, Json.jAny, undefined);
  const [dragging, setDragging] = React.useState<string | undefined>();
  // Preparation
  const onClose =
    (id: string): void => setShape(Grids.removeShapeItem(shape, id));
  const components: Component[] =
    _.filter(
      LIBRARY.collection,
      (item: Item) => isItemId('components', item.id),
    );
  const gridItems =
    components.map(makeGridItem(customize, onClose));
  const holding =
    dragging ? gridItems.find((elt) => elt.props.id === dragging) : undefined;
  // Make view
  return (
    <RSplit margin={120} settings={settingSplit} unfold={customize}>
      <Grids.GridLayout
        dnd={dnd}
        padding={2}
        className="labview-container"
        items={gridItems}
        shape={shape}
        onReshape={setShape}
        holding={holding}
      />
      <CustomizePanel
        dnd={dnd}
        settings={settingPanel}
        shape={shape}
        setShape={setShape}
        setDragging={setDragging}
      />
    </RSplit>
  );
}

// --------------------------------------------------------------------------
