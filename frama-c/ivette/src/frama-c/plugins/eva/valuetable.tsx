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

import React from 'react';
import _ from 'lodash';
import * as Ivette from 'ivette';
import * as Dome from 'dome/dome';
import * as System from 'dome/system';
import * as States from 'frama-c/states';
import * as Server from 'frama-c/server';
import * as Ast from 'frama-c/kernel/api/ast';
import * as Eva from 'frama-c/plugins/eva/api/general';
import * as Values from 'frama-c/plugins/eva/api/values';
import { GlobalState, useGlobalState } from 'dome/data/states';

import { classes } from 'dome/misc/utils';
import { Icon } from 'dome/controls/icons';
import { Inset } from 'dome/frame/toolbars';
import * as Toolbars from 'dome/frame/toolbars';
import { Cell, Code } from 'dome/controls/labels';
import { IconButton } from 'dome/controls/buttons';
import { Filler, Hpack, Hfill, Vpack, Vfill } from 'dome/layout/boxes';
import { ipcRenderer } from 'electron';



/* -------------------------------------------------------------------------- */
/* --- Miscellaneous definitions                                          --- */
/* -------------------------------------------------------------------------- */

type Request<A, B> = (a: A) => Promise<B>;

type Alarm = [ 'True' | 'False' | 'Unknown', string ]
function getAlarmStatus(alarms: Alarm[] | undefined): string {
  if (!alarms) return 'none';
  if (alarms.length === 0) return 'none';
  if (alarms.find(([st, _]) => st === 'False')) return 'False';
  else return 'Unknown';
}

type MarkerTracked = [ 'Tracked', boolean ]
type MarkerPinned  = [ 'Pinned' , boolean ]
type MarkerStatus  = MarkerTracked | MarkerPinned | 'JustFocused'

function MarkerStatusClass(status: MarkerStatus): string {
  if (status === 'JustFocused') return 'eva-header-just-focused';
  const [ kind, focused ] = status;
  return 'eva-header-' + kind.toLowerCase() + (focused ? '-focused' : '');
}

function isPinnedMarker(status: MarkerStatus): boolean {
  if (status === 'JustFocused') return false;
  const [ kind ] = status;
  return kind === 'Pinned';
}

interface TableCellProps {
  children?: JSX.Element | JSX.Element[];
  right?: JSX.Element;
  align?: 'left' | 'center';
}

function TableCell(props: TableCellProps): JSX.Element {
  const { children, right, align = 'center' } = props;
  const leftVisible = align === 'center' ? 'block' : 'none';
  return (
    <div className='eva-cell-container'>
      <div className='eva-cell-left' style={{ display: leftVisible }}/>
      <div className='eva-cell-content'>
        {children}
      </div>
      <div className='eva-cell-right'>
        {right}
      </div>
    </div>
  );
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Callstack related definitions                                      --- */
/* -------------------------------------------------------------------------- */

/* Callstacks are declared by the server. We add the `Summary` construction to
 * cleanly represent the summary of all the callstacks. */
type callstack = 'Summary' | Values.callstack

/* Builds a cached version of the `getCallstacks` request */
function useCallstacksCache(): Request<Ast.marker[], callstack[]> {
  const g = React.useCallback((m) => Server.send(Values.getCallstacks, m), []);
  const toString = React.useCallback((ms) => ms.join('|'), []);
  return Dome.useCache(g, toString);
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Callsite related definitions                                       --- */
/* -------------------------------------------------------------------------- */

/* Representation of a callsite as described in the server */
interface Callsite {
  callee: string;
  caller?: string;
  stmt?: Ast.marker;
}

/* Builds a cached version of the `getCallstackInfo` request */
function useCallsitesCache(): Request<callstack, Callsite[]> {
  const get = React.useCallback((c) => {
    if (c !== 'Summary') return Server.send(Values.getCallstackInfo, c);
    else return Promise.resolve([]);
  }, []);
  return Dome.useCache(get);
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Probe related definitions                                          --- */
/* -------------------------------------------------------------------------- */

/* A Location is a marker in a function */
interface Location {
  target: Ast.marker;
  fct: string;
}

/* An Evaluation keeps track of the values at relevant control point around a
 * statement, along with the potential errors */
interface Evaluation {
  errors?: string;
  vBefore?: Values.evaluation;
  vAfter?: Values.evaluation;
  vThen?: Values.evaluation;
  vElse?: Values.evaluation;
}

/* A Probe is a location along with data representing textually what it is, the
 * considered statement, if it is an effectfull one or one with conditions.
 * Moreover, it gives a function that computes an Evaluation for a given
 * callstack. This computation is asynchronous. */
interface Probe extends Location {
  code?: string;
  stmt?: Ast.marker;
  rank?: number;
  evaluable: boolean;
  effects?: boolean;
  condition?: boolean;
  evaluate: Request<callstack, Evaluation>
}

/* Builds a cached version of the `getValues` request */
function useEvaluationCache(): Request<[ Location, callstack ], Evaluation> {
  type LocStack = [ Location, callstack ];
  const toString = React.useCallback(([ l, c ] : LocStack): string => {
    return `${l.fct}:${l.target}:${c}`;
  }, []);
  const get: Request<LocStack, Evaluation> = React.useCallback(([ l, c ]) => {
    const callstack = c === 'Summary' ? undefined : c;
    return Server.send(Values.getValues, { ...l, callstack });
  }, []);
  return Dome.useCache(get, toString);
}

/* Builds a cached function that builds a Probe given a Location */
function useProbeCache(): Request<Location, Probe> {
  const toString = React.useCallback((l) => `${l.fct}:${l.target}`, []);
  const cache = useEvaluationCache();
  const get = React.useCallback(async (loc: Location): Promise<Probe> => {
    const infos = await Server.send(Values.getProbeInfo, loc.target);
    const evaluate: Request<callstack, Evaluation> = (c) => cache([ loc, c ]);
    return { ...loc, ...infos, evaluate };
  }, [ cache ]);
  return Dome.useCache(get, toString);
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Statement Component                                                --- */
/* -------------------------------------------------------------------------- */

interface StmtProps {
  stmt?: Ast.marker;
  marker?: Ast.marker;
  short?: boolean;
}

function Stmt(props: StmtProps): JSX.Element {
  const markersInfo = States.useSyncArray(Ast.markerInfo);
  const { stmt, marker, short } = props;
  if (!stmt || !marker) return <></>;
  const line = markersInfo.getData(marker)?.sloc?.line;
  const filename = markersInfo.getData(marker)?.sloc?.base;
  const title = markersInfo.getData(stmt)?.descr;
  const text = short ? `@L${line}` : `@${filename}:${line}`;
  const className = 'dome-text-cell eva-stmt';
  return <span className={className} title={title}>{text}</span>;
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Informations on the alarms in a given callstack                    --- */
/* -------------------------------------------------------------------------- */

function AlarmsInfos(probe?: Probe): Request<callstack, JSX.Element> {
  return async (c: callstack): Promise<JSX.Element> => {
    const evaluation = await probe?.evaluate(c);
    const alarms = evaluation?.vBefore?.alarms ?? [];
    if (alarms.length <= 0) return <></>;
    const renderAlarm = ([status, alarm]: Alarm): JSX.Element => {
      const className = classes('eva-alarm-info', `eva-alarm-${status}`);
      return <Code className={className} icon="WARNING">{alarm}</Code>;
    };
    const children = React.Children.toArray(alarms.map(renderAlarm));
    return <Vpack className="eva-info">{children}</Vpack>;
  };
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Informations on the selected callstack                             --- */
/* -------------------------------------------------------------------------- */

interface StackInfosProps {
  callsites: Callsite[];
  isSelected: boolean;
  setSelection: (a: States.SelectionActions) => void;
  close: () => void;
}

async function StackInfos(props: StackInfosProps): Promise<JSX.Element> {
  const { callsites, setSelection, isSelected, close } = props;
  const selectedClass = isSelected ? 'eva-focused' : '';
  const className = classes('eva-callsite', selectedClass);
  if (callsites.length <= 1) return <></>;
  const makeCallsite = ({ caller, stmt }: Callsite): JSX.Element => {
    if (!caller || !stmt) return <></>;
    const key = `${caller}@${stmt}`;
    const location = { fct: caller, marker: stmt };
    const select = (meta: boolean): void => {
      setSelection({ location });
      if (meta) States.MetaSelection.emit(location);
    };
    const onClick = (evt: React.MouseEvent): void => { select(evt.altKey); };
    const onDoubleClick = (evt: React.MouseEvent): void => {
      evt.preventDefault();
      select(true);
    };
    return (
      <Cell
        key={key}
        icon='TRIANGLE.LEFT'
        className={className}
        onClick={onClick}
        onDoubleClick={onDoubleClick}
      >
        {caller}
        <Stmt stmt={stmt} marker={stmt} />
      </Cell>
    );
  };
  const children = React.Children.toArray(callsites.map(makeCallsite));
  return (
    <div className='eva-info'>
      <Hpack className='eva-info-wrap'>{children}</Hpack>
      <Hfill />
      <IconButton
        icon='CROSS'
        className='eva-button'
        onClick={close}
      />
    </div>
  );
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Probe Header Component                                             --- */
/* -------------------------------------------------------------------------- */
/* --- Header of a column, describing the evaluated expression and its    --- */
/* --- status inside the component (pinned, tracked, etc).                --- */
/* -------------------------------------------------------------------------- */

interface ProbeHeaderProps {
  probe: Probe;
  status: MarkerStatus;
  pinProbe: (pin: boolean) => void;
  selectProbe: () => void;
  removeProbe: () => void;
  setSelection: (a: States.SelectionActions) => void;
  locEvt: Dome.Event<Location>;
}

function ProbeHeader(props: ProbeHeaderProps): JSX.Element {
  const { probe, status, setSelection, locEvt } = props;
  const { code = '(error)', stmt, target, fct } = probe;
  const color = classes(MarkerStatusClass(status), 'eva-table-header-sticky');
  const { selectProbe, removeProbe, pinProbe } = props;
  const span = 1 + (probe.effects ? 1 : 0) + (probe.condition ? 2 : 0);
  const buttonClass = classes('eva-button', 'eva-header-button');

  // When the location is selected, we scroll the header into view, making it
  // appears wherever it was.
  const ref = React.createRef<HTMLTableCellElement>();
  locEvt.on((l) => { if (l === probe) ref.current?.scrollIntoView(); });

  const isPinned = isPinnedMarker(status);
  const pinText = isPinned ? 'Unpin' : 'Pin';
  const loc: States.SelectionActions = { location: { fct, marker: target} };
  const onClick = (): void => { setSelection(loc); selectProbe(); };
  const onDoubleClick = (): void => pinProbe(!isPinned);
  const onContextMenu = (): void => {
    const items: Dome.PopupMenuItem[] = [];
    const pinLabel = `${pinText} column for ${code}`;
    items.push({ label: pinLabel, onClick: onDoubleClick });
    const removeLabel = `Remove column for ${code}`;
    items.push({ label: removeLabel, onClick: removeProbe });
    Dome.popupMenu(items);
  };

  const buttons =
    <div>
      <IconButton
        icon='PIN'
        className={buttonClass}
        title={`${pinText} the column`}
        selected={isPinned}
        onClick={onDoubleClick}
      />
      <IconButton
        icon="CIRC.CLOSE"
        className={buttonClass}
        title="Remove the column"
        onClick={() => removeProbe()}
      />
    </div>;
  
  return (
    <th
      ref={ref}
      className={color}
      colSpan={span}
      onClick={onClick}
      onDoubleClick={onDoubleClick}
      onContextMenu={onContextMenu}
    >
      <TableCell right={buttons}>
        <div className='eva-header-text-overflow'>
          <span className='dome-text-cell' title={code}>{code}</span>
        </div>
        <Stmt stmt={stmt} marker={target} short={true}/>
      </TableCell>
    </th>
  );
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Probe Description Component                                        --- */
/* -------------------------------------------------------------------------- */
/* --- Description of a table column, i.e. if it contains values          --- */
/* --- evaluated before or after the considered statement.                --- */
/* -------------------------------------------------------------------------- */

interface ProbeDescrProps {
  probe: Probe;
}

function ProbeDescr(props: ProbeDescrProps): JSX.Element[] {
  const { probe } = props;
  const valuesClass = classes('eva-table-values', 'eva-table-values-center');
  const tableClass = classes('eva-table-descrs', 'eva-table-descr-sticky');
  const cls = classes(valuesClass, tableClass);
  const title = (s: string): string => `Values ${s} the statement evaluation`;
  const elements: JSX.Element[] = [];
  function push(title: string, children: JSX.Element | string): void {
    elements.push(<td className={cls} title={title}>{children}</td>);
  }
  if (!probe.effects && !probe.condition)
    push('Values at the statement', '-');
  if (probe.effects || probe.condition)
    push(title('before'), 'Before');
  if (probe.effects)
    push(title('after'), 'After');
  if (probe.condition) {
    const pushCondition = (s: string): void => {
      const t = `Values after the condition, in the ${s.toLowerCase()} branch`;
      const child =
        <div className='eva-header-after-condition'>
          After
          <div className='eva-stmt'>{`(${s})`}</div>
        </div>;
      push(t, child);
    };
    pushCondition('Then');
    pushCondition('Else');
  }
  return elements;
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Probe Values Component                                             --- */
/* -------------------------------------------------------------------------- */
/* --- This component represents the contents of one of the table that    --- */
/* --- displays values information. As the content depends on the         --- */
/* --- considered callstack, we decided to return a function that build   --- */
/* --- the actual component when given a callstack. It avoids useless     --- */
/* --- computational boilerplate.                                         --- */
/* -------------------------------------------------------------------------- */

interface ProbeValuesProps {
  probe: Probe;
  addLoc: (loc: Location) => void;
  isSelectedCallstack: (c: callstack) => boolean;
}

function ProbeValues(props: ProbeValuesProps): Request<callstack, JSX.Element> {
  const { probe, addLoc, isSelectedCallstack } = props;

  // Building common parts
  const onContextMenu = (evaluation?: Values.evaluation) => (): void => {
    const { value = '', pointedVars = [] } = evaluation ?? {};
    const items: Dome.PopupMenuItem[] = [];
    const copy = (): void => { navigator.clipboard.writeText(value); };
    if (value !== '') items.push({ label: 'Copy to clipboard', onClick: copy });
    if (items.length > 0 && pointedVars.length > 0) items.push('separator');
    pointedVars.forEach((lval) => {
      const [text, lvalMarker] = lval;
      const label = `Display values for ${text}`;
      const location = { fct: probe.fct, target: lvalMarker };
      const onItemClick = (): void => addLoc(location);
      items.push({ label, onClick: onItemClick });
    });
    if (items.length > 0) Dome.popupMenu(items);
  };

  return async (callstack: callstack): Promise<JSX.Element> => {
    const evaluation = await probe.evaluate(callstack);
    const { vBefore, vAfter, vThen, vElse } = evaluation;
    const isSelected = isSelectedCallstack(callstack);
    const selected = isSelected && callstack !== 'Summary' ? 'eva-focused' : '';
    const font = callstack === 'Summary' ? 'eva-italic' : '';
    const c = classes('eva-table-values', selected, font);
    const kind = callstack === 'Summary' ? 'one' : 'this';
    const title = `At least one alarm is raised in ${kind} callstack`;
    function td(e?: Values.evaluation, colSpan = 1): JSX.Element {
      const { alarms, value = '-' } = e ?? {};
      const status = getAlarmStatus(alarms);
      const alarmClass = classes('eva-cell-alarms', `eva-alarm-${status}`);
      const align = value?.includes('\n') ? 'left' : 'center';
      const warning =
        <Icon className={alarmClass} size={10} title={title} id="WARNING" />;
      return (
        <td className={c} colSpan={colSpan} onContextMenu={onContextMenu(e)}>
          <TableCell right={warning} align={align}>
            <span className='eva-table-text'>{value}</span>
          </TableCell>
        </td>
      );
    }
    const elements: JSX.Element[] = [];
    if (probe.effects && _.isEqual(vBefore, vAfter))
      elements.push(td(vBefore, 2));
    else {
      if (!probe.effects && !probe.condition)
        elements.push(td(vBefore));
      if (probe.effects || probe.condition)
        elements.push(td(vBefore));
      if (probe.effects)
        elements.push(td(vAfter));
      if (probe.condition)
        elements.push(td(vThen), td(vElse));
    }
    return <>{React.Children.toArray(elements)}</>;
  };
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Row header describing the corresponding callstack                  --- */
/* -------------------------------------------------------------------------- */

interface CallsiteCellProps {
  callstack: callstack | 'Header';
  index?: number;
  getCallsites: Request<callstack, Callsite[]>;
  selectedClass?: string;
}

function makeStackTitle(calls: Callsite[]): string {
  const cs = calls.slice(1);
  if (cs.length > 0)
    return `Callstack: ${cs.map((c) => c.callee).join(' \u2190 ')}`;
  return 'Callstack Details';
}

async function CallsiteCell(props: CallsiteCellProps): Promise<JSX.Element> {
  const { callstack, index, getCallsites, selectedClass = '' } = props;
  const baseClasses = classes('eva-table-callsite-box', selectedClass);
  switch (callstack) {
    case 'Header': {
      const cls = classes(baseClasses, 'eva-table-header-sticky');
      const title = 'Callstack at which expressions are evaluated';
      return <td className={cls} rowSpan={2} title={title}>{'#'}</td>;
    }
    default: {
      const cls = classes(baseClasses, 'eva-table-value-sticky');
      const callsites = await getCallsites(callstack);
      const isSummary = callstack === 'Summary';
      const summary = 'Summary: value consolidated accross all callstacks';
      const infos = isSummary ? summary : makeStackTitle(callsites);
      const text = isSummary ? '∑' : (index ? index.toString() : '0');
      return <td className={cls} title={infos}>{text}</td>;
    }
  }
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Function Section Component                                         --- */
/* -------------------------------------------------------------------------- */

interface FunctionProps {
  fct: string;
  markers: Map<Ast.marker, MarkerStatus>;
  close: () => void;
  getProbe: Request<Location, Probe>;
  pinProbe: (probe: Probe, pin: boolean) => void;
  selectProbe: (probe: Probe) => void;
  removeProbe: (probe: Probe) => void;
  addLoc: (loc: Location) => void;
  folded: boolean;
  setFolded: (folded: boolean) => void;
  getCallsites: Request<callstack, Callsite[]>;
  byCallstacks: boolean;
  getCallstacks: Request<Ast.marker[], callstack[]>;
  setByCallstacks: (byCallstack: boolean) => void;
  selectCallstack: (callstack: callstack) => void;
  isSelectedCallstack: (c: callstack) => boolean;
  setSelection: (a: States.SelectionActions) => void;
  locEvt: Dome.Event<Location>;
  startingCallstack: number;
  changeStartingCallstack: (n: number) => void;
}

const PageSize = 99;

async function FunctionSection(props: FunctionProps): Promise<JSX.Element> {
  const { fct, folded, isSelectedCallstack, locEvt } = props;
  const { byCallstacks, setSelection, getCallsites } = props;
  const { addLoc, getCallstacks: getCS } = props;
  const { setFolded, setByCallstacks, close } = props;
  const { startingCallstack, changeStartingCallstack } = props;
  const displayTable = folded ? 'none' : 'block';
  type RowHandler = React.MouseEventHandler<HTMLTableRowElement>;
  const onClick: (c: callstack) => RowHandler = (c) => (event) => {
    const elt = document.elementFromPoint(event.clientX, event.clientY);
    if (elt?.localName !== 'span')
      props.selectCallstack(isSelectedCallstack(c) ? 'Summary' : c);
  };

  /* Computes the relevant callstacks */
  const markers = Array.from(props.markers.keys());
  const allCallstacks = await getCS(markers);
  const summaryOnly = allCallstacks.length === 1;
  const callstacks = byCallstacks || summaryOnly ? allCallstacks : [];
  const nbCS = allCallstacks.length;

  /* Computes the relevant data for each marker */
  interface Data { probe: Probe; summary: Evaluation; status: MarkerStatus }
  const entries = Array.from(props.markers.entries());
  const data = await Promise.all(entries.map(async ([ target, status ]) => {
    const probe = await props.getProbe({ target, fct });
    const summary = await probe.evaluate('Summary');
    return { probe, summary, status } as Data;
  }));
  const doCall = data.length > 0;

  /* Computes the headers for each marker */
  const headerCall = await CallsiteCell({ getCallsites, callstack: 'Header' });
  const headers = await Promise.all(data.map((d: Data) => {
    const pinProbe = (pin: boolean): void => props.pinProbe(d.probe, pin);
    const selectProbe = (): void => props.selectProbe(d.probe);
    const removeProbe = (): void => props.removeProbe(d.probe);
    const fcts = { selectProbe, pinProbe, removeProbe, setSelection };
    return ProbeHeader({ ...d, ...fcts, locEvt });
  }));

  /* Computes the columns descriptions */
  const descrs = data.map((d) => ProbeDescr(d)).flat();

  /* Computes the summary values */
  const miscs = { addLoc, isSelectedCallstack };
  const builders = data.map((d: Data) => ProbeValues({ ...d, ...miscs }));
  const summary = await Promise.all(builders.map((b) => b('Summary')));
  const summCall = await CallsiteCell({ callstack: 'Summary', getCallsites });
  let summaryRow = <></>;
  if (!summaryOnly) {
    summaryRow =
      <tr key={'Summary'} onClick={onClick('Summary')}>
        {doCall ? summCall : undefined}
        {React.Children.toArray(summary)}
      </tr>;
  }

  /* Computes the values for each callstack */
  const start = Math.max(1, startingCallstack);
  const stop = Math.min(start + PageSize, callstacks.length);
  const values = await Promise.all(callstacks.map(async (callstack, n) => {
    const index = n + 1;
    if (start > index || stop < index) return <></>;
    const selectedClass = isSelectedCallstack(callstack) ? 'eva-focused' : '';
    const callProps = { selectedClass, getCallsites };
    const call = await CallsiteCell({ index, callstack, ...callProps });
    const values = await Promise.all(builders.map((b) => b(callstack)));
    return (
      <tr key={callstack} onClick={onClick(callstack)}>
        {call}
        {React.Children.toArray(values)}
      </tr>
    );
  }));

  /* We change the starting callstack dynamically when we reach the ends of the
   * scroll to avoid to build the complete table */
  const onScroll: React.UIEventHandler<HTMLDivElement> = (event) => {
    const { scrollTop, scrollHeight, clientHeight } = event.currentTarget;
    if (scrollTop / (scrollHeight - clientHeight) <= 0.1)
      changeStartingCallstack(Math.max(startingCallstack - 10, 0));
    const botGap = (scrollHeight - scrollTop - clientHeight) / scrollHeight;
    const lastCallstack = startingCallstack + PageSize;
    if (botGap <= 0.1 && lastCallstack !== callstacks.length) {
      const maxStart = callstacks.length - PageSize;
      const start = Math.min(startingCallstack + 10, maxStart);
      changeStartingCallstack(start);
    }
  };

  /* Builds the component */
  return (
    <>
      <Hpack className="eva-function">
        <IconButton
          className="eva-fct-fold"
          icon={folded ? 'ANGLE.RIGHT' : 'ANGLE.DOWN'}
          onClick={() => setFolded(!folded)}
        />
        <Cell className="eva-fct-name">{fct}</Cell>
        <Filler />
        <div className='eva-nb-callstacks'>
          {`${nbCS} callstack${nbCS > 1 ? 's' : ''}`}
        </div>
        <IconButton
          icon="ITEMS.LIST"
          className="eva-button"
          selected={byCallstacks}
          disabled={summaryOnly}
          title="Show values by callstack"
          onClick={() => setByCallstacks(!byCallstacks)}
        />
        <Inset />
        <IconButton
          icon="CROSS"
          className="eva-button"
          title="Close"
          onClick={close}
        />
      </Hpack>
      <div
        onScroll={onScroll}
        className='eva-table-container'
        style={{ display: displayTable }}
      >
        <table className='eva-table'>
          <tbody>
            <tr>
              {doCall ? headerCall : undefined}
              {React.Children.toArray(headers)}
            </tr>
            <tr>
              {React.Children.toArray(descrs)}
            </tr>
            {summaryRow}
            {React.Children.toArray(values)}
          </tbody>
        </table>
      </div>
    </>
  );
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Function Manager                                                   --- */
/* -------------------------------------------------------------------------- */
/* --- The Function Manager is responsible of all the data related to     --- */
/* --- programs functions.                                                --- */
/* -------------------------------------------------------------------------- */

/* Informations on one function */
class FunctionInfos {

  readonly fct: string;                     // Function's name
  readonly pinned = new Set<Ast.marker>();  // Pinned markers
  readonly tracked = new Set<Ast.marker>(); // Tracked markers
  startingCallstack = 1;                    // First displayed callstack
  byCallstacks = false;                     // True if displayed by callstacks
  folded = false;                           // True if folded

  constructor(fct: string) {
    this.fct = fct;
  }

  has(marker: Ast.marker): boolean {
    const pinned = this.pinned.has(marker);
    const tracked = this.tracked.has(marker);
    return pinned || tracked;
  }

  pin(marker: Ast.marker): void {
    this.pinned.add(marker);
    this.tracked.delete(marker);
  }

  track(marker: Ast.marker): void {
    this.tracked.add(marker);
    this.pinned.delete(marker);
  }

  delete(marker: Ast.marker): void {
    this.pinned.delete(marker);
    this.tracked.delete(marker);
  }

  isEmpty(): boolean {
    return this.pinned.size === 0 && this.tracked.size === 0;
  }

  markers(focusedLoc?: Location): Map<Ast.marker, MarkerStatus> {
    const { target: tgt, fct } = focusedLoc ?? {};
    const inFct = fct !== undefined && fct === this.fct;
    const ms = new Map<Ast.marker, MarkerStatus>();
    this.pinned.forEach((p) => ms.set(p, [ 'Pinned', inFct && tgt === p ]));
    this.tracked.forEach((p) => ms.set(p, [ 'Tracked', inFct && tgt === p ]));
    if (inFct && tgt && !this.has(tgt)) ms.set(tgt, 'JustFocused');
    return new Map(Array.from(ms.entries()).reverse());
  }

}

/* State keeping tracks of informations for every relevant functions */
class FunctionsManager {

  private readonly cache = new Map<string, FunctionInfos>();

  constructor() {
    this.newFunction = this.newFunction.bind(this);
    this.getInfos = this.getInfos.bind(this);
    this.setByCallstacks = this.setByCallstacks.bind(this);
    this.setFolded = this.setFolded.bind(this);
    this.pin = this.pin.bind(this);
    this.track = this.track.bind(this);
    this.removeLocation = this.removeLocation.bind(this);
    this.delete = this.delete.bind(this);
    this.clear = this.clear.bind(this);
    this.map = this.map.bind(this);
  }

  newFunction(fct: string): void {
    if (!this.cache.has(fct)) this.cache.set(fct, new FunctionInfos(fct));
  }

  private getInfos(fct: string): FunctionInfos {
    const { cache } = this;
    if (cache.has(fct)) return cache.get(fct) as FunctionInfos;
    const infos = new FunctionInfos(fct);
    this.cache.set(fct, infos);
    return infos;
  }

  isEmpty(fct: string): boolean {
    const infos = this.cache.get(fct);
    return infos ? infos.isEmpty() : true;
  }

  setByCallstacks(fct: string, byCallstacks: boolean): void {
    const infos = this.cache.get(fct);
    if (infos) infos.byCallstacks = byCallstacks;
  }

  setFolded(fct: string, folded: boolean): void {
    const infos = this.cache.get(fct);
    if (infos) infos.folded = folded;
  }

  changeStartingCallstack(fct: string, n: number): void {
    const infos = this.cache.get(fct);
    if (infos) infos.startingCallstack = n;
  }

  pin(loc: Location): void {
    const { target, fct } = loc;
    this.getInfos(fct).pin(target);
  }

  unpin(loc: Location): void {
    const { target, fct } = loc;
    this.cache.get(fct)?.pinned.delete(target);
  }

  track(loc: Location): void {
    const { target, fct } = loc;
    this.getInfos(fct).track(target);
  }

  removeLocation(loc: Location): void {
    const { target, fct } = loc;
    const infos = this.cache.get(fct);
    if (infos) infos.delete(target);
  }

  delete(fct: string): void {
    this.cache.delete(fct);
  }

  clear(): void {
    this.cache.clear();
  }

  clean(focused?: Location): void {
    const focusedFct = focused?.fct;
    this.cache.forEach((infos) => {
      if (focusedFct !== infos.fct && infos.isEmpty())
        this.cache.delete(infos.fct);
    });
  }

  map<A>(func: (infos: FunctionInfos, fct: string) => A): A[] {
    const entries = Array.from(this.cache.entries());
    return entries.map(([ fct, infos ]) => func(infos, fct));
  }

}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Evaluation Mode Handling                                           --- */
/* -------------------------------------------------------------------------- */

export const evaluateEvent = new Dome.Event('dome.evaluate');
ipcRenderer.on('dome.ipc.evaluate', () => evaluateEvent.emit());

interface EvaluationModeProps {
  computationState : Eva.computationStateType | undefined;
  selection: States.Selection;
  setLocPin: (loc: Location, pin: boolean) => void;
}

Dome.addMenuItem({
  menu: 'Edit',
  id: 'EvaluateMenu',
  type: 'normal',
  label: 'Evaluate',
  key: 'Cmd+E',
  onClick: () => evaluateEvent.emit(),
});

function useEvaluationMode(props: EvaluationModeProps): void {
  const { computationState, selection, setLocPin } = props;
  const handleError = (): void => { return; };
  const addProbe = (target: Ast.marker | undefined): void => {
    const fct = selection?.current?.fct;
    if (fct && target) setLocPin({ fct, target }, true);
  };
  React.useEffect(() => {
    if (computationState !== 'computed') return () => { return; };
    const shortcut = System.platform === 'macos' ? 'Cmd+E' : 'Ctrl+E';
    const onEnter = (pattern: string): void => {
      const marker = selection?.current?.marker;
      const data = { atStmt: marker, term: pattern };
      Server.send(Ast.markerFromTerm, data).then(addProbe).catch(handleError);
    };
    const evalMode = {
      label: 'Evaluation',
      title: `Evaluate an ACSL expression (shortcut: ${shortcut})`,
      icon: 'TERMINAL',
      className: 'eva-evaluation-mode',
      hints: () => { return Promise.resolve([]); },
      onEnter,
      event: evaluateEvent,
    };
    Toolbars.RegisterMode.emit(evalMode);
    return () => Toolbars.UnregisterMode.emit(evalMode);
  });
  React.useEffect(() => {
    Dome.setMenuItem({ id: 'EvaluateMenu', enabled: true });
    return () => Dome.setMenuItem({ id: 'EvaluateMenu', enabled: false });
  });
}

/* -------------------------------------------------------------------------- */



/* -------------------------------------------------------------------------- */
/* --- Eva Table Complet Component                                        --- */
/* -------------------------------------------------------------------------- */

/* Table's state. It is global for when the user changes the view. */
const CallstackState = new GlobalState<callstack>('Summary');
const FunctionsManagerState = new GlobalState(new FunctionsManager());
const FocusState = new GlobalState<Probe | undefined>(undefined);

/* Component */
function EvaTable(): JSX.Element {

  /* Component state */
  const [ selection, select ] = States.useSelection();
  const [ cs, setCS ] = useGlobalState(CallstackState);
  const [ fcts ] = useGlobalState(FunctionsManagerState);
  const [ focus, setFocus ] = useGlobalState(FocusState);

  /* Used to force the component update. We cannot use the `forceUpdate` hook
   * proposed by Dome as we need to be able to add dependencies on a changing
   * value (here tac) explicitly. We need to force the update as modifications
   * of the Function Manager internal data does NOT trigger the component
   * update. */
  const [ tac, setTic ] = React.useState(0);

  /* Event use to communicate when a location is selected. Used to scroll
   * related column into view if needed */
  const [ locEvt ] = React.useState(new Dome.Event<Location>('eva-location'));

  /* Build cached version of needed server's requests */
  const getProbe = useProbeCache();
  const getCallsites = useCallsitesCache();
  const getCallstacks = useCallstacksCache();

  /* Computing the function corresponding to the selected callstack */
  const csFctPromise = React.useMemo(async () => {
    const selectedCSInfos = await getCallsites(cs);
    if (selectedCSInfos.length === 0) return undefined;
    else return selectedCSInfos[0].callee;
  }, [ cs, getCallsites ]);
  const { result: csFct } = Dome.usePromise(csFctPromise);

  /* Reset the selected callstack when the corresponding function is removed */
  React.useEffect(() => {
    if (csFct && fcts.isEmpty(csFct) && focus?.fct !== csFct)
      setCS('Summary');
  }, [ csFct, setCS, fcts, focus?.fct ] );

  /* Updated the focused Probe when the selection changes. Also emit on the
   * `locEvent` event. */
  React.useEffect(() => {
    const target = selection?.current?.marker;
    const fct = selection?.current?.fct;
    const loc = (target && fct) ? { target, fct } : undefined;
    fcts.clean(loc);
    const doUpdate = (p: Probe): void => {
      if (!p.evaluable) { setFocus(undefined); return; }
      if (fct && p.code) fcts.newFunction(fct);
      setFocus(p); locEvt.emit(p);
    };
    if (loc) getProbe(loc).then(doUpdate);
    else setFocus(undefined);
  }, [ fcts, selection, getProbe, setFocus, locEvt ]);

  /* Callback used to pin or unpin a location */
  const setLocPin = React.useCallback((loc: Location, pin: boolean): void => {
    if (pin) fcts.pin(loc);
    else fcts.unpin(loc);
    setTic(tac + 1);
  }, [fcts, setTic, tac]);

  /* On meta-selection, pin the selected location. */
  React.useEffect(() => {
    const pin = (loc: States.Location): void => {
      const {marker, fct} = loc;
      if (marker && fct) setLocPin({ target: marker, fct }, true);
    };
    States.MetaSelection.on(pin);
    return () => States.MetaSelection.off(pin);
  });

  /* Callback used to remove a probe */
  const remove = React.useCallback((probe: Probe): void => {
    fcts.removeLocation(probe);
    if (probe.target === focus?.target) {
      setFocus(undefined);
      fcts.clean(undefined);
    }
    else {
      fcts.clean(focus);
    }
    setTic(tac + 1);
  }, [ fcts, focus, setFocus, tac ]);

  /* Builds the sections for each function. As the component is built
   * asynchronously, we have to use the `usePromise` hook, which forces us to
   * memoize the promises building. */
  const functionsPromise = React.useMemo(() => {
    const ps = fcts.map((infos, fct) => {
      const { byCallstacks, folded } = infos;
      const isSelectedCallstack = (c: callstack): boolean => c === cs;
      const setFolded = (folded: boolean): void => {
        fcts.setFolded(fct, folded);
        setTic(tac + 1);
      };
      const setByCS = (byCS: boolean): void => {
        fcts.setByCallstacks(fct, byCS);
        setTic(tac + 1);
      };
      const changeStartingCallstack = (n: number): void => {
        fcts.changeStartingCallstack(fct, n);
        setTic(tac + 1);
      };
      const close = (): void => {
        fcts.delete(fct);
        if (csFct === fct) setCS('Summary');
        setTic(tac + 1);
      };
      return {
        fct,
        markers: infos.markers(focus),
        close,
        pinProbe: setLocPin,
        getProbe,
        selectProbe: setFocus,
        removeProbe: remove,
        addLoc: (loc: Location) => { fcts.pin(loc); setTic(tac + 1); },
        folded,
        setFolded,
        getCallsites,
        byCallstacks,
        getCallstacks,
        setByCallstacks: setByCS,
        selectCallstack: (c: callstack) => { setCS(c); setTic(tac + 1); },
        isSelectedCallstack,
        setSelection: select,
        locEvt,
        startingCallstack: infos.startingCallstack,
        changeStartingCallstack,
      };
    });
    return Promise.all(ps.map(FunctionSection));
  },
  [ cs, setCS, fcts, focus, setFocus, tac, getCallsites, setLocPin, csFct,
    getCallstacks, getProbe, remove, select, locEvt ]);
  const { result: functions } = Dome.usePromise(functionsPromise);

  /* Builds the alarms component. As for the function sections, it is an
   * asynchronous process. */
  const alarmsProm = React.useMemo(() => AlarmsInfos(focus)(cs), [ focus, cs ]);
  const { result: alarmsInfos } = Dome.usePromise(alarmsProm);

  /* Builds the stacks component. As for the function sections, it is an
   * asynchronous process. */
  const stackInfosPromise = React.useMemo(async () => {
    const callsites = await getCallsites(cs);
    const tgt = selection.current?.marker;
    const p = (c: Callsite): boolean => c.stmt !== undefined && c.stmt === tgt;
    const isSelected = callsites.find(p) !== undefined;
    const close = (): void => setCS('Summary');
    return StackInfos({ callsites, isSelected, setSelection: select, close });
  }, [ cs, setCS, select, getCallsites, selection ]);
  const { result: stackInfos } = Dome.usePromise(stackInfosPromise);

  /* Handle Evaluation mode */
  const computationState = States.useSyncValue(Eva.computationState);
  useEvaluationMode({ computationState, selection, setLocPin });

  /* Builds the component */
  return (
    <>
      <Ivette.TitleBar />
      <div className='eva-functions-section'>
        {React.Children.toArray(functions)}
      </div>
      <Vfill/>
      {alarmsInfos}
      {stackInfos}
    </>
  );

}

/* Registers the component in Ivette */
Ivette.registerComponent({
  id: 'frama-c.plugins.values',
  group: 'frama-c.plugins',
  rank: 1,
  label: 'Eva Values',
  title: 'Values inferred by the Eva analysis',
  children: <EvaTable />,
});

/* -------------------------------------------------------------------------- */
