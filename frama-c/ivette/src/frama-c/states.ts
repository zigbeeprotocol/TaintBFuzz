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
// --- Frama-C States
// --------------------------------------------------------------------------

/**
 * Manage the current Frama-C project and projectified state values.
 * @packageDocumentation
 * @module frama-c/states
*/

import React from 'react';
import * as Dome from 'dome';
import * as Json from 'dome/data/json';
import { Order } from 'dome/data/compare';
import { GlobalState, useGlobalState } from 'dome/data/states';
import { Client, useModel } from 'dome/table/models';
import { CompactModel } from 'dome/table/arrays';
import * as Ast from 'frama-c/kernel/api/ast';
import * as Server from './server';

const PROJECT = new Dome.Event('frama-c.project');
class STATE extends Dome.Event {
  constructor(id: string) {
    super(`frama-c.state.${id}`);
  }
}

// --------------------------------------------------------------------------
// --- Pretty Printing (Browser Console)
// --------------------------------------------------------------------------

const D = new Dome.Debug('States');

// --------------------------------------------------------------------------
// --- Synchronized Current Project
// --------------------------------------------------------------------------

let currentProject: string | undefined;

Server.onReady(async () => {
  try {
    const sr: Server.GetRequest<null, { id?: string }> = {
      kind: Server.RqKind.GET,
      name: 'kernel.project.getCurrent',
      input: Json.jNull,
      output: Json.jObject({ id: Json.jString }),
      signals: [],
    };
    const current: { id?: string } = await Server.send(sr, null);
    currentProject = current.id;
    PROJECT.emit();
  } catch (error) {
    D.error(`Fail to retrieve the current project. ${error}`);
  }
});

Server.onShutdown(() => {
  currentProject = '';
  PROJECT.emit();
});

// --------------------------------------------------------------------------
// --- Project API
// --------------------------------------------------------------------------

/**
 * Current Project (Custom React Hook).
 * @return The current project.
 */
export function useProject(): string | undefined {
  Dome.useUpdate(PROJECT);
  return currentProject;
}

/**
 * Update Current Project.
 *
 * Make all states switching to their projectified value.
 *
 * Emits `PROJECT`.
 * @param project The project identifier.
 */
export async function setProject(project: string): Promise<void> {
  if (Server.isRunning()) {
    try {
      const sr: Server.SetRequest<string, null> = {
        kind: Server.RqKind.SET,
        name: 'kernel.project.setCurrent',
        input: Json.jString,
        output: Json.jNull,
        signals: [],
      };
      await Server.send(sr, project);
      currentProject = project;
      PROJECT.emit();
    } catch (error) {
      D.error(`Fail to set the current project. ${error}`);
    }
  }
}

// --------------------------------------------------------------------------
// --- Cached GET Requests
// --------------------------------------------------------------------------

/** Options to tweak the behavior of `useReques()`. Null values means
    keeping the last result. */
export interface UseRequestOptions<A> {
  /** Returned value in case where the server goes offline. */
  offline?: A | null;
  /** Temporary returned value when the request is pending. */
  pending?: A | null;
  /** Returned value when the request fails. */
  onError?: A | null;
  /** Re-send the request when any of the signals are sent. */
  onSignals?: Server.Signal[];
}

/**
  Cached GET request (Custom React Hook).

  Sends the specified GET request and returns its result. The request is send
  asynchronously and cached until any change in the request parameters or server
  state. The change in the server state are tracked by the signals specified
  when registering the request or by the one in options.onSignals if specified.

  Options can be used to tune more precisely the behavior of the hook.
 */
export function useRequest<In, Out>(
  rq: Server.GetRequest<In, Out>,
  params: In | undefined,
  options: UseRequestOptions<Out> = {},
): Out | undefined {
  const state = React.useRef<string>();
  const project = useProject();
  const [response, setResponse] =
    React.useState<Out | undefined>(options.offline ?? undefined);
  const footprint =
    project ? JSON.stringify([project, rq.name, params]) : undefined;

  const update = (opt: Out | undefined | null): void => {
    if (opt !== null) setResponse(opt);
  };

  async function trigger(): Promise<void> {
    if (project && rq && params !== undefined) {
      try {
        update(options.pending);
        const r = await Server.send(rq, params);
        update(r);
      } catch (error) {
        D.error(`Fail in useRequest '${rq.name}'. ${error}`);
        update(options.onError);
      }
    } else {
      update(options.offline);
    }
  }

  React.useEffect(() => {
    if (state.current !== footprint) {
      state.current = footprint;
      trigger();
    }
  });

  const signals = rq.signals.concat(options.onSignals ?? []);
  React.useEffect(() => {
    signals.forEach((s) => Server.onSignal(s, trigger));
    return () => {
      signals.forEach((s) => Server.offSignal(s, trigger));
    };
  });

  return response;
}

// --------------------------------------------------------------------------
// --- Dictionaries
// --------------------------------------------------------------------------

export type Tag = {
  name: string;
  label?: string;
  descr?: string;
};

const holdCurrent = { offline: null, pending: null, onError: null };

export type GetTags = Server.GetRequest<null, Tag[]>;

export function useTags(rq: GetTags): Map<string, Tag> {
  const tags = useRequest(rq, null, holdCurrent);
  return React.useMemo(() => {
    const m = new Map<string, Tag>();
    if (tags !== undefined)
      tags.forEach((tg) => m.set(tg.name, tg));
    return m;
  }, [tags]);
}

// --------------------------------------------------------------------------
// --- Synchronized States
// --------------------------------------------------------------------------

export interface Value<A> {
  name: string;
  signal: Server.Signal;
  getter: Server.GetRequest<null, A>;
}

export interface State<A> {
  name: string;
  signal: Server.Signal;
  getter: Server.GetRequest<null, A>;
  setter: Server.SetRequest<A, null>;
}

export interface Fetches<K, A> {
  reload: boolean;
  pending: number;
  updated: A[];
  removed: K[];
}

export interface Array<K, A> {
  name: string;
  order: Order<A>;
  getkey: (row: A) => K;
  signal: Server.Signal;
  reload: Server.GetRequest<null, null>;
  fetch: Server.GetRequest<number, Fetches<K, A>>;
}

// --------------------------------------------------------------------------
// --- Handler for Synchronized St byates
// --------------------------------------------------------------------------

interface Handler<A> {
  name: string;
  signal: Server.Signal;
  getter: Server.GetRequest<null, A>;
  setter?: Server.SetRequest<A, null>;
}

// shared for all projects
class SyncState<A> {
  UPDATE: Dome.Event;
  handler: Handler<A>;
  upToDate: boolean;
  value?: A;

  constructor(h: Handler<A>) {
    this.handler = h;
    this.UPDATE = new STATE(h.name);
    this.upToDate = false;
    this.value = undefined;
    this.update = this.update.bind(this);
    this.getValue = this.getValue.bind(this);
    this.setValue = this.setValue.bind(this);
    PROJECT.on(this.update);
  }

  getValue(): A | undefined {
    const running = Server.isRunning();
    if (!this.upToDate && running) {
      this.update();
    }
    return running ? this.value : undefined;
  }

  async setValue(v: A): Promise<void> {
    try {
      this.upToDate = true;
      this.value = v;
      const setter = this.handler.getter;
      if (setter) await Server.send(setter, v);
      this.UPDATE.emit();
    } catch (error) {
      D.error(
        `Fail to set value of SyncState '${this.handler.name}'.`,
        `${error}`,
      );
      this.UPDATE.emit();
    }
  }

  async update(): Promise<void> {
    try {
      this.upToDate = true;
      if (Server.isRunning()) {
        const v = await Server.send(this.handler.getter, null);
        this.value = v;
        this.UPDATE.emit();
      } else if (this.value !== undefined) {
        this.value = undefined;
        this.UPDATE.emit();
      }
    } catch (error) {
      D.error(
        `Fail to update SyncState '${this.handler.name}'.`,
        `${error}`,
      );
      this.value = undefined;
      this.UPDATE.emit();
    }
  }
}

// --------------------------------------------------------------------------
// --- Synchronized States Registry
// --------------------------------------------------------------------------

const syncStates = new Map<string, SyncState<unknown>>();

function getSyncState<A>(h: Handler<A>): SyncState<A> {
  const id = `${currentProject}@${h.name}`;
  let s = syncStates.get(id) as SyncState<A> | undefined;
  if (!s) {
    s = new SyncState(h);
    syncStates.set(id, s);
  }
  return s;
}

Server.onShutdown(() => syncStates.clear());

// --------------------------------------------------------------------------
// --- Synchronized State Hooks
// --------------------------------------------------------------------------

/** Synchronization with a (projectified) server state. */
export function useSyncState<A>(
  st: State<A>,
): [A | undefined, (value: A) => void] {
  const s = getSyncState(st);
  Dome.useUpdate(PROJECT, s.UPDATE);
  Server.useSignal(s.handler.signal, s.update);
  return [s.getValue(), s.setValue];
}

/** Synchronization with a (projectified) server value. */
export function useSyncValue<A>(va: Value<A>): A | undefined {
  const s = getSyncState(va);
  Dome.useUpdate(PROJECT, s.UPDATE);
  Server.useSignal(s.handler.signal, s.update);
  return s.getValue();
}

// --------------------------------------------------------------------------
// --- Synchronized Arrays
// --------------------------------------------------------------------------

// one per project
class SyncArray<K, A> {
  handler: Array<K, A>;
  upToDate: boolean;
  fetching: boolean;
  model: CompactModel<K, A>;

  constructor(h: Array<K, A>) {
    this.handler = h;
    this.fetching = false;
    this.upToDate = false;
    this.model = new CompactModel(h.getkey);
    this.model.setNaturalOrder(h.order);
    this.fetch = this.fetch.bind(this);
    this.reload = this.reload.bind(this);
    this.update = this.update.bind(this);
  }

  update(): void {
    if (!this.upToDate && Server.isRunning()) this.fetch();
  }

  async fetch(): Promise<void> {
    if (this.fetching || !Server.isRunning()) return;
    try {
      this.fetching = true;
      let pending;
      /* eslint-disable no-await-in-loop */
      do {
        const data = await Server.send(this.handler.fetch, 20000);
        const { reload = false, removed = [], updated = [] } = data;
        const { model } = this;
        if (reload) model.removeAllData();
        model.updateData(updated);
        model.removeData(removed);
        if (reload || updated.length > 0 || removed.length > 0)
          model.reload();
        pending = data.pending ?? 0;
      } while (pending > 0);
      /* eslint-enable no-await-in-loop */
    } catch (error) {
      D.error(
        `Fail to retrieve the value of syncArray '${this.handler.name}'.`,
        error,
      );
    } finally {
      this.fetching = false;
      this.upToDate = true;
    }
  }

  async reload(): Promise<void> {
    try {
      this.model.clear();
      this.upToDate = false;
      if (Server.isRunning()) {
        await Server.send(this.handler.reload, null);
        this.fetch();
      }
    } catch (error) {
      D.error(
        `Fail to set reload of syncArray '${this.handler.name}'.`,
        `${error}`,
      );
    }
  }

}

// --------------------------------------------------------------------------
// --- Synchronized Arrays Registry
// --------------------------------------------------------------------------

const syncArrays = new Map<string, SyncArray<unknown, unknown>>();

function lookupSyncArray<K, A>(
  array: Array<K, A>,
): SyncArray<K, A> {
  const id = `${currentProject}@${array.name}`;
  let st = syncArrays.get(id) as SyncArray<K, A> | undefined;
  if (!st) {
    st = new SyncArray(array);
    syncArrays.set(id, st as SyncArray<unknown, unknown>);
  }
  return st;
}

Server.onShutdown(() => syncArrays.clear());

// --------------------------------------------------------------------------
// --- Synchronized Array Hooks
// --------------------------------------------------------------------------

/** Force a Synchronized Array to reload. */
export function reloadArray<K, A>(arr: Array<K, A>): void {
  lookupSyncArray(arr).reload();
}

/**
   Use Synchronized Array (Custom React Hook).

   Unless specified, the hook makes the component re-render on every
   update. Disabling this automatic re-rendering can be an option when
   using the model to make a table view, which automatically synchronizes on
   model updates.
   @param sync Whether the component re-renders on updates (default is `true`).
 */
export function useSyncArray<K, A>(
  arr: Array<K, A>,
  sync = true,
): CompactModel<K, A> {
  Dome.useUpdate(PROJECT);
  const st = lookupSyncArray(arr);
  React.useEffect(() => st.update(), [st]);
  Server.useSignal(arr.signal, st.fetch);
  st.update();
  useModel(st.model, sync);
  return st.model;
}

/**
   Return the associated array model.
*/
export function getSyncArray<K, A>(
  arr: Array<K, A>,
): CompactModel<K, A> {
  const st = lookupSyncArray(arr);
  return st.model;
}

/**
   Link on the associated array model.
   @param onReload callback on reload event and update event if not specified.
   @param onUpdate callback on update event.
 */
export function onSyncArray<K, A>(
  arr: Array<K, A>,
  onReload?: () => void,
  onUpdate?: () => void,
): Client {
  const st = lookupSyncArray(arr);
  return st.model.link(onReload, onUpdate);
}

// --------------------------------------------------------------------------
// --- Selection
// --------------------------------------------------------------------------

/** An AST location.
 *
 *  Properties [[function]] and [[marker]] are optional,
 *  but at least one of the two must be set.
 */
export type Location = {
  fct?: string;
  marker?: Ast.marker;
};

export interface HistorySelection {
  /** Previous locations with respect to the [[current]] one. */
  prevSelections: Location[];
  /** Next locations with respect to the [[current]] one. */
  nextSelections: Location[];
}

/** Actions on history selections:
 * - `HISTORY_PREV` jumps to previous history location
 *   (first in [[prevSelections]]).
 * - `HISTORY_NEXT` jumps to next history location
 *   (first in [[nextSelections]]).
 */
export type HistorySelectActions = 'HISTORY_PREV' | 'HISTORY_NEXT';

/** A selection of multiple locations. */
export interface MultipleSelection {
  /** Name of the multiple selection.  */
  name: string;
  /** Explanatory description of the multiple selection.  */
  title: string;
  /** The index of the current selected location in [[allSelections]]. */
  index: number;
  /** All locations forming a multiple selection. */
  allSelections: Location[];
}

/** A select action on multiple locations. */
export interface MultipleSelect {
  readonly name: string;
  readonly title: string;
  readonly index: number;
  readonly locations: Location[];
}

/** Select the [[index]]-nth location of the current multiple selection. */
export interface NthSelect {
  readonly index: number;
}

/** Actions on multiple selections:
 * - [[MultipleSelect]].
 * - [[NthSelect]].
 * - `MULTIPLE_PREV` jumps to previous location of the multiple selections.
 * - `MULTIPLE_NEXT` jumps to next location of the multiple selections.
 * - `MULTIPLE_CYCLE` cycles between the multiple selections.
 * - `MULTIPLE_CLEAR` clears the multiple selection.
 */
export type MultipleSelectActions =
  MultipleSelect | NthSelect
  | 'MULTIPLE_PREV' | 'MULTIPLE_NEXT' | 'MULTIPLE_CYCLE' | 'MULTIPLE_CLEAR';

export interface Selection {
  /** Current selection. May be one in [[history]] or [[multiple]]. */
  current?: Location;
  /** History of selections. */
  history: HistorySelection;
  /** Multiple selections at once. */
  multiple: MultipleSelection;
}

/** A select action on a location. */
export interface SingleSelect {
  readonly location: Location;
}

/** Actions on selection:
 * - [[SingleSelect]].
 * - [[HistorySelectActions]].
 * - [[MultipleSelectActions]].
 */
export type SelectionActions =
  SingleSelect | HistorySelectActions | MultipleSelectActions;

function isSingleSelect(a: SelectionActions): a is SingleSelect {
  return (a as SingleSelect).location !== undefined;
}

function isMultipleSelect(a: SelectionActions): a is MultipleSelect {
  return (
    (a as MultipleSelect).locations !== undefined &&
    (a as MultipleSelect).index !== undefined
  );
}

function isNthSelect(a: SelectionActions): a is NthSelect {
  return (a as NthSelect).index !== undefined;
}

/** Update selection to the given location. */
function selectLocation(s: Selection, location: Location): Selection {
  const [prevSelections, nextSelections] =
    s.current && s.current.fct !== location.fct ?
      [[s.current, ...s.history.prevSelections], []] :
      [s.history.prevSelections, s.history.nextSelections];
  return {
    ...s,
    current: location,
    history: { prevSelections, nextSelections },
  };
}

/** Compute the next selection picking from the current history, depending on
 *  action.
 */
function fromHistory(s: Selection, action: HistorySelectActions): Selection {
  switch (action) {
    case 'HISTORY_PREV': {
      const [pS, ...prevS] = s.history.prevSelections;
      return {
        ...s,
        current: pS,
        history: {
          prevSelections: prevS,
          nextSelections:
            [(s.current as Location), ...s.history.nextSelections],
        },
      };
    }
    case 'HISTORY_NEXT': {
      const [nS, ...nextS] = s.history.nextSelections;
      return {
        ...s,
        current: nS,
        history: {
          prevSelections:
            [(s.current as Location), ...s.history.prevSelections],
          nextSelections: nextS,
        },
      };
    }
    default:
      return s;
  }
}

/** Compute the next selection picking from the current multiple, depending on
 *  action.
 */
function fromMultipleSelections(
  s: Selection,
  a: 'MULTIPLE_PREV' | 'MULTIPLE_NEXT' | 'MULTIPLE_CYCLE' | 'MULTIPLE_CLEAR',
): Selection {
  switch (a) {
    case 'MULTIPLE_PREV':
    case 'MULTIPLE_NEXT':
    case 'MULTIPLE_CYCLE': {
      const idx =
        a === 'MULTIPLE_PREV' ?
          s.multiple.index - 1 :
          s.multiple.index + 1;
      const index =
        a === 'MULTIPLE_CYCLE' && idx >= s.multiple.allSelections.length ?
          0 :
          idx;
      if (0 <= index && index < s.multiple.allSelections.length) {
        const multiple = { ...s.multiple, index };
        return selectLocation(
          { ...s, multiple },
          s.multiple.allSelections[index],
        );
      }
      return s;
    }
    case 'MULTIPLE_CLEAR':
      return {
        ...s,
        multiple: {
          name: '',
          title: '',
          index: 0,
          allSelections: [],
        },
      };
    default:
      return s;
  }
}

/** Compute the next selection based on the current one and the given action. */
function reducer(s: Selection, action: SelectionActions): Selection {
  if (isSingleSelect(action)) {
    return selectLocation(s, action.location);
  }
  if (isMultipleSelect(action)) {
    const index = action.index > 0 ? action.index : 0;
    const selection =
      action.locations.length === 0 ? s :
        selectLocation(s, action.locations[index]);
    return {
      ...selection,
      multiple: {
        name: action.name,
        title: action.title,
        allSelections: action.locations,
        index,
      },
    };
  }
  if (isNthSelect(action)) {
    const { index } = action;
    if (0 <= index && index < s.multiple.allSelections.length) {
      const location = s?.multiple.allSelections[index];
      const selection = selectLocation(s, location);
      const multiple = { ...selection.multiple, index };
      return { ...selection, multiple };
    }
    return s;
  }
  switch (action) {
    case 'HISTORY_PREV':
    case 'HISTORY_NEXT':
      return fromHistory(s, action);
    case 'MULTIPLE_PREV':
    case 'MULTIPLE_NEXT':
    case 'MULTIPLE_CYCLE':
    case 'MULTIPLE_CLEAR':
      return fromMultipleSelections(s, action);
    default:
      return s;
  }
}

/** The initial selection is empty. */
const emptySelection = {
  current: undefined,
  history: {
    prevSelections: [],
    nextSelections: [],
  },
  multiple: {
    name: '',
    title: '',
    index: 0,
    allSelections: [],
  },
};

export type Hovered = Location | undefined;
export const MetaSelection = new Dome.Event<Location>('frama-c-meta-selection');
export const GlobalHovered = new GlobalState<Hovered>(undefined);
export const GlobalSelection = new GlobalState<Selection>(emptySelection);

Server.onShutdown(() => GlobalSelection.setValue(emptySelection));

export function setHovered(h: Hovered): void { GlobalHovered.setValue(h); }
export function useHovered(): [Hovered, (h: Hovered) => void] {
  return useGlobalState(GlobalHovered);
}

export function setSelection(location: Location, meta = false): void {
  const s = GlobalSelection.getValue();
  GlobalSelection.setValue(reducer(s, { location }));
  if (meta) MetaSelection.emit(location);
}

/** Current selection. */
export function useSelection(): [Selection, (a: SelectionActions) => void] {
  const [current, setCurrent] = useGlobalState(GlobalSelection);
  const callback = React.useCallback((action) => {
    setCurrent(reducer(current, action));
  }, [current, setCurrent]);
  return [current, callback];
}

/** Resets the selected locations. */
export async function resetSelection(): Promise<void> {
  GlobalSelection.setValue(emptySelection);
  if (Server.isRunning()) {
    try {
      const main = await Server.send(Ast.getMainFunction, {});
      // If the selection has already been modified, do not change it.
      if (main && GlobalSelection.getValue() === emptySelection) {
        GlobalSelection.setValue({ ...emptySelection, current: { fct: main } });
      }
    } catch (err) {
      if (err) D.warn('Request error', err);
    }
  }
}

/* Select the main function when the current project changes and the selection
   is still empty (which happens at the start of the GUI). */
PROJECT.on(async () => {
  if (GlobalSelection.getValue() === emptySelection)
    resetSelection();
});

// --------------------------------------------------------------------------
