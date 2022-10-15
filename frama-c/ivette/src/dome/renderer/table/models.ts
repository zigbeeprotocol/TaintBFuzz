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
// --- Models
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/table/models
*/

import React from 'react';
import { SortDirectionType } from 'react-virtualized';

// --------------------------------------------------------------------------
// --- Listeners
// --------------------------------------------------------------------------

/** Update callback. */
export type Trigger = () => void;

/** Client Views. */
export interface Client {
  /** Set the update callback of the client. */
  onUpdate(trigger?: Trigger): void;
  /** Set the reload callback of the client. */
  onReload(trigger?: Trigger): void;
  /** Set the watching range of the client. */
  watch(lower: number, upper: number): void;
  /** Unlink the client. */
  unlink(): void;
}

/** @internal */
interface Watcher {
  lower: number;
  upper: number;
  update: undefined | Trigger;
  reload: undefined | Trigger;
}

// --------------------------------------------------------------------------
// --- Sorting
// --------------------------------------------------------------------------

/** Sorting Info. */
export interface SortingInfo {
  /** The column identifier that triggers some sorting. */
  sortBy: string;
  /** The requested sorting direction (`'ASC'` or `'DESC'`). */
  sortDirection: SortDirectionType;
}

/** Sorting proxy.
    Can be provided along with Models or in a separate class or object. */
export interface Sorting {
  /** Whether the model can be sorted from the `dataKey` column identifier. */
  canSortBy(dataKey: string): boolean;
  /** Callback to respond to sorting requests from columns. */
  setSorting(order?: SortingInfo): void;
  /** Current sorting information. */
  getSorting(): SortingInfo | undefined;
}

// --------------------------------------------------------------------------
// --- Filtering
// --------------------------------------------------------------------------

export interface Filter<Key, Row> {
  (row: Row, key: Key): boolean;
}

export interface Filtering<Key, Row> {
  setFilter(fn?: Filter<Key, Row>): void;
}

// --------------------------------------------------------------------------
// --- Collection
// --------------------------------------------------------------------------

/** Convenient type for a collection of items. */
export type Collection<A> = undefined | null | A | Collection<A>[];

/** Iterator over collection. */
export function forEach<A>(data: Collection<A>, fn: (elt: A) => void): void {
  if (Array.isArray(data)) data.forEach((e) => forEach(e, fn));
  else if (data !== undefined && data !== null) fn(data);
}

// --------------------------------------------------------------------------
// --- Abstract Model
// --------------------------------------------------------------------------

/**
   A Model is responsible for keeping the tables and lists views in sync
   with their associated data sets. The model listens for updates, retrieves
   items from their index, and re-render the views when necessary.

   Several tables may connect to the same table model, but they will share the
   same number and ordering of items. However, each connected table will only
   render its own range of items and will re-render only when impacted by
   individual updates.

   The model might not hold the entire collection of data at the same time, but
   serves as a proxy for fetching data on demand. A model makes a distinction
   between:
   - `Key`: a key identifies a given entry in the table at any time;
   - `Row`: the row data associated to some `Key` at a given time;

   When row data change over time, the table views associated to the model
   use `Key` information to keep scrolling and selection states in sync.

   The model is responsible for:
   - providing row data to the views;
   - informing views of data updates;
   - compute row ordering with respect to ordering and/or filtering;
   - lookup key index with respect to ordering and/or filtering;

   When your data change over time, you shall invoke the following methods
   of the model to keep views in sync:
   - [[update]] or [[updateIndex]] when single or contiguous row data
   changes over time;
   - [[reload]] when the number of rows, their ordering, or (many) row data
   has been changed.

   It is always safe to use `reload` instead of `update` although it might be
   less performant.

   @template Key - identification of some entry
   @template Row - dynamic row data associated to some key
*/
export abstract class Model<Key, Row> {

  private clients = new Map<number, Watcher>();
  private clientsId = 0;

  constructor() {
    this.reload = this.reload.bind(this);
  }

  /**
     Shall return the number of rows to be currently displayed in the table.
     Negative values are considered as zero.
  */
  abstract getRowCount(): number;

  /**
     Shall return the current row data at a given index in the table, with
     respect to current filtering and ordering (if any).  Might return
     `undefined` if the index is invalid or not (yet) available.
  */
  abstract getRowAt(index: number): undefined | Row;

  /**
     Shall return the key at the given index. The specified index and data are
     those of the last corresponding call to [[getRowAt]].  Might return
     `undefined` if the index is invalid.
  */
  abstract getKeyAt(index: number): undefined | Key;

  /**
     Shall return the key of the given entry. The specified index and data
     are those of the last corresponding call to [[getRowAt]].
     Might return `undefined` if the index is invalid.
  */
  abstract getKeyFor(index: number, data: Row): undefined | Key;

  /**
     Shall return the index of a given entry in the table, identified by its
     key, with respect to current filtering and ordering (if any).
     Shall return
     `undefined` if the specified key no longer belong to the table or when it
     is currently filtered out.  Out-of-range indices would be treated as
     `undefined`.
  */
  abstract getIndexOf(key: Key): undefined | number;

  /**
     Signal an item update.
     Default implementation uses [[getIndexOf]] to retrieve the index and then
     delegates to [[updateIndex]].
     All views that might be rendering the specified item will be updated.
  */
  update(key: Key): void {
    const k = this.getIndexOf(key);
    if (k !== undefined && 0 <= k) this.updateIndex(k);
  }

  /**
     Signal a range of updates.
     @param first - the first updated item index
     @param last - the last updated item index (defaults to `first`)
  */
  updateIndex(first: number, last = first): void {
    if (first <= last) {
      this.clients.forEach(({ lower, upper, update }) => {
        if (update && first <= upper && lower <= last) update();
      });
    }
  }

  /**
     Re-render all views.
     Bound to this.
  */
  reload(): void {
    this.clients.forEach(({ reload }) => reload && reload());
  }

  /**
     Connect a client view to the model.
     The initial watching range is empty with no trigger.
     You normally never call this method directly.
     It is automatically called by table views.
     @param onReload - optional callback for reloads
     (and updates, unless specified)
     @param onUpdate - optional callback for updates
     (when different from reloads)
  */
  link(onReload?: Trigger, onUpdate?: Trigger): Client {
    const id = this.clientsId++;
    const m = this.clients;
    const w: Watcher & Client = {
      lower: 0,
      upper: 0,
      reload: onReload,
      update: onUpdate ?? onReload,
      onUpdate(s?: Trigger) { w.update = s; },
      onReload(s?: Trigger) { w.reload = s; },
      unlink() { m.delete(id); },
      watch(lower: number, upper: number) {
        w.lower = lower;
        w.upper = upper;
      },
    };
    m.set(id, w);
    return w;
  }

}

// --------------------------------------------------------------------------
// --- Model Hooks
// --------------------------------------------------------------------------

/**
   Make the component to synchronize with the model and re-render on
   every updates.
   @param sync - whether to synchronize on model updates or not, `true`
   by default.
   @return a number that can be used to memoize other effects
 */

export function useModel<K, R>(model: Model<K, R>, sync = true): number {
  const [age, setAge] = React.useState(0);
  React.useEffect(() => {
    if (sync) {
      const w = model.link(() => setImmediate(() => setAge(age + 1)));
      return w.unlink;
    }
    return undefined;
  });
  return age;
}

// --------------------------------------------------------------------------
