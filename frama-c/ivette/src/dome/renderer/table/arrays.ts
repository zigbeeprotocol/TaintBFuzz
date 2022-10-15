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
// --- Array Models
// --------------------------------------------------------------------------

/**
   @packageDocumentation
   @module dome/table/arrays
*/

import { Debug } from 'dome';
import * as Compare from 'dome/data/compare';
import type { ByFields, Order } from 'dome/data/compare';
import {
  SortingInfo, Sorting,
  Filter, Filtering,
  Model, Collection, forEach,
} from './models';

const D = new Debug('Dome');

// --------------------------------------------------------------------------
// --- Sorting Utilities
// --------------------------------------------------------------------------

export type ByColumns<Row> = { [dataKey: string]: Compare.Order<Row> };

export interface PACK<Key, Row> {
  index: number | undefined;
  key: Key;
  row: Row;
}

export type SORT<K, R> = Order<PACK<K, R>>;

function orderBy<K, R>(
  columns: ByColumns<R>,
  ord: SortingInfo,
): SORT<K, R> {
  const dataKey = ord.sortBy;
  const byData = columns[dataKey] ?? Compare.equal;
  const rv = ord.sortDirection === 'DESC';
  type D = PACK<K, R>;
  const byEntry = (x: D, y: D): number => byData(x.row, y.row);
  const byIndex = (x: D, y: D): number => (x.index ?? 0) - (y.index ?? 0);
  return Compare.direction(Compare.sequence(byEntry, byIndex), rv);
}

function orderByRing<K, R>(
  natural: undefined | Order<R>,
  columns: undefined | ByColumns<R>,
  ring: SortingInfo[],
): SORT<K, R> {
  type D = PACK<K, R>;
  const byRing = columns ? ring.map((ord) => orderBy(columns, ord)) : [];
  const byData = natural ? ((x: D, y: D) => natural(x.row, y.row)) : undefined;
  return Compare.sequence(...byRing, byData);
}

// --------------------------------------------------------------------------
// --- Filtering Utilities
// --------------------------------------------------------------------------

type INDEX<K, R> = Map<K, PACK<K, R>>;

// --------------------------------------------------------------------------
// --- Array Model
// --------------------------------------------------------------------------

export class ArrayModel<Key, Row>
  extends Model<Key, Row>
  implements Sorting, Filtering<Key, Row>
{

  // Hold raw data (unsorted, unfiltered)
  private index: INDEX<Key, Row> = new Map();

  // Hold filtered & sorted data (computed and cached on demand)
  private table?: PACK<Key, Row>[];

  // Hold filtered & sorted array of data (computed and cached on demand)
  private array?: Row[];

  // Filtered-out Row Count
  private filtered = 0;

  // Filtering function
  private filter?: Filter<Key, Row>;

  // Natural ordering (if any)
  private natural?: Order<Row>;

  // Sortable columns and associated ordering (if any)
  private columns?: ByColumns<Row>;

  // Comparison Ring
  private ring: SortingInfo[] = [];

  // Consolidated order (computed on demand)
  private order?: SORT<Key, Row>;

  // --------------------------------------------------------------------------
  // --- Rebuild Array
  // --------------------------------------------------------------------------

  // Lazily compute order
  protected sorter(): SORT<Key, Row> {
    let current = this.order;
    if (current) return current;
    current = this.order = // eslint-disable-line no-multi-assign
      orderByRing(this.natural, this.columns, this.ring);
    return current;
  }

  // Lazily compute table ; modifies packed entries in place
  protected rebuild(): PACK<Key, Row>[] {
    const current = this.table;
    let filtered = 0;
    if (current !== undefined) return current;
    const table: PACK<Key, Row>[] = [];
    try {
      this.index.forEach((packed) => {
        packed.index = undefined;
        const phi = this.filter;
        if (!phi || phi(packed.row, packed.key))
          table.push(packed);
        else
          filtered++;
      });
      table.sort(this.sorter());
    } catch (err) {
      D.warn('error when rebuilding table:', err);
    }
    table.forEach((packed, index) => { packed.index = index; });
    this.table = table;
    this.filtered = filtered;
    return table;
  }

  // --------------------------------------------------------------------------
  // --- Proxy
  // --------------------------------------------------------------------------

  /** Non filtered. */
  getTotalRowCount(): number { return this.getRowCount() + this.filtered; }

  getRowCount(): number { return this.rebuild().length; }

  getRowAt(k: number): Row { return this.rebuild()[k]?.row; }

  getKeyAt(k: number): Key | undefined {
    const current = this.table;
    return current ? current[k]?.key : undefined;
  }

  getKeyFor(k: number, _: Row): Key | undefined { return this.getKeyAt(k); }

  getIndexOf(key: Key): number | undefined {
    const pack = this.index.get(key);
    if (!pack) return undefined;
    const k = pack.index;
    if (k === undefined || k < 0) return undefined;
    const current = this.table;
    return (current && k < current.length) ? k : undefined;
  }

  // --------------------------------------------------------------------------
  // --- Ordering
  // --------------------------------------------------------------------------

  /** Sets comparison functions for the specified columns. Previous
      comparison for un-specified columns are kept unchanged, if any.
      This will be used to refine
      [[setNaturalOrder]] in response to user column selection with
      [[setSorting]] provided you enable by-column sorting from the table view.
      Finally triggers a reload. */
  setColumnOrder(columns?: ByColumns<Row>): void {
    this.columns = { ...this.columns, ...columns };
    this.reload();
  }

  /** Sets natural ordering of the rows.
      It defines in which order the entries are rendered in the table.  This
      primary ordering can be refined in response to user column selection with
      [[setSorting]] provided you enable by-column sorting from the table view.
      Finally triggers a reload. */
  setNaturalOrder(order?: Order<Row>): void {
    this.natural = order;
    this.reload();
  }

  /**
     Sets both natural ordering and column ordering with the provided
     orders by fields. This is a combination of [[setColumnOrder]] and
     [[setNaturalOrder]] with [[dome/data/compare.byFields]].
   */
  setOrderingByFields(byfields: ByFields<Row>): void {
    this.natural = Compare.byFields(byfields);
    const columns = this.columns ?? {};
    const keys = Object.keys(byfields);
    for (let i = 0; i < keys.length; i++) {
      const dataKey = keys[i] as (string & keyof Row);
      const fn = byfields[dataKey];
      if (fn) columns[dataKey] = (x: Row, y: Row) => {
        const dx = x[dataKey];
        const dy = y[dataKey];
        if (dx === dy) return 0;
        if (dx === undefined) return 1;
        if (dy === undefined) return -1;
        return fn(dx, dy);
      };
    }
    this.columns = columns;
    this.reload();
  }

  /**
     Remove the sorting function for the provided column.
   */
  deleteColumnOrder(dataKey: string): void {
    const { columns } = this;
    if (columns) delete columns[dataKey];
    this.ring = this.ring.filter((ord) => ord.sortBy !== dataKey);
    this.reload();
  }

  /** Reorder rows with the provided column and direction.
      Previous ordering is kept and refined by the new one.
      Use `undefined` or `null` to reset the natural ordering. */
  setSorting(ord?: undefined | null | SortingInfo): void {
    if (ord) {
      const { ring } = this;
      const cur = ring[0];
      const fd = ord.sortBy;
      if (
        !cur ||
        cur.sortBy !== fd ||
        cur.sortDirection !== ord.sortDirection
      ) {
        const newRing = ring.filter((o) => o.sortBy !== fd);
        newRing.unshift(ord);
        this.ring = newRing;
        this.reload();
      }
    } else if (this.ring.length > 0) {
      this.ring = [];
      this.reload();
    }
  }

  canSortBy(column: string): boolean {
    const columns = this.columns;
    return !!columns && columns[column] !== undefined;
  }

  getSorting(): SortingInfo | undefined {
    return this.ring[0];
  }

  // --------------------------------------------------------------------------
  // --- Filtering
  // --------------------------------------------------------------------------

  setFilter(fn?: Filter<Key, Row>): void {
    const phi = this.filter;
    if (phi !== fn) {
      this.filter = fn;
      this.reload();
    }
  }

  // --------------------------------------------------------------------------
  // --- Full Updates
  // --------------------------------------------------------------------------

  /** Trigger a complete reload of the table. */
  reload(): void {
    this.array = undefined;
    this.table = undefined;
    this.order = undefined;
    super.reload();
  }

  /** Remove all data and reload. */
  clear(): void {
    this.index.clear();
    this.reload();
  }

  // --------------------------------------------------------------------------
  // --- Checks for Reload vs. Update
  // --------------------------------------------------------------------------

  private needReloadForUpdate(pack: PACK<Key, Row>): boolean {
    // Case where reload is already triggered
    const current = this.table;
    if (!current) return false;
    // Case where filtering of key has changed
    const k = pack.index ?? -1;
    const n = current ? current.length : 0;
    const phi = this.filter;
    const oldOk = 0 <= k && k < n;
    const nowOk = phi ? phi(pack.row, pack.key) : true;
    if (oldOk !== nowOk) return true;
    // Case where element was not displayed and will still not be
    if (!oldOk) return false;
    // Detecting if ordering is preserved
    const order = this.sorter();
    const prev = k - 1;
    if (0 <= prev && order(pack, current[prev]) < 0) return true;
    const next = k + 1;
    if (next < n && order(current[next], pack) < 0) return true;
    super.updateIndex(k);
    return false;
  }

  private needReloadForInsert(pack: PACK<Key, Row>): boolean {
    // Case where reload is already triggered
    const current = this.table;
    if (!current) return false;
    // Case where inserted element is filtered out
    const phi = this.filter;
    return phi ? phi(pack.row, pack.key) : true;
  }

  private needReloadForRemoval(pack: PACK<Key, Row>): boolean {
    // Case where reload is already triggered
    const current = this.table;
    if (!current) return false;
    // Case where inserted element is filtered out
    const k = pack.index ?? -1;
    return 0 <= k && k < current.length;
  }

  // --------------------------------------------------------------------------
  // --- Update item and optimized reload
  // --------------------------------------------------------------------------

  /**
     Update a data entry and signal the views only if needed.
     Use `undefined` to keep value unchanged, `null` for removal,
     or the new row data for update. This triggers a full
     reload if ordering or filtering if modified by the updated value,
     a update index if the row data is only modified and visible.
     Otherwise, no rendering is triggered since the modification
     is not visible.
     @param key - the entry identifier
     @param row - new value of `null` for removal
   */
  update(key: Key, row?: undefined | null | Row): void {
    if (row === undefined) return;
    const pack = this.index.get(key);
    let doReload = false;
    if (pack) {
      if (row === null) {
        // Removal
        this.index.delete(key);
        doReload = this.needReloadForRemoval(pack);
      } else {
        // Updated
        pack.row = row;
        doReload = this.needReloadForUpdate(pack);
      }
    } else {
      if (row === null) {
        // Nop
        return;
      }
      const newPack = { key, row, index: undefined };
      this.index.set(key, newPack);
      doReload = this.needReloadForInsert(newPack);

    }
    if (doReload) this.reload();
  }

  // --------------------------------------------------------------------------
  // ---  Batched Updates
  // --------------------------------------------------------------------------

  /**
     Silently removes the entry.
     Modification will be only visible after a final [[reload]].
     Useful for a large number of batched updates.
  */
  removeAllData(): void {
    this.index.clear();
  }

  /**
     Silently removes the entries.
     Modification will be only visible after a final [[reload]].
     Useful for a large number of batched updates.
     @param key - the removed entry.
   */
  removeData(keys: Collection<Key>): void {
    forEach(keys, (k) => this.index.delete(k));
  }

  /**
     Silently updates the entry.
     Modification will be only visible after a final [[reload]].
     Useful for a large number of batched updates.
     @param key - the entry to update.
     @param row - the new row data or `null` for removal.
   */
  setData(key: Key, row: null | Row): void {
    if (row !== null) {
      this.index.set(key, { key, row, index: undefined });
    } else {
      this.index.delete(key);
    }
  }

  /** Returns the data associated with a key (if any). */
  getData(key: Key): Row | undefined {
    return this.index.get(key)?.row;
  }

  /** Returns an array of filtered and sorted entries.
      Computed on demand and cached. */
  getArray(): Row[] {
    let arr = this.array;
    if (arr === undefined) {
      arr = this.array = // eslint-disable-line no-multi-assign
        this.rebuild().map((e) => e.row);
    }
    return arr;
  }

}

// --------------------------------------------------------------------------
// --- Compact Array Model
// --------------------------------------------------------------------------

/**
   @template Row - object data that also contains their « key ».
*/
export class CompactModel<Key, Row> extends ArrayModel<Key, Row> {

  getkey: (d: Row) => Key;

  /** @param key - the key property of `Row` holding an entry identifier. */
  constructor(getkey: (d: Row) => Key) {
    super();
    this.getkey = getkey;
  }

  /** Use the key getter directly. */
  getKeyFor(_: number, data: Row): Key | undefined { return this.getkey(data); }

  /**
     Silently add or update a collection of data.
     Requires a final trigger to update views.
  */
  updateData(data: Collection<Row>): void {
    forEach(data, (row: Row) => this.setData(this.getkey(row), row));
  }

  /**
     Replace all previous data with the new ones.
     Finally triggers a reload.
  */
  replaceAllDataWith(data: Collection<Row>): void {
    this.removeAllData();
    this.updateData(data);
    this.reload();
  }

}

// --------------------------------------------------------------------------
