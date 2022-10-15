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

/* --- Generated Frama-C Server API --- */

/**
   Property Services
   @packageDocumentation
   @module frama-c/kernel/api/properties
*/

//@ts-ignore
import * as Json from 'dome/data/json';
//@ts-ignore
import * as Compare from 'dome/data/compare';
//@ts-ignore
import * as Server from 'frama-c/server';
//@ts-ignore
import * as State from 'frama-c/states';

//@ts-ignore
import { bySource } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jSource } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jSourceSafe } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { source } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { byTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTagSafe } from 'frama-c/kernel/api/data';
//@ts-ignore
import { tag } from 'frama-c/kernel/api/data';

/** Property Kinds */
export enum propKind {
  /** Contract behavior */
  behavior = 'behavior',
  /** Complete behaviors clause */
  complete = 'complete',
  /** Disjoint behaviors clause */
  disjoint = 'disjoint',
  /** Clause `@assumes` */
  assumes = 'assumes',
  /** Function precondition */
  requires = 'requires',
  /** Instance of a precondition at a call site */
  instance = 'instance',
  /** Clause `@breaks` */
  breaks = 'breaks',
  /** Clause `@continues` */
  continues = 'continues',
  /** Clause `@returns` */
  returns = 'returns',
  /** Clause `@exits` */
  exits = 'exits',
  /** Function postcondition */
  ensures = 'ensures',
  /** Function termination clause */
  terminates = 'terminates',
  /** Function allocation */
  allocates = 'allocates',
  /** Clause `@decreases` */
  decreases = 'decreases',
  /** Function assigns */
  assigns = 'assigns',
  /** Functional dependencies in function assigns */
  froms = 'froms',
  /** Assertion */
  assert = 'assert',
  /** Check */
  check = 'check',
  /** Hypothesis */
  admit = 'admit',
  /** Clause `@loop invariant` */
  loop_invariant = 'loop_invariant',
  /** Clause `@loop assigns` */
  loop_assigns = 'loop_assigns',
  /** Clause `@loop variant` */
  loop_variant = 'loop_variant',
  /** Clause `@loop allocates` */
  loop_allocates = 'loop_allocates',
  /** Clause `@loop pragma` */
  loop_pragma = 'loop_pragma',
  /** Reachable statement */
  reachable = 'reachable',
  /** Statement contract */
  code_contract = 'code_contract',
  /** Generalized loop invariant */
  code_invariant = 'code_invariant',
  /** Type invariant */
  type_invariant = 'type_invariant',
  /** Global invariant */
  global_invariant = 'global_invariant',
  /** Axiomatic definitions */
  axiomatic = 'axiomatic',
  /** Logical axiom */
  axiom = 'axiom',
  /** Logical lemma */
  lemma = 'lemma',
  /** Logical check lemma */
  check_lemma = 'check_lemma',
  /** ACSL extension */
  extension = 'extension',
}

/** Loose decoder for `propKind` */
export const jPropKind: Json.Loose<propKind> = Json.jEnum(propKind);

/** Safe decoder for `propKind` */
export const jPropKindSafe: Json.Safe<propKind> =
  Json.jFail(Json.jEnum(propKind),'kernel.properties.propKind expected');

/** Natural order for `propKind` */
export const byPropKind: Compare.Order<propKind> = Compare.byEnum(propKind);

const propKindTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.properties.propKindTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const propKindTags: Server.GetRequest<null,tag[]>= propKindTags_internal;

/** Property Status (consolidated) */
export enum propStatus {
  /** Unknown status */
  unknown = 'unknown',
  /** Unknown status (never tried) */
  never_tried = 'never_tried',
  /** Inconsistent status */
  inconsistent = 'inconsistent',
  /** Valid property */
  valid = 'valid',
  /** Valid (under hypotheses) */
  valid_under_hyp = 'valid_under_hyp',
  /** Valid (external assumption) */
  considered_valid = 'considered_valid',
  /** Invalid property (counter example found) */
  invalid = 'invalid',
  /** Invalid property (under hypotheses) */
  invalid_under_hyp = 'invalid_under_hyp',
  /** Dead property (but invalid) */
  invalid_but_dead = 'invalid_but_dead',
  /** Dead property (but valid) */
  valid_but_dead = 'valid_but_dead',
  /** Dead property (but unknown) */
  unknown_but_dead = 'unknown_but_dead',
}

/** Loose decoder for `propStatus` */
export const jPropStatus: Json.Loose<propStatus> = Json.jEnum(propStatus);

/** Safe decoder for `propStatus` */
export const jPropStatusSafe: Json.Safe<propStatus> =
  Json.jFail(Json.jEnum(propStatus),'kernel.properties.propStatus expected');

/** Natural order for `propStatus` */
export const byPropStatus: Compare.Order<propStatus> =
  Compare.byEnum(propStatus);

const propStatusTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.properties.propStatusTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const propStatusTags: Server.GetRequest<null,tag[]>= propStatusTags_internal;

/** Alarm Kinds */
export enum alarms {
  /** Integer division by zero */
  division_by_zero = 'division_by_zero',
  /** Invalid pointer dereferencing */
  mem_access = 'mem_access',
  /** Array access out of bounds */
  index_bound = 'index_bound',
  /** Invalid pointer computation */
  pointer_value = 'pointer_value',
  /** Invalid shift */
  shift = 'shift',
  /** Invalid pointer comparison */
  ptr_comparison = 'ptr_comparison',
  /** Operation on pointers within different blocks */
  differing_blocks = 'differing_blocks',
  /** Integer overflow or downcast */
  overflow = 'overflow',
  /** Overflow in float to int conversion */
  float_to_int = 'float_to_int',
  /** Unsequenced side-effects on non-separated memory */
  separation = 'separation',
  /** Overlap between left- and right-hand-side in assignment */
  overlap = 'overlap',
  /** Uninitialized memory read */
  initialization = 'initialization',
  /** Read of a dangling pointer */
  dangling_pointer = 'dangling_pointer',
  /** Non-finite (nan or infinite) floating-point value */
  is_nan_or_infinite = 'is_nan_or_infinite',
  /** NaN floating-point value */
  is_nan = 'is_nan',
  /** Pointer to a function with non-compatible type */
  function_pointer = 'function_pointer',
  /** Uninitialized memory read of union */
  initialization_of_union = 'initialization_of_union',
  /** Trap representation of a _Bool lvalue */
  bool_value = 'bool_value',
}

/** Loose decoder for `alarms` */
export const jAlarms: Json.Loose<alarms> = Json.jEnum(alarms);

/** Safe decoder for `alarms` */
export const jAlarmsSafe: Json.Safe<alarms> =
  Json.jFail(Json.jEnum(alarms),'kernel.properties.alarms expected');

/** Natural order for `alarms` */
export const byAlarms: Compare.Order<alarms> = Compare.byEnum(alarms);

const alarmsTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.properties.alarmsTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const alarmsTags: Server.GetRequest<null,tag[]>= alarmsTags_internal;

/** Data for array rows [`status`](#status)  */
export interface statusData {
  /** Entry identifier. */
  key: Json.key<'#property'>;
  /** Full description */
  descr: string;
  /** Kind */
  kind: propKind;
  /** Names */
  names: string[];
  /** Status */
  status: propStatus;
  /** Function */
  fct?: Json.key<'#fct'>;
  /** Instruction */
  kinstr?: Json.key<'#stmt'>;
  /** Position */
  source: source;
  /** Alarm name (if the property is an alarm) */
  alarm?: string;
  /** Alarm description (if the property is an alarm) */
  alarm_descr?: string;
  /** Predicate */
  predicate?: string;
}

/** Loose decoder for `statusData` */
export const jStatusData: Json.Loose<statusData> =
  Json.jObject({
    key: Json.jFail(Json.jKey<'#property'>('#property'),'#property expected'),
    descr: Json.jFail(Json.jString,'String expected'),
    kind: jPropKindSafe,
    names: Json.jList(Json.jString),
    status: jPropStatusSafe,
    fct: Json.jKey<'#fct'>('#fct'),
    kinstr: Json.jKey<'#stmt'>('#stmt'),
    source: jSourceSafe,
    alarm: Json.jString,
    alarm_descr: Json.jString,
    predicate: Json.jString,
  });

/** Safe decoder for `statusData` */
export const jStatusDataSafe: Json.Safe<statusData> =
  Json.jFail(jStatusData,'StatusData expected');

/** Natural order for `statusData` */
export const byStatusData: Compare.Order<statusData> =
  Compare.byFields
    <{ key: Json.key<'#property'>, descr: string, kind: propKind,
       names: string[], status: propStatus, fct?: Json.key<'#fct'>,
       kinstr?: Json.key<'#stmt'>, source: source, alarm?: string,
       alarm_descr?: string, predicate?: string }>({
    key: Compare.string,
    descr: Compare.string,
    kind: byPropKind,
    names: Compare.array(Compare.string),
    status: byPropStatus,
    fct: Compare.defined(Compare.string),
    kinstr: Compare.defined(Compare.string),
    source: bySource,
    alarm: Compare.defined(Compare.string),
    alarm_descr: Compare.defined(Compare.string),
    predicate: Compare.defined(Compare.string),
  });

/** Signal for array [`status`](#status)  */
export const signalStatus: Server.Signal = {
  name: 'kernel.properties.signalStatus',
};

const reloadStatus_internal: Server.GetRequest<null,null> = {
  kind: Server.RqKind.GET,
  name:   'kernel.properties.reloadStatus',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Force full reload for array [`status`](#status)  */
export const reloadStatus: Server.GetRequest<null,null>= reloadStatus_internal;

const fetchStatus_internal: Server.GetRequest<
  number,
  { pending: number, updated: statusData[], removed: Json.key<'#property'>[],
    reload: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.properties.fetchStatus',
  input:  Json.jNumber,
  output: Json.jObject({
            pending: Json.jFail(Json.jNumber,'Number expected'),
            updated: Json.jList(jStatusData),
            removed: Json.jList(Json.jKey<'#property'>('#property')),
            reload: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Data fetcher for array [`status`](#status)  */
export const fetchStatus: Server.GetRequest<
  number,
  { pending: number, updated: statusData[], removed: Json.key<'#property'>[],
    reload: boolean }
  >= fetchStatus_internal;

const status_internal: State.Array<Json.key<'#property'>,statusData> = {
  name: 'kernel.properties.status',
  getkey: ((d:statusData) => d.key),
  signal: signalStatus,
  fetch: fetchStatus,
  reload: reloadStatus,
  order: byStatusData,
};
/** Status of Registered Properties */
export const status: State.Array<Json.key<'#property'>,statusData> = status_internal;

/* ------------------------------------- */
