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
   Eva General Services
   @packageDocumentation
   @module frama-c/plugins/eva/api/general
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
import { byMarker } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jMarker } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jMarkerSafe } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { marker } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { byTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTagSafe } from 'frama-c/kernel/api/data';
//@ts-ignore
import { tag } from 'frama-c/kernel/api/data';

/** State of the computation of Eva Analysis. */
export type computationStateType = "not_computed" | "computing" | "computed";

/** Loose decoder for `computationStateType` */
export const jComputationStateType: Json.Loose<computationStateType> =
  Json.jUnion<"not_computed" | "computing" | "computed">(
    Json.jTag("not_computed"),
    Json.jTag("computing"),
    Json.jTag("computed"),
  );

/** Safe decoder for `computationStateType` */
export const jComputationStateTypeSafe: Json.Safe<computationStateType> =
  Json.jFail(jComputationStateType,'ComputationStateType expected');

/** Natural order for `computationStateType` */
export const byComputationStateType: Compare.Order<computationStateType> =
  Compare.structural;

/** Signal for state [`computationState`](#computationstate)  */
export const signalComputationState: Server.Signal = {
  name: 'plugins.eva.general.signalComputationState',
};

const getComputationState_internal: Server.GetRequest<
  null,
  computationStateType
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.getComputationState',
  input:  Json.jNull,
  output: jComputationStateType,
  signals: [],
};
/** Getter for state [`computationState`](#computationstate)  */
export const getComputationState: Server.GetRequest<
  null,
  computationStateType
  >= getComputationState_internal;

const computationState_internal: State.Value<computationStateType> = {
  name: 'plugins.eva.general.computationState',
  signal: signalComputationState,
  getter: getComputationState,
};
/** The current computation state of the analysis. */
export const computationState: State.Value<computationStateType> = computationState_internal;

const getCallers_internal: Server.GetRequest<
  Json.key<'#fct'>,
  [ Json.key<'#fct'>, Json.key<'#stmt'> ][]
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.getCallers',
  input:  Json.jKey<'#fct'>('#fct'),
  output: Json.jList(
            Json.jTry(
              Json.jPair(
                Json.jFail(Json.jKey<'#fct'>('#fct'),'#fct expected'),
                Json.jFail(Json.jKey<'#stmt'>('#stmt'),'#stmt expected'),
              ))),
  signals: [],
};
/** Get the list of call site of a function */
export const getCallers: Server.GetRequest<
  Json.key<'#fct'>,
  [ Json.key<'#fct'>, Json.key<'#stmt'> ][]
  >= getCallers_internal;

/** Unreachable and non terminating statements. */
export interface deadCode {
  /** List of unreachable statements. */
  unreachable: marker[];
  /** List of reachable but non terminating statements. */
  nonTerminating: marker[];
}

/** Loose decoder for `deadCode` */
export const jDeadCode: Json.Loose<deadCode> =
  Json.jObject({
    unreachable: Json.jList(jMarker),
    nonTerminating: Json.jList(jMarker),
  });

/** Safe decoder for `deadCode` */
export const jDeadCodeSafe: Json.Safe<deadCode> =
  Json.jFail(jDeadCode,'DeadCode expected');

/** Natural order for `deadCode` */
export const byDeadCode: Compare.Order<deadCode> =
  Compare.byFields
    <{ unreachable: marker[], nonTerminating: marker[] }>({
    unreachable: Compare.array(byMarker),
    nonTerminating: Compare.array(byMarker),
  });

const getDeadCode_internal: Server.GetRequest<Json.key<'#fct'>,deadCode> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.getDeadCode',
  input:  Json.jKey<'#fct'>('#fct'),
  output: jDeadCode,
  signals: [],
};
/** Get the lists of unreachable and of non terminating statements in a function */
export const getDeadCode: Server.GetRequest<Json.key<'#fct'>,deadCode>= getDeadCode_internal;

/** Taint status of logical properties */
export enum taintStatus {
  /** **Not computed:**
      the Eva taint domain has not been enabled, or the Eva analysis has not been run */
  not_computed = 'not_computed',
  /** **Error:**
      the memory zone on which this property depends could not be computed */
  error = 'error',
  /** **Not applicable:** no taint for this kind of property */
  not_applicable = 'not_applicable',
  /** **Data tainted:**
      this property is related to a memory location that can be affected by an attacker */
  data_tainted = 'data_tainted',
  /** **Control tainted:**
      this property is related to a memory location whose assignment depends on path conditions that can be affected by an attacker */
  control_tainted = 'control_tainted',
  /** **Untainted property:** this property is safe */
  not_tainted = 'not_tainted',
}

/** Loose decoder for `taintStatus` */
export const jTaintStatus: Json.Loose<taintStatus> = Json.jEnum(taintStatus);

/** Safe decoder for `taintStatus` */
export const jTaintStatusSafe: Json.Safe<taintStatus> =
  Json.jFail(Json.jEnum(taintStatus),
    'plugins.eva.general.taintStatus expected');

/** Natural order for `taintStatus` */
export const byTaintStatus: Compare.Order<taintStatus> =
  Compare.byEnum(taintStatus);

const taintStatusTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.taintStatusTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const taintStatusTags: Server.GetRequest<null,tag[]>= taintStatusTags_internal;

/** Data for array rows [`properties`](#properties)  */
export interface propertiesData {
  /** Entry identifier. */
  key: Json.key<'#property'>;
  /** Is the property invalid in some context of the analysis? */
  priority: boolean;
  /** Is the property tainted according to the Eva taint domain? */
  taint: taintStatus;
}

/** Loose decoder for `propertiesData` */
export const jPropertiesData: Json.Loose<propertiesData> =
  Json.jObject({
    key: Json.jFail(Json.jKey<'#property'>('#property'),'#property expected'),
    priority: Json.jFail(Json.jBoolean,'Boolean expected'),
    taint: jTaintStatusSafe,
  });

/** Safe decoder for `propertiesData` */
export const jPropertiesDataSafe: Json.Safe<propertiesData> =
  Json.jFail(jPropertiesData,'PropertiesData expected');

/** Natural order for `propertiesData` */
export const byPropertiesData: Compare.Order<propertiesData> =
  Compare.byFields
    <{ key: Json.key<'#property'>, priority: boolean, taint: taintStatus }>({
    key: Compare.string,
    priority: Compare.boolean,
    taint: byTaintStatus,
  });

/** Signal for array [`properties`](#properties)  */
export const signalProperties: Server.Signal = {
  name: 'plugins.eva.general.signalProperties',
};

const reloadProperties_internal: Server.GetRequest<null,null> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.reloadProperties',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Force full reload for array [`properties`](#properties)  */
export const reloadProperties: Server.GetRequest<null,null>= reloadProperties_internal;

const fetchProperties_internal: Server.GetRequest<
  number,
  { pending: number, updated: propertiesData[],
    removed: Json.key<'#property'>[], reload: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.fetchProperties',
  input:  Json.jNumber,
  output: Json.jObject({
            pending: Json.jFail(Json.jNumber,'Number expected'),
            updated: Json.jList(jPropertiesData),
            removed: Json.jList(Json.jKey<'#property'>('#property')),
            reload: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Data fetcher for array [`properties`](#properties)  */
export const fetchProperties: Server.GetRequest<
  number,
  { pending: number, updated: propertiesData[],
    removed: Json.key<'#property'>[], reload: boolean }
  >= fetchProperties_internal;

const properties_internal: State.Array<Json.key<'#property'>,propertiesData> = {
  name: 'plugins.eva.general.properties',
  getkey: ((d:propertiesData) => d.key),
  signal: signalProperties,
  fetch: fetchProperties,
  reload: reloadProperties,
  order: byPropertiesData,
};
/** Status of Registered Properties */
export const properties: State.Array<Json.key<'#property'>,propertiesData> = properties_internal;

/** The alarms are counted after being grouped by these categories */
export enum alarmCategory {
  /** Integer division by zero */
  division_by_zero = 'division_by_zero',
  /** Invalid pointer dereferencing */
  mem_access = 'mem_access',
  /** Array access out of bounds */
  index_bound = 'index_bound',
  /** Invalid shift */
  shift = 'shift',
  /** Integer overflow or downcast */
  overflow = 'overflow',
  /** Uninitialized memory read */
  initialization = 'initialization',
  /** Read of a dangling pointer */
  dangling_pointer = 'dangling_pointer',
  /** Non-finite (nan or infinite) floating-point value */
  is_nan_or_infinite = 'is_nan_or_infinite',
  /** Overflow in float to int conversion */
  float_to_int = 'float_to_int',
  /** Any other alarm */
  other = 'other',
}

/** Loose decoder for `alarmCategory` */
export const jAlarmCategory: Json.Loose<alarmCategory> =
  Json.jEnum(alarmCategory);

/** Safe decoder for `alarmCategory` */
export const jAlarmCategorySafe: Json.Safe<alarmCategory> =
  Json.jFail(Json.jEnum(alarmCategory),
    'plugins.eva.general.alarmCategory expected');

/** Natural order for `alarmCategory` */
export const byAlarmCategory: Compare.Order<alarmCategory> =
  Compare.byEnum(alarmCategory);

const alarmCategoryTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.alarmCategoryTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const alarmCategoryTags: Server.GetRequest<null,tag[]>= alarmCategoryTags_internal;

/** Statuses count. */
export type statusesEntry =
  { valid: number, unknown: number, invalid: number };

/** Loose decoder for `statusesEntry` */
export const jStatusesEntry: Json.Loose<statusesEntry> =
  Json.jObject({
    valid: Json.jFail(Json.jNumber,'Number expected'),
    unknown: Json.jFail(Json.jNumber,'Number expected'),
    invalid: Json.jFail(Json.jNumber,'Number expected'),
  });

/** Safe decoder for `statusesEntry` */
export const jStatusesEntrySafe: Json.Safe<statusesEntry> =
  Json.jFail(jStatusesEntry,'StatusesEntry expected');

/** Natural order for `statusesEntry` */
export const byStatusesEntry: Compare.Order<statusesEntry> =
  Compare.byFields
    <{ valid: number, unknown: number, invalid: number }>({
    valid: Compare.number,
    unknown: Compare.number,
    invalid: Compare.number,
  });

/** Alarm count for each alarm category. */
export type alarmEntry = { category: alarmCategory, count: number };

/** Loose decoder for `alarmEntry` */
export const jAlarmEntry: Json.Loose<alarmEntry> =
  Json.jObject({
    category: jAlarmCategorySafe,
    count: Json.jFail(Json.jNumber,'Number expected'),
  });

/** Safe decoder for `alarmEntry` */
export const jAlarmEntrySafe: Json.Safe<alarmEntry> =
  Json.jFail(jAlarmEntry,'AlarmEntry expected');

/** Natural order for `alarmEntry` */
export const byAlarmEntry: Compare.Order<alarmEntry> =
  Compare.byFields
    <{ category: alarmCategory, count: number }>({
    category: byAlarmCategory,
    count: Compare.number,
  });

/** Statistics about an Eva analysis. */
export type programStatsType =
  { progFunCoverage: { reachable: number, dead: number },
    progStmtCoverage: { reachable: number, dead: number },
    progAlarms: alarmEntry[],
    evaEvents: { errors: number, warnings: number },
    kernelEvents: { errors: number, warnings: number },
    alarmsStatuses: statusesEntry, assertionsStatuses: statusesEntry,
    precondsStatuses: statusesEntry };

/** Loose decoder for `programStatsType` */
export const jProgramStatsType: Json.Loose<programStatsType> =
  Json.jObject({
    progFunCoverage: Json.jFail(
                       Json.jObject({
                         reachable: Json.jFail(Json.jNumber,
                                      'Number expected'),
                         dead: Json.jFail(Json.jNumber,'Number expected'),
                       }),'Record expected'),
    progStmtCoverage: Json.jFail(
                        Json.jObject({
                          reachable: Json.jFail(Json.jNumber,
                                       'Number expected'),
                          dead: Json.jFail(Json.jNumber,'Number expected'),
                        }),'Record expected'),
    progAlarms: Json.jList(jAlarmEntry),
    evaEvents: Json.jFail(
                 Json.jObject({
                   errors: Json.jFail(Json.jNumber,'Number expected'),
                   warnings: Json.jFail(Json.jNumber,'Number expected'),
                 }),'Record expected'),
    kernelEvents: Json.jFail(
                    Json.jObject({
                      errors: Json.jFail(Json.jNumber,'Number expected'),
                      warnings: Json.jFail(Json.jNumber,'Number expected'),
                    }),'Record expected'),
    alarmsStatuses: jStatusesEntrySafe,
    assertionsStatuses: jStatusesEntrySafe,
    precondsStatuses: jStatusesEntrySafe,
  });

/** Safe decoder for `programStatsType` */
export const jProgramStatsTypeSafe: Json.Safe<programStatsType> =
  Json.jFail(jProgramStatsType,'ProgramStatsType expected');

/** Natural order for `programStatsType` */
export const byProgramStatsType: Compare.Order<programStatsType> =
  Compare.byFields
    <{ progFunCoverage: { reachable: number, dead: number },
       progStmtCoverage: { reachable: number, dead: number },
       progAlarms: alarmEntry[],
       evaEvents: { errors: number, warnings: number },
       kernelEvents: { errors: number, warnings: number },
       alarmsStatuses: statusesEntry, assertionsStatuses: statusesEntry,
       precondsStatuses: statusesEntry }>({
    progFunCoverage: Compare.byFields
                       <{ reachable: number, dead: number }>({
                       reachable: Compare.number,
                       dead: Compare.number,
                     }),
    progStmtCoverage: Compare.byFields
                        <{ reachable: number, dead: number }>({
                        reachable: Compare.number,
                        dead: Compare.number,
                      }),
    progAlarms: Compare.array(byAlarmEntry),
    evaEvents: Compare.byFields
                 <{ errors: number, warnings: number }>({
                 errors: Compare.number,
                 warnings: Compare.number,
               }),
    kernelEvents: Compare.byFields
                    <{ errors: number, warnings: number }>({
                    errors: Compare.number,
                    warnings: Compare.number,
                  }),
    alarmsStatuses: byStatusesEntry,
    assertionsStatuses: byStatusesEntry,
    precondsStatuses: byStatusesEntry,
  });

/** Signal for state [`programStats`](#programstats)  */
export const signalProgramStats: Server.Signal = {
  name: 'plugins.eva.general.signalProgramStats',
};

const getProgramStats_internal: Server.GetRequest<null,programStatsType> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.getProgramStats',
  input:  Json.jNull,
  output: jProgramStatsType,
  signals: [],
};
/** Getter for state [`programStats`](#programstats)  */
export const getProgramStats: Server.GetRequest<null,programStatsType>= getProgramStats_internal;

const programStats_internal: State.Value<programStatsType> = {
  name: 'plugins.eva.general.programStats',
  signal: signalProgramStats,
  getter: getProgramStats,
};
/** Statistics about the last Eva analysis for the whole program */
export const programStats: State.Value<programStatsType> = programStats_internal;

/** Data for array rows [`functionStats`](#functionstats)  */
export interface functionStatsData {
  /** Entry identifier. */
  key: Json.key<'#fundec'>;
  /** Coverage of the Eva analysis */
  coverage: { reachable: number, dead: number };
  /** Alarms raised by the Eva analysis by category */
  alarmCount: alarmEntry[];
  /** Alarms statuses emitted by the Eva analysis */
  alarmStatuses: statusesEntry;
}

/** Loose decoder for `functionStatsData` */
export const jFunctionStatsData: Json.Loose<functionStatsData> =
  Json.jObject({
    key: Json.jFail(Json.jKey<'#fundec'>('#fundec'),'#fundec expected'),
    coverage: Json.jFail(
                Json.jObject({
                  reachable: Json.jFail(Json.jNumber,'Number expected'),
                  dead: Json.jFail(Json.jNumber,'Number expected'),
                }),'Record expected'),
    alarmCount: Json.jList(jAlarmEntry),
    alarmStatuses: jStatusesEntrySafe,
  });

/** Safe decoder for `functionStatsData` */
export const jFunctionStatsDataSafe: Json.Safe<functionStatsData> =
  Json.jFail(jFunctionStatsData,'FunctionStatsData expected');

/** Natural order for `functionStatsData` */
export const byFunctionStatsData: Compare.Order<functionStatsData> =
  Compare.byFields
    <{ key: Json.key<'#fundec'>,
       coverage: { reachable: number, dead: number },
       alarmCount: alarmEntry[], alarmStatuses: statusesEntry }>({
    key: Compare.string,
    coverage: Compare.byFields
                <{ reachable: number, dead: number }>({
                reachable: Compare.number,
                dead: Compare.number,
              }),
    alarmCount: Compare.array(byAlarmEntry),
    alarmStatuses: byStatusesEntry,
  });

/** Signal for array [`functionStats`](#functionstats)  */
export const signalFunctionStats: Server.Signal = {
  name: 'plugins.eva.general.signalFunctionStats',
};

const reloadFunctionStats_internal: Server.GetRequest<null,null> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.reloadFunctionStats',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Force full reload for array [`functionStats`](#functionstats)  */
export const reloadFunctionStats: Server.GetRequest<null,null>= reloadFunctionStats_internal;

const fetchFunctionStats_internal: Server.GetRequest<
  number,
  { pending: number, updated: functionStatsData[],
    removed: Json.key<'#fundec'>[], reload: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.general.fetchFunctionStats',
  input:  Json.jNumber,
  output: Json.jObject({
            pending: Json.jFail(Json.jNumber,'Number expected'),
            updated: Json.jList(jFunctionStatsData),
            removed: Json.jList(Json.jKey<'#fundec'>('#fundec')),
            reload: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Data fetcher for array [`functionStats`](#functionstats)  */
export const fetchFunctionStats: Server.GetRequest<
  number,
  { pending: number, updated: functionStatsData[],
    removed: Json.key<'#fundec'>[], reload: boolean }
  >= fetchFunctionStats_internal;

const functionStats_internal: State.Array<
  Json.key<'#fundec'>,
  functionStatsData
  > = {
  name: 'plugins.eva.general.functionStats',
  getkey: ((d:functionStatsData) => d.key),
  signal: signalFunctionStats,
  fetch: fetchFunctionStats,
  reload: reloadFunctionStats,
  order: byFunctionStatsData,
};
/** Statistics about the last Eva analysis for each function */
export const functionStats: State.Array<
  Json.key<'#fundec'>,
  functionStatsData
  > = functionStats_internal;

/* ------------------------------------- */
