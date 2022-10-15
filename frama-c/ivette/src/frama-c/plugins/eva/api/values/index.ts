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
   Eva Values
   @packageDocumentation
   @module frama-c/plugins/eva/api/values
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

/** Emitted when EVA results has changed */
export const changed: Server.Signal = {
  name: 'plugins.eva.values.changed',
};

export type callstack = Json.index<'#eva-callstack-id'>;

/** Loose decoder for `callstack` */
export const jCallstack: Json.Loose<callstack> =
  Json.jIndex<'#eva-callstack-id'>('#eva-callstack-id');

/** Safe decoder for `callstack` */
export const jCallstackSafe: Json.Safe<callstack> =
  Json.jFail(Json.jIndex<'#eva-callstack-id'>('#eva-callstack-id'),
    '#eva-callstack-id expected');

/** Natural order for `callstack` */
export const byCallstack: Compare.Order<callstack> = Compare.number;

const getCallstacks_internal: Server.GetRequest<marker[],callstack[]> = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.values.getCallstacks',
  input:  Json.jList(jMarker),
  output: Json.jList(jCallstack),
  signals: [],
};
/** Callstacks for markers */
export const getCallstacks: Server.GetRequest<marker[],callstack[]>= getCallstacks_internal;

const getCallstackInfo_internal: Server.GetRequest<
  callstack,
  { callee: Json.key<'#fct'>, caller?: Json.key<'#fct'>,
    stmt?: Json.key<'#stmt'>, rank?: number }[]
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.values.getCallstackInfo',
  input:  jCallstack,
  output: Json.jList(
            Json.jObject({
              callee: Json.jFail(Json.jKey<'#fct'>('#fct'),'#fct expected'),
              caller: Json.jKey<'#fct'>('#fct'),
              stmt: Json.jKey<'#stmt'>('#stmt'),
              rank: Json.jNumber,
            })),
  signals: [],
};
/** Callstack Description */
export const getCallstackInfo: Server.GetRequest<
  callstack,
  { callee: Json.key<'#fct'>, caller?: Json.key<'#fct'>,
    stmt?: Json.key<'#stmt'>, rank?: number }[]
  >= getCallstackInfo_internal;

const getStmtInfo_internal: Server.GetRequest<
  Json.key<'#stmt'>,
  { rank: number, fct: Json.key<'#fct'> }
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.values.getStmtInfo',
  input:  Json.jKey<'#stmt'>('#stmt'),
  output: Json.jObject({
            rank: Json.jFail(Json.jNumber,'Number expected'),
            fct: Json.jFail(Json.jKey<'#fct'>('#fct'),'#fct expected'),
          }),
  signals: [],
};
/** Stmt Information */
export const getStmtInfo: Server.GetRequest<
  Json.key<'#stmt'>,
  { rank: number, fct: Json.key<'#fct'> }
  >= getStmtInfo_internal;

const getProbeInfo_internal: Server.GetRequest<
  marker,
  { condition: boolean, effects: boolean, rank: number,
    stmt?: Json.key<'#stmt'>, code?: string, evaluable: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.values.getProbeInfo',
  input:  jMarker,
  output: Json.jObject({
            condition: Json.jFail(Json.jBoolean,'Boolean expected'),
            effects: Json.jFail(Json.jBoolean,'Boolean expected'),
            rank: Json.jFail(Json.jNumber,'Number expected'),
            stmt: Json.jKey<'#stmt'>('#stmt'),
            code: Json.jString,
            evaluable: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Probe informations */
export const getProbeInfo: Server.GetRequest<
  marker,
  { condition: boolean, effects: boolean, rank: number,
    stmt?: Json.key<'#stmt'>, code?: string, evaluable: boolean }
  >= getProbeInfo_internal;

/** Evaluation of an expression or lvalue */
export interface evaluation {
  /** Textual representation of the value */
  value: string;
  /** Alarms raised by the evaluation */
  alarms: [ "True" | "False" | "Unknown", string ][];
  /** List of variables pointed by the value */
  pointedVars: [ string, marker ][];
}

/** Loose decoder for `evaluation` */
export const jEvaluation: Json.Loose<evaluation> =
  Json.jObject({
    value: Json.jFail(Json.jString,'String expected'),
    alarms: Json.jList(
              Json.jTry(
                Json.jPair(
                  Json.jFail(
                    Json.jUnion<"True" | "False" | "Unknown">(
                      Json.jTag("True"),
                      Json.jTag("False"),
                      Json.jTag("Unknown"),
                    ),'Union expected'),
                  Json.jFail(Json.jString,'String expected'),
                ))),
    pointedVars: Json.jList(
                   Json.jTry(
                     Json.jPair(
                       Json.jFail(Json.jString,'String expected'),
                       jMarkerSafe,
                     ))),
  });

/** Safe decoder for `evaluation` */
export const jEvaluationSafe: Json.Safe<evaluation> =
  Json.jFail(jEvaluation,'Evaluation expected');

/** Natural order for `evaluation` */
export const byEvaluation: Compare.Order<evaluation> =
  Compare.byFields
    <{ value: string, alarms: [ "True" | "False" | "Unknown", string ][],
       pointedVars: [ string, marker ][] }>({
    value: Compare.string,
    alarms: Compare.array(Compare.pair(Compare.structural,Compare.string,)),
    pointedVars: Compare.array(Compare.pair(Compare.string,byMarker,)),
  });

const getValues_internal: Server.GetRequest<
  { callstack?: callstack, target: marker },
  { vElse?: evaluation, vThen?: evaluation, vAfter?: evaluation,
    vBefore?: evaluation }
  > = {
  kind: Server.RqKind.GET,
  name:   'plugins.eva.values.getValues',
  input:  Json.jObject({ callstack: jCallstack, target: jMarkerSafe,}),
  output: Json.jObject({
            vElse: jEvaluation,
            vThen: jEvaluation,
            vAfter: jEvaluation,
            vBefore: jEvaluation,
          }),
  signals: [],
};
/** Abstract values for the given marker */
export const getValues: Server.GetRequest<
  { callstack?: callstack, target: marker },
  { vElse?: evaluation, vThen?: evaluation, vAfter?: evaluation,
    vBefore?: evaluation }
  >= getValues_internal;

/* ------------------------------------- */
