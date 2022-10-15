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
   Pivot Table Services
   @packageDocumentation
   @module frama-c/plugins/pivot/api/general
*/

//@ts-ignore
import * as Json from 'dome/data/json';
//@ts-ignore
import * as Compare from 'dome/data/compare';
//@ts-ignore
import * as Server from 'frama-c/server';
//@ts-ignore
import * as State from 'frama-c/states';


/** State of the pivot table source data. */
export type tableStateType = string[][];

/** Safe decoder for `tableStateType` */
export const jTableStateTypeSafe: Json.Safe<tableStateType> =
  Json.jArray(Json.jArray(Json.jFail(Json.jString,'String expected')));

/** Loose decoder for `tableStateType` */
export const jTableStateType: Json.Loose<tableStateType> =
  Json.jTry(jTableStateTypeSafe);

/** Natural order for `tableStateType` */
export const byTableStateType: Compare.Order<tableStateType> =
  Compare.array(Compare.array(Compare.string));

/** Signal for state [`pivotState`](#pivotstate)  */
export const signalPivotState: Server.Signal = {
  name: 'plugins.pivot.general.signalPivotState',
};

const getPivotState_internal: Server.GetRequest<null,tableStateType> = {
  kind: Server.RqKind.GET,
  name:   'plugins.pivot.general.getPivotState',
  input:  Json.jNull,
  output: jTableStateType,
  signals: [],
};
/** Getter for state [`pivotState`](#pivotstate)  */
export const getPivotState: Server.GetRequest<null,tableStateType>= getPivotState_internal;

const pivotState_internal: State.Value<tableStateType> = {
  name: 'plugins.pivot.general.pivotState',
  signal: signalPivotState,
  getter: getPivotState,
};
/** State of the pivot table source data. */
export const pivotState: State.Value<tableStateType> = pivotState_internal;

const compute_internal: Server.ExecRequest<null,null> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.pivot.general.compute',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Computes the pivot table. */
export const compute: Server.ExecRequest<null,null>= compute_internal;

/* ------------------------------------- */
