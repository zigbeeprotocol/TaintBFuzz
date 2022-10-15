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
   Dive Services
   @packageDocumentation
   @module frama-c/plugins/dive/api
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
import { byLocation } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { byMarker } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jLocation } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jLocationSafe } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jMarker } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { jMarkerSafe } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { location } from 'frama-c/kernel/api/ast';
//@ts-ignore
import { marker } from 'frama-c/kernel/api/ast';

/** Parametrization of the exploration range. */
export interface range {
  /** range for the write dependencies */
  backward?: number;
  /** range for the read dependencies */
  forward?: number;
}

/** Loose decoder for `range` */
export const jRange: Json.Loose<range> =
  Json.jObject({ backward: Json.jNumber, forward: Json.jNumber,});

/** Safe decoder for `range` */
export const jRangeSafe: Json.Safe<range> =
  Json.jFail(jRange,'Range expected');

/** Natural order for `range` */
export const byRange: Compare.Order<range> =
  Compare.byFields
    <{ backward?: number, forward?: number }>({
    backward: Compare.defined(Compare.number),
    forward: Compare.defined(Compare.number),
  });

/** Global parametrization of the exploration. */
export interface explorationWindow {
  /** how far dive will explore from root nodes ; must be a finite range */
  perception: range;
  /** range beyond which the nodes must be hidden */
  horizon: range;
}

/** Loose decoder for `explorationWindow` */
export const jExplorationWindow: Json.Loose<explorationWindow> =
  Json.jObject({ perception: jRangeSafe, horizon: jRangeSafe,});

/** Safe decoder for `explorationWindow` */
export const jExplorationWindowSafe: Json.Safe<explorationWindow> =
  Json.jFail(jExplorationWindow,'ExplorationWindow expected');

/** Natural order for `explorationWindow` */
export const byExplorationWindow: Compare.Order<explorationWindow> =
  Compare.byFields
    <{ perception: range, horizon: range }>({
    perception: byRange,
    horizon: byRange,
  });

/** A node identifier in the graph */
export type nodeId = number;

/** Loose decoder for `nodeId` */
export const jNodeId: Json.Loose<nodeId> = Json.jNumber;

/** Safe decoder for `nodeId` */
export const jNodeIdSafe: Json.Safe<nodeId> =
  Json.jFail(Json.jNumber,'Number expected');

/** Natural order for `nodeId` */
export const byNodeId: Compare.Order<nodeId> = Compare.number;

/** A callsite */
export type callsite = { fun: string, instr: number | string };

/** Loose decoder for `callsite` */
export const jCallsite: Json.Loose<callsite> =
  Json.jObject({
    fun: Json.jFail(Json.jString,'String expected'),
    instr: Json.jFail(
             Json.jUnion<number | string>( Json.jNumber, Json.jString,),
             'Union expected'),
  });

/** Safe decoder for `callsite` */
export const jCallsiteSafe: Json.Safe<callsite> =
  Json.jFail(jCallsite,'Callsite expected');

/** Natural order for `callsite` */
export const byCallsite: Compare.Order<callsite> =
  Compare.byFields
    <{ fun: string, instr: number | string }>({
    fun: Compare.string,
    instr: Compare.structural,
  });

/** The callstack context for a node */
export type callstack = callsite[];

/** Safe decoder for `callstack` */
export const jCallstackSafe: Json.Safe<callstack> =
  Json.jArray(jCallsiteSafe);

/** Loose decoder for `callstack` */
export const jCallstack: Json.Loose<callstack> = Json.jTry(jCallstackSafe);

/** Natural order for `callstack` */
export const byCallstack: Compare.Order<callstack> =
  Compare.array(byCallsite);

/** The description of a node locality */
export type nodeLocality = { file: string, callstack?: callstack };

/** Loose decoder for `nodeLocality` */
export const jNodeLocality: Json.Loose<nodeLocality> =
  Json.jObject({
    file: Json.jFail(Json.jString,'String expected'),
    callstack: jCallstack,
  });

/** Safe decoder for `nodeLocality` */
export const jNodeLocalitySafe: Json.Safe<nodeLocality> =
  Json.jFail(jNodeLocality,'NodeLocality expected');

/** Natural order for `nodeLocality` */
export const byNodeLocality: Compare.Order<nodeLocality> =
  Compare.byFields
    <{ file: string, callstack?: callstack }>({
    file: Compare.string,
    callstack: Compare.defined(byCallstack),
  });

/** A graph node */
export type node =
  { id: nodeId, label: string, kind: string, locality: nodeLocality,
    is_root: boolean, backward_explored: string, forward_explored: string,
    writes: location[], values?: string, range: number | string,
    type?: string };

/** Loose decoder for `node` */
export const jNode: Json.Loose<node> =
  Json.jObject({
    id: jNodeIdSafe,
    label: Json.jFail(Json.jString,'String expected'),
    kind: Json.jFail(Json.jString,'String expected'),
    locality: jNodeLocalitySafe,
    is_root: Json.jFail(Json.jBoolean,'Boolean expected'),
    backward_explored: Json.jFail(Json.jString,'String expected'),
    forward_explored: Json.jFail(Json.jString,'String expected'),
    writes: Json.jArray(jLocationSafe),
    values: Json.jString,
    range: Json.jFail(
             Json.jUnion<number | string>( Json.jNumber, Json.jString,),
             'Union expected'),
    type: Json.jString,
  });

/** Safe decoder for `node` */
export const jNodeSafe: Json.Safe<node> = Json.jFail(jNode,'Node expected');

/** Natural order for `node` */
export const byNode: Compare.Order<node> =
  Compare.byFields
    <{ id: nodeId, label: string, kind: string, locality: nodeLocality,
       is_root: boolean, backward_explored: string, forward_explored: string,
       writes: location[], values?: string, range: number | string,
       type?: string }>({
    id: byNodeId,
    label: Compare.string,
    kind: Compare.string,
    locality: byNodeLocality,
    is_root: Compare.boolean,
    backward_explored: Compare.string,
    forward_explored: Compare.string,
    writes: Compare.array(byLocation),
    values: Compare.defined(Compare.string),
    range: Compare.structural,
    type: Compare.defined(Compare.string),
  });

/** The dependency between two nodes */
export type dependency =
  { id: number, src: nodeId, dst: nodeId, kind: string, origins: location[] };

/** Loose decoder for `dependency` */
export const jDependency: Json.Loose<dependency> =
  Json.jObject({
    id: Json.jFail(Json.jNumber,'Number expected'),
    src: jNodeIdSafe,
    dst: jNodeIdSafe,
    kind: Json.jFail(Json.jString,'String expected'),
    origins: Json.jArray(jLocationSafe),
  });

/** Safe decoder for `dependency` */
export const jDependencySafe: Json.Safe<dependency> =
  Json.jFail(jDependency,'Dependency expected');

/** Natural order for `dependency` */
export const byDependency: Compare.Order<dependency> =
  Compare.byFields
    <{ id: number, src: nodeId, dst: nodeId, kind: string,
       origins: location[] }>({
    id: Compare.number,
    src: byNodeId,
    dst: byNodeId,
    kind: Compare.string,
    origins: Compare.array(byLocation),
  });

/** The whole graph being built */
export type graphData = { nodes: node[], deps: dependency[] };

/** Loose decoder for `graphData` */
export const jGraphData: Json.Loose<graphData> =
  Json.jObject({
    nodes: Json.jArray(jNodeSafe),
    deps: Json.jArray(jDependencySafe),
  });

/** Safe decoder for `graphData` */
export const jGraphDataSafe: Json.Safe<graphData> =
  Json.jFail(jGraphData,'GraphData expected');

/** Natural order for `graphData` */
export const byGraphData: Compare.Order<graphData> =
  Compare.byFields
    <{ nodes: node[], deps: dependency[] }>({
    nodes: Compare.array(byNode),
    deps: Compare.array(byDependency),
  });

/** Graph differences from the last action. */
export type diffData =
  { root?: nodeId, add: { nodes: node[], deps: dependency[] }, sub: nodeId[]
    };

/** Loose decoder for `diffData` */
export const jDiffData: Json.Loose<diffData> =
  Json.jObject({
    root: jNodeId,
    add: Json.jFail(
           Json.jObject({
             nodes: Json.jArray(jNodeSafe),
             deps: Json.jArray(jDependencySafe),
           }),'Record expected'),
    sub: Json.jArray(jNodeIdSafe),
  });

/** Safe decoder for `diffData` */
export const jDiffDataSafe: Json.Safe<diffData> =
  Json.jFail(jDiffData,'DiffData expected');

/** Natural order for `diffData` */
export const byDiffData: Compare.Order<diffData> =
  Compare.byFields
    <{ root?: nodeId, add: { nodes: node[], deps: dependency[] },
       sub: nodeId[] }>({
    root: Compare.defined(byNodeId),
    add: Compare.byFields
           <{ nodes: node[], deps: dependency[] }>({
           nodes: Compare.array(byNode),
           deps: Compare.array(byDependency),
         }),
    sub: Compare.array(byNodeId),
  });

const window_internal: Server.SetRequest<explorationWindow,null> = {
  kind: Server.RqKind.SET,
  name:   'plugins.dive.window',
  input:  jExplorationWindow,
  output: Json.jNull,
  signals: [],
};
/** Set the exploration window */
export const window: Server.SetRequest<explorationWindow,null>= window_internal;

const graph_internal: Server.GetRequest<null,graphData> = {
  kind: Server.RqKind.GET,
  name:   'plugins.dive.graph',
  input:  Json.jNull,
  output: jGraphData,
  signals: [],
};
/** Retrieve the whole graph */
export const graph: Server.GetRequest<null,graphData>= graph_internal;

const clear_internal: Server.ExecRequest<null,null> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.dive.clear',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Erase the graph and start over with an empty one */
export const clear: Server.ExecRequest<null,null>= clear_internal;

const add_internal: Server.ExecRequest<marker,diffData> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.dive.add',
  input:  jMarker,
  output: jDiffData,
  signals: [],
};
/** Add a node to the graph */
export const add: Server.ExecRequest<marker,diffData>= add_internal;

const explore_internal: Server.ExecRequest<nodeId,diffData> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.dive.explore',
  input:  jNodeId,
  output: jDiffData,
  signals: [],
};
/** Explore the graph starting from an existing vertex */
export const explore: Server.ExecRequest<nodeId,diffData>= explore_internal;

const show_internal: Server.ExecRequest<nodeId,diffData> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.dive.show',
  input:  jNodeId,
  output: jDiffData,
  signals: [],
};
/** Show the dependencies of an existing vertex */
export const show: Server.ExecRequest<nodeId,diffData>= show_internal;

const hide_internal: Server.ExecRequest<nodeId,diffData> = {
  kind: Server.RqKind.EXEC,
  name:   'plugins.dive.hide',
  input:  jNodeId,
  output: jDiffData,
  signals: [],
};
/** Hide the dependencies of an existing vertex */
export const hide: Server.ExecRequest<nodeId,diffData>= hide_internal;

/* ------------------------------------- */
