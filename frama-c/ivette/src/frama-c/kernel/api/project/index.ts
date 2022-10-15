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
   Project Management
   @packageDocumentation
   @module frama-c/kernel/api/project
*/

//@ts-ignore
import * as Json from 'dome/data/json';
//@ts-ignore
import * as Compare from 'dome/data/compare';
//@ts-ignore
import * as Server from 'frama-c/server';
//@ts-ignore
import * as State from 'frama-c/states';


/** Project informations */
export type projectInfo =
  { id: Json.key<'#project'>, name: string, current: boolean };

/** Loose decoder for `projectInfo` */
export const jProjectInfo: Json.Loose<projectInfo> =
  Json.jObject({
    id: Json.jFail(Json.jKey<'#project'>('#project'),'#project expected'),
    name: Json.jFail(Json.jString,'String expected'),
    current: Json.jFail(Json.jBoolean,'Boolean expected'),
  });

/** Safe decoder for `projectInfo` */
export const jProjectInfoSafe: Json.Safe<projectInfo> =
  Json.jFail(jProjectInfo,'ProjectInfo expected');

/** Natural order for `projectInfo` */
export const byProjectInfo: Compare.Order<projectInfo> =
  Compare.byFields
    <{ id: Json.key<'#project'>, name: string, current: boolean }>({
    id: Compare.string,
    name: Compare.alpha,
    current: Compare.boolean,
  });

/** Request to be executed on the specified project. */
export type projectRequest =
  { project: Json.key<'#project'>, request: string, data: Json.json };

/** Loose decoder for `projectRequest` */
export const jProjectRequest: Json.Loose<projectRequest> =
  Json.jObject({
    project: Json.jFail(Json.jKey<'#project'>('#project'),
               '#project expected'),
    request: Json.jFail(Json.jString,'String expected'),
    data: Json.jAny,
  });

/** Safe decoder for `projectRequest` */
export const jProjectRequestSafe: Json.Safe<projectRequest> =
  Json.jFail(jProjectRequest,'ProjectRequest expected');

/** Natural order for `projectRequest` */
export const byProjectRequest: Compare.Order<projectRequest> =
  Compare.byFields
    <{ project: Json.key<'#project'>, request: string, data: Json.json }>({
    project: Compare.string,
    request: Compare.string,
    data: Compare.structural,
  });

const getCurrent_internal: Server.GetRequest<null,projectInfo> = {
  kind: Server.RqKind.GET,
  name:   'kernel.project.getCurrent',
  input:  Json.jNull,
  output: jProjectInfo,
  signals: [],
};
/** Returns the current project */
export const getCurrent: Server.GetRequest<null,projectInfo>= getCurrent_internal;

const setCurrent_internal: Server.SetRequest<Json.key<'#project'>,null> = {
  kind: Server.RqKind.SET,
  name:   'kernel.project.setCurrent',
  input:  Json.jKey<'#project'>('#project'),
  output: Json.jNull,
  signals: [],
};
/** Switches the current project */
export const setCurrent: Server.SetRequest<Json.key<'#project'>,null>= setCurrent_internal;

const getList_internal: Server.GetRequest<null,projectInfo[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.project.getList',
  input:  Json.jNull,
  output: Json.jList(jProjectInfo),
  signals: [],
};
/** Returns the list of all projects */
export const getList: Server.GetRequest<null,projectInfo[]>= getList_internal;

const getOn_internal: Server.GetRequest<projectRequest,Json.json> = {
  kind: Server.RqKind.GET,
  name:   'kernel.project.getOn',
  input:  jProjectRequest,
  output: Json.jAny,
  signals: [],
};
/** Execute a GET request within the given project */
export const getOn: Server.GetRequest<projectRequest,Json.json>= getOn_internal;

const setOn_internal: Server.SetRequest<projectRequest,Json.json> = {
  kind: Server.RqKind.SET,
  name:   'kernel.project.setOn',
  input:  jProjectRequest,
  output: Json.jAny,
  signals: [],
};
/** Execute a SET request within the given project */
export const setOn: Server.SetRequest<projectRequest,Json.json>= setOn_internal;

const execOn_internal: Server.ExecRequest<projectRequest,Json.json> = {
  kind: Server.RqKind.EXEC,
  name:   'kernel.project.execOn',
  input:  jProjectRequest,
  output: Json.jAny,
  signals: [],
};
/** Execute an EXEC request within the given project */
export const execOn: Server.ExecRequest<projectRequest,Json.json>= execOn_internal;

const create_internal: Server.SetRequest<string,projectInfo> = {
  kind: Server.RqKind.SET,
  name:   'kernel.project.create',
  input:  Json.jString,
  output: jProjectInfo,
  signals: [],
};
/** Create a new project */
export const create: Server.SetRequest<string,projectInfo>= create_internal;

/* ------------------------------------- */
