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
   Ast Services
   @packageDocumentation
   @module frama-c/kernel/api/ast
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
import { byTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { byText } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTagSafe } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jText } from 'frama-c/kernel/api/data';
//@ts-ignore
import { jTextSafe } from 'frama-c/kernel/api/data';
//@ts-ignore
import { tag } from 'frama-c/kernel/api/data';
//@ts-ignore
import { text } from 'frama-c/kernel/api/data';

const compute_internal: Server.ExecRequest<null,null> = {
  kind: Server.RqKind.EXEC,
  name:   'kernel.ast.compute',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Ensures that AST is computed */
export const compute: Server.ExecRequest<null,null>= compute_internal;

/** Emitted when the AST has been changed */
export const changed: Server.Signal = {
  name: 'kernel.ast.changed',
};

/** Source file positions. */
export type source =
  { dir: string, base: string, file: string, line: number };

/** Loose decoder for `source` */
export const jSource: Json.Loose<source> =
  Json.jObject({
    dir: Json.jFail(Json.jString,'String expected'),
    base: Json.jFail(Json.jString,'String expected'),
    file: Json.jFail(Json.jString,'String expected'),
    line: Json.jFail(Json.jNumber,'Number expected'),
  });

/** Safe decoder for `source` */
export const jSourceSafe: Json.Safe<source> =
  Json.jFail(jSource,'Source expected');

/** Natural order for `source` */
export const bySource: Compare.Order<source> =
  Compare.byFields
    <{ dir: string, base: string, file: string, line: number }>({
    dir: Compare.string,
    base: Compare.string,
    file: Compare.string,
    line: Compare.number,
  });

/** Marker kind */
export enum markerKind {
  /** Expression */
  expression = 'expression',
  /** Lvalue */
  lvalue = 'lvalue',
  /** Declaration */
  declaration = 'declaration',
  /** Statement */
  statement = 'statement',
  /** Global */
  global = 'global',
  /** Term */
  term = 'term',
  /** Property */
  property = 'property',
}

/** Loose decoder for `markerKind` */
export const jMarkerKind: Json.Loose<markerKind> = Json.jEnum(markerKind);

/** Safe decoder for `markerKind` */
export const jMarkerKindSafe: Json.Safe<markerKind> =
  Json.jFail(Json.jEnum(markerKind),'kernel.ast.markerKind expected');

/** Natural order for `markerKind` */
export const byMarkerKind: Compare.Order<markerKind> =
  Compare.byEnum(markerKind);

const markerKindTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.markerKindTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const markerKindTags: Server.GetRequest<null,tag[]>= markerKindTags_internal;

/** Marker variable */
export enum markerVar {
  /** None */
  none = 'none',
  /** Variable */
  variable = 'variable',
  /** Function */
  function = 'function',
}

/** Loose decoder for `markerVar` */
export const jMarkerVar: Json.Loose<markerVar> = Json.jEnum(markerVar);

/** Safe decoder for `markerVar` */
export const jMarkerVarSafe: Json.Safe<markerVar> =
  Json.jFail(Json.jEnum(markerVar),'kernel.ast.markerVar expected');

/** Natural order for `markerVar` */
export const byMarkerVar: Compare.Order<markerVar> =
  Compare.byEnum(markerVar);

const markerVarTags_internal: Server.GetRequest<null,tag[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.markerVarTags',
  input:  Json.jNull,
  output: Json.jList(jTag),
  signals: [],
};
/** Registered tags for the above type. */
export const markerVarTags: Server.GetRequest<null,tag[]>= markerVarTags_internal;

/** Data for array rows [`markerInfo`](#markerinfo)  */
export interface markerInfoData {
  /** Entry identifier. */
  key: string;
  /** Marker kind */
  kind: markerKind;
  /** Marker variable */
  var: markerVar;
  /** Marker short name */
  name: string;
  /** Marker declaration or description */
  descr: string;
  /** Source location */
  sloc: source;
}

/** Loose decoder for `markerInfoData` */
export const jMarkerInfoData: Json.Loose<markerInfoData> =
  Json.jObject({
    key: Json.jFail(Json.jString,'String expected'),
    kind: jMarkerKindSafe,
    var: jMarkerVarSafe,
    name: Json.jFail(Json.jString,'String expected'),
    descr: Json.jFail(Json.jString,'String expected'),
    sloc: jSourceSafe,
  });

/** Safe decoder for `markerInfoData` */
export const jMarkerInfoDataSafe: Json.Safe<markerInfoData> =
  Json.jFail(jMarkerInfoData,'MarkerInfoData expected');

/** Natural order for `markerInfoData` */
export const byMarkerInfoData: Compare.Order<markerInfoData> =
  Compare.byFields
    <{ key: string, kind: markerKind, var: markerVar, name: string,
       descr: string, sloc: source }>({
    key: Compare.string,
    kind: byMarkerKind,
    var: byMarkerVar,
    name: Compare.alpha,
    descr: Compare.string,
    sloc: bySource,
  });

/** Signal for array [`markerInfo`](#markerinfo)  */
export const signalMarkerInfo: Server.Signal = {
  name: 'kernel.ast.signalMarkerInfo',
};

const reloadMarkerInfo_internal: Server.GetRequest<null,null> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.reloadMarkerInfo',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Force full reload for array [`markerInfo`](#markerinfo)  */
export const reloadMarkerInfo: Server.GetRequest<null,null>= reloadMarkerInfo_internal;

const fetchMarkerInfo_internal: Server.GetRequest<
  number,
  { pending: number, updated: markerInfoData[], removed: string[],
    reload: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.fetchMarkerInfo',
  input:  Json.jNumber,
  output: Json.jObject({
            pending: Json.jFail(Json.jNumber,'Number expected'),
            updated: Json.jList(jMarkerInfoData),
            removed: Json.jList(Json.jString),
            reload: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Data fetcher for array [`markerInfo`](#markerinfo)  */
export const fetchMarkerInfo: Server.GetRequest<
  number,
  { pending: number, updated: markerInfoData[], removed: string[],
    reload: boolean }
  >= fetchMarkerInfo_internal;

const markerInfo_internal: State.Array<string,markerInfoData> = {
  name: 'kernel.ast.markerInfo',
  getkey: ((d:markerInfoData) => d.key),
  signal: signalMarkerInfo,
  fetch: fetchMarkerInfo,
  reload: reloadMarkerInfo,
  order: byMarkerInfoData,
};
/** Marker information */
export const markerInfo: State.Array<string,markerInfoData> = markerInfo_internal;

/** Localizable AST markers */
export type marker =
  Json.key<'#stmt'> | Json.key<'#decl'> | Json.key<'#lval'> |
  Json.key<'#expr'> | Json.key<'#term'> | Json.key<'#global'> |
  Json.key<'#property'>;

/** Loose decoder for `marker` */
export const jMarker: Json.Loose<marker> =
  Json.jUnion<Json.key<'#stmt'> | Json.key<'#decl'> | Json.key<'#lval'> |
              Json.key<'#expr'> | Json.key<'#term'> | Json.key<'#global'> |
              Json.key<'#property'>>(
    Json.jKey<'#stmt'>('#stmt'),
    Json.jKey<'#decl'>('#decl'),
    Json.jKey<'#lval'>('#lval'),
    Json.jKey<'#expr'>('#expr'),
    Json.jKey<'#term'>('#term'),
    Json.jKey<'#global'>('#global'),
    Json.jKey<'#property'>('#property'),
  );

/** Safe decoder for `marker` */
export const jMarkerSafe: Json.Safe<marker> =
  Json.jFail(jMarker,'Marker expected');

/** Natural order for `marker` */
export const byMarker: Compare.Order<marker> = Compare.structural;

/** Location: function and marker */
export interface location {
  /** Function */
  fct: Json.key<'#fct'>;
  /** Marker */
  marker: marker;
}

/** Loose decoder for `location` */
export const jLocation: Json.Loose<location> =
  Json.jObject({
    fct: Json.jFail(Json.jKey<'#fct'>('#fct'),'#fct expected'),
    marker: jMarkerSafe,
  });

/** Safe decoder for `location` */
export const jLocationSafe: Json.Safe<location> =
  Json.jFail(jLocation,'Location expected');

/** Natural order for `location` */
export const byLocation: Compare.Order<location> =
  Compare.byFields
    <{ fct: Json.key<'#fct'>, marker: marker }>({
    fct: Compare.string,
    marker: byMarker,
  });

const getMainFunction_internal: Server.GetRequest<
  null,
  Json.key<'#fct'> |
  undefined
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.getMainFunction',
  input:  Json.jNull,
  output: Json.jKey<'#fct'>('#fct'),
  signals: [],
};
/** Get the current 'main' function. */
export const getMainFunction: Server.GetRequest<
  null,
  Json.key<'#fct'> |
  undefined
  >= getMainFunction_internal;

const getFunctions_internal: Server.GetRequest<null,Json.key<'#fct'>[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.getFunctions',
  input:  Json.jNull,
  output: Json.jList(Json.jKey<'#fct'>('#fct')),
  signals: [],
};
/** Collect all functions in the AST */
export const getFunctions: Server.GetRequest<null,Json.key<'#fct'>[]>= getFunctions_internal;

const printFunction_internal: Server.GetRequest<Json.key<'#fct'>,text> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.printFunction',
  input:  Json.jKey<'#fct'>('#fct'),
  output: jText,
  signals: [],
};
/** Print the AST of a function */
export const printFunction: Server.GetRequest<Json.key<'#fct'>,text>= printFunction_internal;

/** Data for array rows [`functions`](#functions)  */
export interface functionsData {
  /** Entry identifier. */
  key: Json.key<'#functions'>;
  /** Name */
  name: string;
  /** Signature */
  signature: string;
  /** Is the function the main entry point */
  main?: boolean;
  /** Is the function defined? */
  defined?: boolean;
  /** Is the function from the Frama-C stdlib? */
  stdlib?: boolean;
  /** Is the function a Frama-C builtin? */
  builtin?: boolean;
  /** Has the function been analyzed by Eva */
  eva_analyzed?: boolean;
  /** Source location */
  sloc: source;
}

/** Loose decoder for `functionsData` */
export const jFunctionsData: Json.Loose<functionsData> =
  Json.jObject({
    key: Json.jFail(Json.jKey<'#functions'>('#functions'),
           '#functions expected'),
    name: Json.jFail(Json.jString,'String expected'),
    signature: Json.jFail(Json.jString,'String expected'),
    main: Json.jBoolean,
    defined: Json.jBoolean,
    stdlib: Json.jBoolean,
    builtin: Json.jBoolean,
    eva_analyzed: Json.jBoolean,
    sloc: jSourceSafe,
  });

/** Safe decoder for `functionsData` */
export const jFunctionsDataSafe: Json.Safe<functionsData> =
  Json.jFail(jFunctionsData,'FunctionsData expected');

/** Natural order for `functionsData` */
export const byFunctionsData: Compare.Order<functionsData> =
  Compare.byFields
    <{ key: Json.key<'#functions'>, name: string, signature: string,
       main?: boolean, defined?: boolean, stdlib?: boolean,
       builtin?: boolean, eva_analyzed?: boolean, sloc: source }>({
    key: Compare.string,
    name: Compare.alpha,
    signature: Compare.string,
    main: Compare.defined(Compare.boolean),
    defined: Compare.defined(Compare.boolean),
    stdlib: Compare.defined(Compare.boolean),
    builtin: Compare.defined(Compare.boolean),
    eva_analyzed: Compare.defined(Compare.boolean),
    sloc: bySource,
  });

/** Signal for array [`functions`](#functions)  */
export const signalFunctions: Server.Signal = {
  name: 'kernel.ast.signalFunctions',
};

const reloadFunctions_internal: Server.GetRequest<null,null> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.reloadFunctions',
  input:  Json.jNull,
  output: Json.jNull,
  signals: [],
};
/** Force full reload for array [`functions`](#functions)  */
export const reloadFunctions: Server.GetRequest<null,null>= reloadFunctions_internal;

const fetchFunctions_internal: Server.GetRequest<
  number,
  { pending: number, updated: functionsData[],
    removed: Json.key<'#functions'>[], reload: boolean }
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.fetchFunctions',
  input:  Json.jNumber,
  output: Json.jObject({
            pending: Json.jFail(Json.jNumber,'Number expected'),
            updated: Json.jList(jFunctionsData),
            removed: Json.jList(Json.jKey<'#functions'>('#functions')),
            reload: Json.jFail(Json.jBoolean,'Boolean expected'),
          }),
  signals: [],
};
/** Data fetcher for array [`functions`](#functions)  */
export const fetchFunctions: Server.GetRequest<
  number,
  { pending: number, updated: functionsData[],
    removed: Json.key<'#functions'>[], reload: boolean }
  >= fetchFunctions_internal;

const functions_internal: State.Array<Json.key<'#functions'>,functionsData> = {
  name: 'kernel.ast.functions',
  getkey: ((d:functionsData) => d.key),
  signal: signalFunctions,
  fetch: fetchFunctions,
  reload: reloadFunctions,
  order: byFunctionsData,
};
/** AST Functions */
export const functions: State.Array<Json.key<'#functions'>,functionsData> = functions_internal;

/** Updated AST information */
export const getInformationUpdate: Server.Signal = {
  name: 'kernel.ast.getInformationUpdate',
};

const getInformation_internal: Server.GetRequest<
  marker |
  undefined,
  { id: string, label: string, title: string, descr: text }[]
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.getInformation',
  input:  jMarker,
  output: Json.jList(
            Json.jObject({
              id: Json.jFail(Json.jString,'String expected'),
              label: Json.jFail(Json.jString,'String expected'),
              title: Json.jFail(Json.jString,'String expected'),
              descr: jTextSafe,
            })),
  signals: [ { name: 'kernel.ast.getInformationUpdate' } ],
};
/** Get available information about markers. When no marker is given, returns all kinds of information (with empty `descr` field). */
export const getInformation: Server.GetRequest<
  marker |
  undefined,
  { id: string, label: string, title: string, descr: text }[]
  >= getInformation_internal;

const getMarkerAt_internal: Server.GetRequest<
  [ string, number, number ],
  [ Json.key<'#fct'> | undefined, marker | undefined ]
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.getMarkerAt',
  input:  Json.jTry(
            Json.jTriple(
              Json.jFail(Json.jString,'String expected'),
              Json.jFail(Json.jNumber,'Number expected'),
              Json.jFail(Json.jNumber,'Number expected'),
            )),
  output: Json.jTry(Json.jPair( Json.jKey<'#fct'>('#fct'), jMarker,)),
  signals: [],
};
/** Returns the marker and function at a source file position, if any. Input: file path, line and column. */
export const getMarkerAt: Server.GetRequest<
  [ string, number, number ],
  [ Json.key<'#fct'> | undefined, marker | undefined ]
  >= getMarkerAt_internal;

const getFiles_internal: Server.GetRequest<null,string[]> = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.getFiles',
  input:  Json.jNull,
  output: Json.jList(Json.jString),
  signals: [],
};
/** Get the currently analyzed source file names */
export const getFiles: Server.GetRequest<null,string[]>= getFiles_internal;

const setFiles_internal: Server.SetRequest<string[],null> = {
  kind: Server.RqKind.SET,
  name:   'kernel.ast.setFiles',
  input:  Json.jList(Json.jString),
  output: Json.jNull,
  signals: [],
};
/** Set the source file names to analyze. */
export const setFiles: Server.SetRequest<string[],null>= setFiles_internal;

/** <markerFromTerm> input */
export interface markerFromTermInput {
  /** The statement at which we will build the marker. */
  atStmt: marker;
  /** The ACSL term. */
  term: string;
}

/** Loose decoder for `markerFromTermInput` */
export const jMarkerFromTermInput: Json.Loose<markerFromTermInput> =
  Json.jObject({
    atStmt: jMarkerSafe,
    term: Json.jFail(Json.jString,'String expected'),
  });

/** Safe decoder for `markerFromTermInput` */
export const jMarkerFromTermInputSafe: Json.Safe<markerFromTermInput> =
  Json.jFail(jMarkerFromTermInput,'MarkerFromTermInput expected');

/** Natural order for `markerFromTermInput` */
export const byMarkerFromTermInput: Compare.Order<markerFromTermInput> =
  Compare.byFields
    <{ atStmt: marker, term: string }>({
    atStmt: byMarker,
    term: Compare.string,
  });

const markerFromTerm_internal: Server.GetRequest<
  markerFromTermInput,
  marker |
  undefined
  > = {
  kind: Server.RqKind.GET,
  name:   'kernel.ast.markerFromTerm',
  input:  jMarkerFromTermInput,
  output: jMarker,
  signals: [],
};
/** Build a marker from an ACSL term. */
export const markerFromTerm: Server.GetRequest<
  markerFromTermInput,
  marker |
  undefined
  >= markerFromTerm_internal;

/* ------------------------------------- */
