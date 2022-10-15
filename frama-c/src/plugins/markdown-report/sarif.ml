(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

(** OCaml representation for the sarif 2.1 schema. *)

(* ppx_deriving_yojson generates parser and printer that are recursive
   by default: we must thus silence spurious let rec warning (39). *)
[@@@ warning "-39"]

type 'a dict = (string * 'a) list

module type Json_type = sig
  type t
  val of_yojson: Yojson.Safe.t -> t Ppx_deriving_yojson_runtime.error_or
  val to_yojson: t -> Yojson.Safe.t
end

module type Json_default = sig
  include Json_type
  val default: t
end

module Json_string: Json_type with type t = string =
struct
  type t = string
  let of_yojson = function
    | `String s -> Ok s
    | _ -> Error "string"
  let to_yojson s = `String s
end

module Json_dictionary(J: Json_type):
  Json_type with type t = (string * J.t) list =
struct
  type t = (string * J.t) list
  let bind x f = match x with Ok x -> f x | Error e -> Error e
  let bindret x f = bind x (fun x -> Ok (f x))
  let bind_pair f (s, x) = bindret (f x) (fun x -> (s, x))
  let one_step f acc x =
    bind acc (fun acc -> (bindret (f x) (fun x -> (x :: acc))))
  let bind_list l f =
    bindret (List.fold_left (one_step (bind_pair f)) (Ok []) l) List.rev
  let of_yojson = function
    | `Assoc l ->
      (match bind_list l J.of_yojson with
       | Error e -> Error ("dict." ^ e)
       | Ok _ as res -> res)
    | `Null -> Ok []
    | _ -> Error "dict"
  let to_yojson l =
    let json_l = List.map (fun (s, x) -> (s, J.to_yojson x)) l in
    `Assoc json_l
end

module JsonStringDictionary = Json_dictionary(Json_string)

module Uri: sig
  include Json_type with type t = private string
  val sarif_github:t
end
=
struct
  type t = string[@@deriving yojson]
  let sarif_github =
    "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json"
end

module Version: sig
  include Json_type with type t = private string
  val v2_1_0: t
end
=
struct
  type t = string[@@deriving yojson]
  let v2_1_0 = "2.1.0"
end

module ArtifactLocation = struct
  type t = {
    uri: string;
    uriBaseId: (string [@default ""])
  }[@@deriving yojson]

  type _t = t

  let create ~uri ?(uriBaseId = "") () = { uri; uriBaseId }

  let default = create ~uri:"" ()

  let of_loc loc =
    let uriBaseId, uri = Filepath.(Normalized.to_base_uri (fst loc).pos_path) in
    create ~uri ?uriBaseId ()
end

module ArtifactLocationDictionary = Json_dictionary(ArtifactLocation)

module Custom_properties =
  Json_dictionary(struct
    type t = Yojson.Safe.t
    let of_yojson x = Ok x
    let to_yojson x = x
  end)

module Properties = struct
  type tags = string list [@@deriving yojson]

  type t = {
    tags: tags;
    additional_properties: Custom_properties.t
  }

  type _t = t

  let default = { tags = []; additional_properties = [] }

  let create additional_properties =
    let tags = List.map fst additional_properties in
    { tags; additional_properties }

  let of_yojson = function
    | `Null -> Ok default
    | `Assoc l ->
      (match List.assoc_opt "tags" l with
       | None -> Error "properties"
       | Some json ->
         (match tags_of_yojson json with
          | Ok tags ->
            let additional_properties = List.remove_assoc "tags" l in
            Ok { tags; additional_properties }
          | Error loc -> Error ("properties." ^ loc)))
    | _ -> Error "properties"

  let to_yojson { tags; additional_properties } =
    match tags with
    | [] -> `Null
    | _ -> `Assoc (("tags", tags_to_yojson tags)::additional_properties)
end

module Message = struct
  type t = {
    text: (string [@default ""]);
    id: (string [@default ""]);
    markdown: (string [@default ""]);
    arguments: (string list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  type _t = t

  let create
      ?(text="")
      ?(id="")
      ?(markdown="")
      ?(arguments=[])
      ?(properties=Properties.default)
      ()
    =
    { text; id; markdown; arguments; properties }

  let plain_text ~text ?id ?arguments () =
    create ~text ?id ?arguments ()

  let markdown ~markdown ?id ?arguments () =
    let pp fmt = Markdown.pp_elements fmt in
    let markdown = String.trim (Format.asprintf "@[%a@]" pp markdown)
    in
    create ~markdown ?id ?arguments ()

  let default = create ()
end

module MultiformatMessageString = struct
  type t = {
    text: string;
    markdown: (string [@default ""]);
    properties: (Properties.t [@default Properties.default])
  }[@@deriving yojson]

  type _t = t

  let create ~text ?(markdown="") ?(properties=Properties.default) () =
    { text; markdown; properties }

  let default = create ~text:"default" ()
end

module MultiformatMessageStringDictionary =
  Json_dictionary(MultiformatMessageString)

module ArtifactContent = struct
  type t =
    { text: (string [@default ""]);
      binary: (string [@default ""]);
      rendered:
        (MultiformatMessageString.t [@default MultiformatMessageString.default]);
      properties: (Properties.t [@default Properties.default])
    }
  [@@deriving yojson]

  type _t = t

  let create ?(text="") ?(binary="")
      ?(rendered=MultiformatMessageString.default)
      ?(properties=Properties.default) () =
    { text; binary; rendered; properties }

  let default = create ()
end

module Region = struct
  type t = {
    startLine: (int [@default 0]);
    startColumn: (int [@default 0]);
    endLine: (int [@default 0]);
    endColumn: (int [@default 0]);
    charOffset: (int [@default 0]);
    charLength: (int [@default 0]);
    byteOffset: (int [@default 0]);
    byteLength: (int [@default 0]);
    snippet: (ArtifactContent.t [@default ArtifactContent.default]);
    message: (Message.t [@default Message.default])
  }[@@deriving yojson]

  let create
      ?(startLine = 0)
      ?(startColumn = 0)
      ?(endLine = 0)
      ?(endColumn = 0)
      ?(charOffset = 0)
      ?(charLength = 0)
      ?(byteOffset = 0)
      ?(byteLength = 0)
      ?(snippet = ArtifactContent.default)
      ?(message = Message.default)
      ()
    =
    { startLine; startColumn; endLine; endColumn; charOffset; charLength;
      byteOffset; byteLength; snippet; message }

  let default = create ()

  let of_loc loc =
    let open Filepath in
    let (start, finish) = loc in
    let startLine = start.pos_lnum in
    let startColumn = start.pos_cnum - start.pos_bol in
    let endLine = finish.pos_lnum in
    let endColumn = finish.pos_cnum - finish.pos_bol in
    let byteLength = finish.pos_cnum - start.pos_cnum in
    create ~startLine ~startColumn ~endLine ~endColumn ~byteLength ()
end

module Rectangle = struct
  type t = {
    top: (float [@default 0.]);
    left: (float [@default 0.]);
    bottom: (float [@default 0.]);
    right: (float [@default 0.]);
    message: (Message.t [@default Message.default]);
  }
  [@@deriving yojson]
end

module PhysicalLocation = struct
  type t = {
    id: (string [@default ""]);
    artifactLocation: ArtifactLocation.t;
    region: (Region.t [@default Region.default]);
    contextRegion: (Region.t [@default Region.default]);
  }[@@deriving yojson]

  let create
      ?(id = "")
      ~artifactLocation
      ?(region = Region.default)
      ?(contextRegion = Region.default)
      ()
    =
    { id; artifactLocation; region; contextRegion }

  let default = create ~artifactLocation:ArtifactLocation.default ()

  let of_loc loc =
    let artifactLocation = ArtifactLocation.of_loc loc in
    let region = Region.of_loc loc in
    create ~artifactLocation ~region ()

end

module Location = struct
  type t = {
    physicalLocation: PhysicalLocation.t;
    fullyQualifiedLogicalName: (string [@default ""]);
    message: (Message.t [@default Message.default]);
    annotations: (Region.t list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ~physicalLocation
      ?(fullyQualifiedLogicalName = "")
      ?(message = Message.default)
      ?(annotations = [])
      ?(properties = Properties.default)
      ()
    =
    { physicalLocation; fullyQualifiedLogicalName;
      message; annotations; properties;
    }

  let default = create ~physicalLocation:PhysicalLocation.default ()

  let of_loc loc =
    let physicalLocation = PhysicalLocation.of_loc loc in
    create ~physicalLocation ()
end

module StackFrame = struct
  type t = {
    location: (Location.t [@default Location.default]);
    stack_module: (string [@default ""])[@key "module"];
    threadId: (int [@default 0]);
    address: (int [@default 0]);
    offset: (int [@default 0]);
    parameters: (string list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Stack = struct
  type t = {
    message: (Message.t [@default Message.default]);
    frames: StackFrame.t list;
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let default = {
    message = Message.default;
    frames = [];
    properties = Properties.default;
  }
end


module Additional_properties = struct
  include Json_dictionary(struct type t = string[@@deriving yojson] end)

  let default = []
end

module Stl_importance: sig
  include Json_type with type t = private string
  val important: t
  val essential: t
  val unimportant: t
end
=
struct
  type t = string [@@deriving yojson]
  let important = "important"
  let essential = "essential"
  let unimportant = "unimportant"
end

module ThreadFlowLocation = struct
  type t = {
    step: int;
    location: (Location.t [@default Location.default]);
    stack: (Stack.t [@default Stack.default]);
    kind: (string [@default ""]);
    tfl_module: (string [@default ""])[@key "module"];
    state: (Additional_properties.t [@default Additional_properties.default]);
    nestingLevel: (int [@default 0]);
    executionOrder: (int [@default 0]);
    timestamp: (string [@default ""]);
    importance: (Stl_importance.t [@default Stl_importance.unimportant]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module ThreadFlow = struct
  type t = {
    id: (string [@default ""]);
    message: (Message.t [@default Message.default]);
    locations: ThreadFlowLocation.t list;
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Attachment = struct
  type t = {
    description: (Message.t [@default Message.default ]);
    artifactLocation: ArtifactLocation.t;
    regions: (Region.t list [@default []]);
    rectangles: (Rectangle.t list [@default []])
  } [@@deriving yojson]
end

module CodeFlow = struct
  type t = {
    description: (Message.t [@default Message.default]);
    threadFlows: ThreadFlow.t list;
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]
end

module Sarif_exception = struct
  type t = {
    kind: (string [@default ""]);
    message: (string [@default ""]);
    stack: (Stack.t [@default Stack.default]);
    innerExceptions: (t list [@default []]);
  }[@@deriving yojson]

  let default =
    {
      kind = "";
      message = "";
      stack = Stack.default;
      innerExceptions = []
    }
end

module Notification_kind: sig
  include Json_type with type t = private string
  val note: t
  val warning: t
  val error: t
end
=
struct
  type t = string [@@deriving yojson]
  let note = "note"
  let warning = "warning"
  let error = "error"
end

module Notification = struct
  type t = {
    id: (string [@default ""]);
    ruleId: (string [@default ""]);
    physicalLocation: (PhysicalLocation.t [@default PhysicalLocation.default]);
    message: Message.t;
    level: (Notification_kind.t [@default Notification_kind.warning]);
    threadId: (int [@default 0]);
    time: (string [@default ""]);
    exn: (Sarif_exception.t [@default Sarif_exception.default])
         [@key "exception"];
    properties: (Properties.t [@default Properties.default])
  }[@@deriving yojson]
end

module Driver = struct
  type t = {
    name: string;
    fullName: (string [@default ""]);
    version: (string [@default ""]);
    semanticVersion: (string [@default ""]);
    fileVersion: (string [@default ""]);
    downloadUri: (string [@default ""]);
    informationUri: (string [@default ""]);
    sarifLoggerVersion: (string [@default ""]);
    language: (string [@default "en-US"]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ~name
      ?(fullName="")
      ?(version="")
      ?(semanticVersion="")
      ?(fileVersion="")
      ?(downloadUri="")
      ?(informationUri="")
      ?(sarifLoggerVersion="")
      ?(language="en-US")
      ?(properties=Properties.default)
      ()
    =
    { name; fullName; version; semanticVersion; fileVersion;
      downloadUri; informationUri; sarifLoggerVersion; language; properties }

  let default = create ~name:"" ()
end

module Tool = struct
  type t = {
    driver: Driver.t
  }[@@deriving yojson]

  let create driver = { driver; }

  let default = create Driver.default
end

module Invocation = struct

  type t =  {
    commandLine: string;
    arguments: string list;
    responseFiles: (ArtifactLocation.t list [@default []]);
    attachments: (Attachment.t list [@default []]);
    startTime: (string [@default ""]);
    endTime: (string [@default ""]);
    exitCode: int;
    toolNotifications: (Notification.t list [@default []]);
    configurationNotifications: (Notification.t list [@default []]);
    exitCodeDescription: (string [@default ""]);
    exitSignalName: (string [@default ""]);
    exitSignalNumber: (int [@default 0]);
    processStartFailureMessage: (string [@default ""]);
    executionSuccessful: bool;
    machine: (string [@default ""]);
    account: (string [@default ""]);
    processId: (int [@default 0]);
    executableLocation: (ArtifactLocation.t [@default ArtifactLocation.default]);
    workingDirectory: (ArtifactLocation.t [@default ArtifactLocation.default]);
    environmentVariables:
      (Additional_properties.t [@default Additional_properties.default]);
    stdin: (ArtifactLocation.t [@default ArtifactLocation.default]);
    stdout: (ArtifactLocation.t [@default ArtifactLocation.default]);
    stderr: (ArtifactLocation.t [@default ArtifactLocation.default]);
    stdoutStderr: (ArtifactLocation.t [@default ArtifactLocation.default]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ~commandLine
      ?(arguments = [])
      ?(responseFiles = [])
      ?(attachments = [])
      ?(startTime = "")
      ?(endTime = "")
      ?(exitCode = 0)
      ?(toolNotifications = [])
      ?(configurationNotifications = [])
      ?(exitCodeDescription = "")
      ?(exitSignalName = "")
      ?(exitSignalNumber = 0)
      ?(processStartFailureMessage = "")
      ?(executionSuccessful = true)
      ?(machine = "")
      ?(account = "")
      ?(processId = 0)
      ?(executableLocation = ArtifactLocation.default)
      ?(workingDirectory = ArtifactLocation.default)
      ?(environmentVariables = Additional_properties.default)
      ?(stdin = ArtifactLocation.default)
      ?(stdout = ArtifactLocation.default)
      ?(stderr = ArtifactLocation.default)
      ?(stdoutStderr = ArtifactLocation.default)
      ?(properties = Properties.default)
      ()
    =
    {
      commandLine;
      arguments;
      responseFiles;
      attachments;
      startTime;
      endTime;
      exitCode;
      toolNotifications;
      configurationNotifications;
      exitCodeDescription;
      exitSignalName;
      exitSignalNumber;
      processStartFailureMessage;
      executionSuccessful;
      machine;
      account;
      processId;
      executableLocation;
      workingDirectory;
      environmentVariables;
      stdin;
      stdout;
      stderr;
      stdoutStderr;
      properties;
    }

  let default = create ~commandLine:"/bin/true" ()

end

module Conversion = struct
  type t = {
    tool: Tool.t;
    invocation: (Invocation.t [@default Invocation.default]);
    analysisToolLogFiles: (ArtifactLocation.t [@default ArtifactLocation.default]);
  } [@@deriving yojson]

  let default = {
    tool = {driver = Driver.default};
    invocation = Invocation.default;
    analysisToolLogFiles = ArtifactLocation.default;
  }
end

module Edge = struct
  type t  = {
    id: string;
    label: (Message.t [@default Message.default]);
    sourceNodeId: string;
    targetNodeId: string;
    properties: (Properties.t [@default Properties.default])
  } [@@deriving yojson]
end

module Node = struct
  type t = {
    id: string;
    label: (string [@default ""]);
    location: (Location.t [@default Location.default]);
    children: (t list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Edge_traversal = struct
  type t = {
    edgeId: string;
    message: (Message.t [@default Message.default]);
    finalState:
      (Additional_properties.t [@default Additional_properties.default]);
    stepOverEdgeCount: (int [@default 0]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Role: sig
  include Json_type with type t = private string
  val analysisTarget: t
  val attachment: t
  val responseFile: t
  val resultFile: t
  val standardStream: t
  val traceFile: t
  val unmodifiedFile: t
  val modifiedFile: t
  val addedFile: t
  val deletedFile:t
  val renamedFile:t
  val uncontrolledFile: t
end
=
struct
  type t = string[@@deriving yojson]

  let analysisTarget = "analysisTarget"
  let attachment = "attachment"
  let responseFile = "responseFile"
  let resultFile = "resultFile"
  let standardStream = "standardStream"
  let traceFile = "traceFile"
  let unmodifiedFile = "unmodifiedFile"
  let modifiedFile = "modifiedFile"
  let addedFile = "addedFile"
  let deletedFile = "deletedFile"
  let renamedFile = "renamedFile"
  let uncontrolledFile = "uncontrolledFile"
end

module Hash = struct
  type t = {
    value: string;
    algorithm: string
  } [@@deriving yojson]
end

module Graph = struct
  type t = {
    id : string;
    description: (Message.t [@default Message.default]);
    nodes: Node.t list;
    edges: Edge.t list;
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Graph_dictionary = Json_dictionary(Graph)

module GraphTraversal = struct
  type t = {
    graphId: string;
    description: (Message.t [@default Message.default]);
    initialState:
      (Additional_properties.t [@default Additional_properties.default]);
    edgeTraversals: Edge_traversal.t list;
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module Replacement = struct
  type t = {
    deletedRegion: Region.t;
    insertedContent: (ArtifactContent.t [@default ArtifactContent.default])
  }[@@deriving yojson]
end

module Artifact = struct
  type t = {
    description: (Message.t [@default Message.default]);
    location: (ArtifactLocation.t [@default ArtifactLocation.default]);
    parentIndex: (int [@default -1]);
    offset: (int [@default 0]);
    length: (int [@default -1]);
    roles: (Role.t list [@default []]);
    mimeType: (string [@default ""]);
    contents: (ArtifactContent.t [@default ArtifactContent.default]);
    encoding: (string [@default ""]);
    sourceLanguage: (string [@default ""]);
    hashes: (JsonStringDictionary.t [@default []]);
    lastModifiedTimeUtc: (string [@default ""]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ?(description = Message.default)
      ?(location = ArtifactLocation.default)
      ?(parentIndex = -1)
      ?(offset = 0)
      ?(length = -1)
      ?(roles = [])
      ?(mimeType = "")
      ?(contents = ArtifactContent.default)
      ?(encoding = "")
      ?(sourceLanguage = "")
      ?(hashes = [])
      ?(lastModifiedTimeUtc = "")
      ?(properties = Properties.default)
      ()
    =
    {
      description; location; parentIndex; offset; length; roles; mimeType;
      contents; encoding; sourceLanguage; hashes; lastModifiedTimeUtc;
      properties
    }
end

module FileChange = struct
  type t = {
    artifactLocation: ArtifactLocation.t;
    replacements: Replacement.t list
  }[@@deriving yojson]
end

module Fix = struct
  type t = {
    description: (Message.t [@defaut Message.default]);
    fileChanges: FileChange.t list;
  }[@@deriving yojson]
end

module ExternalFiles = struct
  type t = {
    conversion: (ArtifactLocation.t [@default ArtifactLocation.default]);
    files: (ArtifactLocation.t [@default ArtifactLocation.default]);
    graphs: (ArtifactLocation.t [@default ArtifactLocation.default]);
    invocations: (ArtifactLocation.t list [@default []]);
    logicalLocations: (ArtifactLocation.t [@default ArtifactLocation.default]);
    resources: (ArtifactLocation.t [@default ArtifactLocation.default]);
    results: (ArtifactLocation.t [@default ArtifactLocation.default]);
  }[@@deriving yojson]
end

module LogicalLocation = struct
  type t = {
    name: string;
    fullyQualifiedName: string;
    decoratedName: string;
    parentKey: string;
    kind: string;
  }[@@deriving yojson]
end

module RuleConfigLevel:
sig
  include Json_type with type t = private string
  val cl_none: t
  val cl_note: t
  val cl_warning: t
  val cl_error: t
end
=
struct
  type t = string [@@deriving yojson]
  let cl_none = "none"
  let cl_note = "note"
  let cl_warning = "warning"
  let cl_error = "error"
end

module ReportingConfiguration = struct
  type t = {
    enabled: (bool [@default false]);
    defaultLevel: (RuleConfigLevel.t [@default RuleConfigLevel.cl_none]);
    rank: (int [@default -1]);
    parameters: (Properties.t [@default Properties.default]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let default = {
    enabled = false;
    defaultLevel = RuleConfigLevel.cl_none;
    rank = -1;
    parameters = Properties.default;
    properties = Properties.default;
  }
end

module ToolComponentReference =struct
  type t = {
    name: (string [@default ""]);
    index: (int [@default -1]);
    guid: (string [@default ""]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ?(name="") ?(index = -1) ?(guid = "") ?(properties=Properties.default) () =
    { name; index; guid; properties }

  let default = create ()

end

module ReportingDescriptorReference =
struct
  type t = {
    id: (string [@default ""]);
    index: (int [@default -1]);
    guid: (string [@default ""]);
    toolComponent:
      (ToolComponentReference.t [@default ToolComponentReference.default]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ?(id="") ?(index = -1) ?(guid="")
      ?(toolComponent=ToolComponentReference.default)
      ?(properties=Properties.default) () =
    { id; index; guid; toolComponent; properties }

  let default = create ()
end

module ReportingDescriptorRelationship = struct
  type t = {
    target: ReportingDescriptorReference.t;
    kinds: (string list [@default ["relevant"]]);
    description: (Message.t [@default Message.default]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ~target
      ?(kinds=["relevant"])
      ?(description=Message.default)
      ?(properties=Properties.default) () =
    { target; kinds; description; properties }

  let default = create ~target:ReportingDescriptorReference.default ()
end

module ReportingDescriptor = struct
  type t = {
    id: string;
    deprecatedIds: (string list [@default []]);
    guid: (string [@default ""]);
    deprecatedGuids: (string list [@default []]);
    name: (string [@default ""]);
    deprecatedNames: (string list [@default []]);
    shortDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    fullDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    messageStrings:
      (MultiformatMessageStringDictionary.t [@default []]);
    defaultConfiguration:
      (ReportingConfiguration.t [@default ReportingConfiguration.default]);
    helpUri: (string [@default ""]);
    help:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    relationships:
      (ReportingDescriptorRelationship.t list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]

  let create
      ~id
      ?(deprecatedIds=[])
      ?(guid="")
      ?(deprecatedGuids=[])
      ?(name="")
      ?(deprecatedNames=[])
      ?(shortDescription=MultiformatMessageString.default)
      ?(fullDescription=MultiformatMessageString.default)
      ?(messageStrings=[])
      ?(defaultConfiguration=ReportingConfiguration.default)
      ?(helpUri="")
      ?(help=MultiformatMessageString.default)
      ?(relationships=[])
      ?(properties=Properties.default)
      ()
    =
    { id; deprecatedIds; guid; deprecatedGuids; name; deprecatedNames;
      shortDescription; fullDescription; messageStrings;
      defaultConfiguration; helpUri; help; relationships; properties }

  let default = create ~id:"id" ()

end

module Result_kind:
sig
  type t = private string
  val notApplicable: t
  val pass: t
  val fail: t
  val review: t
  val open_: t
  val informational: t

  val to_yojson: t -> Yojson.Safe.t
  val of_yojson: Yojson.Safe.t -> (t,string) result
end
=
struct
  type t = string[@@deriving yojson]
  let notApplicable = "notApplicable"
  let pass = "pass"
  let fail = "fail"
  let review = "review"
  let open_ = "open"
  let informational = "informational"
end

module Result_level:
sig
  type t = private string
  val none: t
  val note: t
  val warning: t
  val error: t

  val to_yojson: t -> Yojson.Safe.t
  val of_yojson: Yojson.Safe.t -> (t,string) result
end
=
struct
  type t = string[@@deriving yojson]
  let none = "none"
  let note = "note"
  let warning = "warning"
  let error = "error"
end

module Result_suppressionState: sig
  include Json_type with type t = private string
  val suppressedInSource: t
  val suppressedExternally: t
end
=
struct
  type t = string [@@deriving yojson]
  let suppressedInSource = "suppressedInSource"
  let suppressedExternally = "suppressedExternally"
end

module Result_baselineState: sig
  include Json_type with type t = private string
  val bs_new: t
  val bs_existing: t
  val bs_absent: t
end
=
struct
  type t = string [@@deriving yojson]
  let bs_new = "new"
  let bs_existing = "existing"
  let bs_absent = "absent"
end

(* we can't use Result here, as this would conflict with
   Ppx_deriving_yojson_runtime.Result that is opened by the
   code generated by Ppx_deriving_yojson. *)
module Sarif_result = struct
  type t = {
    ruleId: (string [@default ""]);
    kind: (Result_kind.t[@default Result_kind.fail]);
    level: (Result_level.t[@default Result_level.warning]);
    message: (Message.t [@default Message.default]);
    analysisTarget: (ArtifactLocation.t [@default ArtifactLocation.default]);
    locations: (Location.t list [@default []]);
    instanceGuid: (string [@default ""]);
    correlationGuid: (string [@default ""]);
    occurrenceCount: (int [@default 1]);
    partialFingerprints:
      (Additional_properties.t [@default Additional_properties.default]);
    fingerprints:
      (Additional_properties.t [@default Additional_properties.default]);
    stacks: (Stack.t list [@default []]);
    codeFlows: (CodeFlow.t list [@default []]);
    graphs: (Graph_dictionary.t [@default []]);
    graphTraversals: (GraphTraversal.t list [@default []]);
    relatedLocations: (Location.t list [@default []]);
    suppressionStates: (Result_suppressionState.t list [@default []]);
    baselineState:
      (Result_baselineState.t [@default Result_baselineState.bs_absent]);
    attachments: (Attachment.t list [@default []]);
    workItemsUris: (string list [@default []]);
    conversionProvenance: (PhysicalLocation.t list [@default[]]);
    fixes: (Fix.t list [@default []]);
    properties: (Properties.t [@default Properties.default])
  }[@@deriving yojson]

  let create
      ~ruleId
      ?(kind=Result_kind.pass)
      ?(level=Result_level.none)
      ?(message=Message.default)
      ?(analysisTarget=ArtifactLocation.default)
      ?(locations=[])
      ?(instanceGuid="")
      ?(correlationGuid="")
      ?(occurrenceCount=1)
      ?(partialFingerprints=Additional_properties.default)
      ?(fingerprints=Additional_properties.default)
      ?(stacks=[])
      ?(codeFlows=[])
      ?(graphs=[])
      ?(graphTraversals=[])
      ?(relatedLocations=[])
      ?(suppressionStates=[])
      ?(baselineState=Result_baselineState.bs_absent)
      ?(attachments=[])
      ?(workItemsUris=[])
      ?(conversionProvenance=[])
      ?(fixes=[])
      ?(properties=Properties.default)
      ()
    =
    {
      ruleId; kind; level; message; analysisTarget; locations; instanceGuid;
      correlationGuid; occurrenceCount; partialFingerprints; fingerprints;
      stacks; codeFlows; graphs; graphTraversals; relatedLocations;
      suppressionStates; baselineState; attachments; workItemsUris;
      conversionProvenance; fixes; properties
    }
end

module VersionControlDetails = struct
  type t = {
    uri: string;
    revisionId: (string [@default ""]);
    branch: (string [@default ""]);
    tag: (string [@default ""]);
    timestamp: (string [@default ""]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
end

module ColumnKind: sig
  include Json_type with type t = private string
  val utf16CodeUnits: t
  val unicodeCodePoints: t
end
=
struct
  type t = string [@@deriving yojson]
  let utf16CodeUnits = "utf16CodeUnits"
  let unicodeCodePoints = "unicodeCodePoints"
end

module RunAutomationDetails = struct
  type t = {
    description: (Message.t [@default Message.default]);
    id: (string [@default ""]);
    guid: (string [@default ""]);
    correlationGuid: (string [@default ""]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ?(description=Message.default) ?(id="") ?(guid="") ?(correlationGuid="")
      ?(properties=Properties.default) () =
    { description; id; guid; correlationGuid; properties }

  let default = create ()
end

module ExternalPropertyFileReferences = struct
  type t = {
    location: (ArtifactLocation.t [@default ArtifactLocation.default]);
    guid: (string [@default ""]);
    itemCount: (int [@default -1]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ?(location = ArtifactLocation.default)
      ?(guid = "")
      ?(itemCount = -1)
      ?(properties = Properties.default)
      () =
    { location; guid; itemCount; properties }

  let default = create ()
end

module TranslationMetadata = struct
  type t = {
    name: (string [@default ""]);
    fullName: (string [@default ""]);
    shortDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    fullDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    downloadUri: (string [@default ""]);
    informationUri: (string [@default ""]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ~name
      ?(fullName = "")
      ?(shortDescription = MultiformatMessageString.default)
      ?(fullDescription = MultiformatMessageString.default)
      ?(downloadUri = "")
      ?(informationUri = "")
      ?(properties = Properties.default)
      ()
    =
    { name; fullName; shortDescription; fullDescription;
      downloadUri; informationUri; properties }

  let default = create ~name:"" ()
end

module ToolComponent = struct
  module Contents: sig
    include Json_type with type t = private string
    val localizedData: t
    val nonLocalizedData: t
  end = struct
    type t = string [@@deriving yojson]
    let localizedData = "localizedData"
    let nonLocalizedData = "nonLocalizedData"
  end
  type t = {
    guid: (string [@default ""]);
    name: (string [@default ""]);
    organization: (string [@default ""]);
    product: (string [@default ""]);
    productSuite: (string [@default ""]);
    shortDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    fullDescription:
      (MultiformatMessageString.t [@default MultiformatMessageString.default]);
    fullName: (string [@default ""]);
    version: (string [@default ""]);
    semanticVersion: (string [@default ""]);
    dottedQuadFileVersion: (string [@default ""]);
    releaseDateUtc: (string [@default ""]);
    downloadUri: (string [@default ""]);
    informationUri: (string [@default ""]);
    globalMessageStrings: (MultiformatMessageStringDictionary.t [@default []]);
    notifications: (ReportingDescriptor.t list [@default []]);
    rules: (ReportingDescriptor.t list [@default []]);
    taxa: (ReportingDescriptor.t list [@default []]);
    locations: (ArtifactLocation.t list [@default []]);
    language: (string [@default "en-US"]);
    contents: (Contents.t list [@default []]);
    isComprehensive: (bool [@default false]);
    localizedDataSemanticVersion: (string [@default ""]);
    minimumRequiredLocalizedDataSemanticVersion: (string [@default ""]);
    associateComponent:
      (ToolComponentReference.t [@default ToolComponentReference.default]);
    translationMetadata:
      (TranslationMetadata.t [@default TranslationMetadata.default]);
    supportedTaxonomies: (ToolComponentReference.t list [@default []]);
    properties: (Properties.t [@default Properties.default]);
  }[@@deriving yojson]
  let create
      ?(guid="")
      ~name
      ?(organization="")
      ?(product="")
      ?(productSuite="")
      ?(shortDescription=MultiformatMessageString.default)
      ?(fullDescription=MultiformatMessageString.default)
      ?(fullName="")
      ?(version="")
      ?(semanticVersion="")
      ?(dottedQuadFileVersion="")
      ?(releaseDateUtc="")
      ?(downloadUri="")
      ?(informationUri="")
      ?(globalMessageStrings=[])
      ?(notifications=[])
      ?(rules=[])
      ?(taxa=[])
      ?(locations=[])
      ?(language="en-US")
      ?(contents=[Contents.nonLocalizedData])
      ?(isComprehensive=false)
      ?(localizedDataSemanticVersion="")
      ?(minimumRequiredLocalizedDataSemanticVersion="")
      ?(associateComponent=ToolComponentReference.default)
      ?(translationMetadata=TranslationMetadata.default)
      ?(supportedTaxonomies=[])
      ?(properties=Properties.default)
      ()
    =
    { guid; name; organization; product; productSuite; shortDescription;
      fullDescription; fullName; version; semanticVersion;
      dottedQuadFileVersion; releaseDateUtc; downloadUri; informationUri;
      globalMessageStrings; notifications; rules; taxa; locations; language;
      contents; isComprehensive; localizedDataSemanticVersion;
      minimumRequiredLocalizedDataSemanticVersion;
      associateComponent; translationMetadata; supportedTaxonomies; properties }
  let default = create ~name:"" ()
end

module Address = struct
  type t = {
    absoluteAddress: (int [@default -1]);
    relativeAddress: (int [@default 0]);
    length: (int [@default 0]);
    kind: (string [@default ""]);
    name: (string [@default ""]);
    fullyQualifiedName: (string [@default ""]);
    offsetFromParent: (int [@default 0]);
    index: (int [@default -1]);
    parentIndex: (int [@default -1]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ?(absoluteAddress = -1)
      ?(relativeAddress = 0)
      ?(length = 0)
      ?(kind = "")
      ?(name = "")
      ?(fullyQualifiedName = "")
      ?(offsetFromParent = 0)
      ?(index = -1)
      ?(parentIndex = -1)
      ?(properties = Properties.default)
      ()
    =
    { absoluteAddress; relativeAddress; length; kind; name;
      fullyQualifiedName; offsetFromParent; index; parentIndex; properties }

  let default = create ()
end

module WebRequest = struct
  type t = {
    index: (int [@default -1]);
    protocol: (string [@default ""]);
    version: (string [@default ""]);
    target: (string [@default ""]);
    method_: (string [@default ""]) [@key "method"];
    headers: (JsonStringDictionary.t [@default []]);
    parameters: (JsonStringDictionary.t [@default []]);
    body: (ArtifactContent.t [@default ArtifactContent.default]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ?(index = -1)
      ?(protocol = "")
      ?(version = "")
      ?(target = "")
      ?(method_ = "")
      ?(headers = [])
      ?(parameters = [])
      ?(body = ArtifactContent.default)
      ?(properties = Properties.default)
      ()
    =
    { index; protocol; version; target; method_; headers; parameters;
      body; properties }

  let default = create ()

end

module WebResponse = struct
  type t = {
    index: (int [@default -1]);
    protocol: (string [@default ""]);
    version: (string [@default ""]);
    statusCode: (int [@default 0]);
    reasonPhrase: (string [@default ""]);
    headers: (JsonStringDictionary.t [@default []]);
    body: (ArtifactContent.t [@default ArtifactContent.default]);
    noResponseReceived: (bool [@default false]);
    properties: (Properties.t [@default Properties.default]);
  } [@@deriving yojson]

  let create
      ?(index = -1)
      ?(protocol = "")
      ?(version = "")
      ?(statusCode = 0)
      ?(reasonPhrase = "")
      ?(headers = [])
      ?(body = ArtifactContent.default)
      ?(noResponseReceived = false)
      ?(properties = Properties.default)
      ()
    =
    { index; protocol; version; statusCode; reasonPhrase;
      headers; body; noResponseReceived; properties }

  let default = create ()

end

module SpecialLocations = struct
  type t = {
    displayBase: (ArtifactLocation.t [@default ArtifactLocation.default]);
    properties: (Properties.t [@default Properties.default])
  } [@@deriving yojson]
  let create
      ?(displayBase = ArtifactLocation.default)
      ?(properties = Properties.default)
      ()
    =
    { displayBase; properties }

  let default = create ()
end

module Run = struct
  type t = {
    tool: Tool.t;
    invocations: (Invocation.t list [@default []]);
    conversion: (Conversion.t [@default Conversion.default]);
    language: (string [@default "en-US"]);
    versionControlProvenance: (VersionControlDetails.t list [@default []]);
    originalUriBaseIds:
      (ArtifactLocationDictionary.t [@default []]);
    artifacts: (Artifact.t list [@default []]);
    logicalLocations: (LogicalLocation.t list [@default []]);
    graphs: (Graph.t list [@default []]);
    results: (Sarif_result.t list [@default []]);
    automationDetails:
      (RunAutomationDetails.t [@default RunAutomationDetails.default]);
    runAggregates: (RunAutomationDetails.t list [@default []]);
    baselineGuid: (string [@default ""]);
    redactionToken: (string list [@default []]);
    defaultEncoding: (string [@default "utf-8"]);
    defaultSourceLanguage: (string [@default ""]);
    newlineSequences: (string list [@default ["\r\n"; "\n"]]);
    columnKind: (ColumnKind.t [@default ColumnKind.unicodeCodePoints]);
    externalPropertyFileReferences:
      (ExternalPropertyFileReferences.t
       [@default ExternalPropertyFileReferences.default]);
    threadFlowLocations: (ThreadFlowLocation.t list [@default []]);
    taxonomies: (ToolComponent.t list [@default []]);
    addresses: (Address.t list [@default []]);
    translations: (ToolComponent.t list [@default []]);
    policies: (ToolComponent.t list [@default[]]);
    webRequests: (WebRequest.t list [@default[]]);
    webResponses: (WebResponse.t list [@default[]]);
    specialLocations: (SpecialLocations.t [@default SpecialLocations.default]);
    properties: (Properties.t [@default Properties.default]);
  }
  [@@deriving yojson]

  let create
      ~tool
      ?(invocations=[])
      ?(conversion=Conversion.default)
      ?(language="en-US")
      ?(versionControlProvenance=[])
      ?(originalUriBaseIds=[])
      ?(artifacts=[])
      ?(logicalLocations=[])
      ?(graphs=[])
      ?(results=[])
      ?(automationDetails=RunAutomationDetails.default)
      ?(runAggregates=[])
      ?(baselineGuid="")
      ?(redactionToken=[])
      ?(defaultEncoding="utf-8")
      ?(defaultSourceLanguage="C")
      ?(newlineSequences=["\r\n"; "\n"])
      ?(columnKind=ColumnKind.unicodeCodePoints)
      ?(externalPropertyFileReferences=ExternalPropertyFileReferences.default)
      ?(threadFlowLocations=[])
      ?(taxonomies=[])
      ?(addresses=[])
      ?(translations=[])
      ?(policies=[])
      ?(webRequests=[])
      ?(webResponses=[])
      ?(specialLocations=SpecialLocations.default)
      ?(properties=Properties.default)
      ()
    =
    {
      tool; invocations; conversion; versionControlProvenance;
      language; originalUriBaseIds;
      artifacts; logicalLocations; graphs; results;
      automationDetails; runAggregates; baselineGuid; redactionToken;
      defaultEncoding; defaultSourceLanguage; newlineSequences; columnKind;
      externalPropertyFileReferences; threadFlowLocations; taxonomies;
      addresses; translations; policies; webRequests; webResponses;
      specialLocations; properties;
    }
end

module Schema = struct
  type t = {
    schema: Uri.t [@key "$schema"];
    version: Version.t;
    runs: Run.t list
  } [@@deriving yojson]

  let create ?(schema=Uri.sarif_github) ?(version=Version.v2_1_0) ~runs () =
    { schema; version; runs }
end
