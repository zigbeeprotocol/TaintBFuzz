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

module type Json_type = sig
  type t
  val of_yojson: Yojson.Safe.t -> t Ppx_deriving_yojson_runtime.error_or
  val to_yojson: t -> Yojson.Safe.t
end

module type Json_default = sig
  include Json_type
  val default: t
end

module Json_string: Json_type with type t = string

type 'a dict = (string * 'a) list

module Json_dictionary(J: Json_type):
  Json_type with type t = J.t dict

module JsonStringDictionary: Json_type with type t = string dict

module Uri: sig
  include Json_type with type t = private string
  val sarif_github:t
end

module Version: sig
  include Json_type with type t = private string
  val v2_1_0: t
end

module ArtifactLocation: sig
  type t = {
    uri: string;
    uriBaseId: string
  } [@@ deriving of_yojson]

  val create: uri:string -> ?uriBaseId:string -> unit -> t

  val of_loc: Cil_datatype.Location.t -> t

  val default: t

end

module ArtifactLocationDictionary:
  Json_type with type t = ArtifactLocation.t dict

module Custom_properties: Json_type with type t = Yojson.Safe.t dict

module Properties: sig
  type tags = string list

  type t = {
    tags: tags;
    additional_properties: Custom_properties.t
  } [@@ deriving of_yojson]

  val create: Custom_properties.t -> t

  val default: t

end

module Message: sig
  type t = {
    text: string;
    id: string;
    markdown: string;
    arguments: string list;
    properties: Properties.t;
  } [@@deriving of_yojson]

  val create:
    ?text:string ->
    ?id: string ->
    ?markdown: string ->
    ?arguments: string list ->
    ?properties: Properties.t ->
    unit ->
    t

  val plain_text:
    text:string -> ?id:string -> ?arguments:string list -> unit -> t

  val markdown:
    markdown:Markdown.elements ->
    ?id:string -> ?arguments:string list -> unit -> t

end

module MultiformatMessageString: sig
  type t = {
    text: string;
    markdown: string;
    properties: Properties.t;
  } [@@deriving of_yojson]

  val create:
    text:string -> ?markdown:string -> ?properties:Properties.t -> unit -> t

  val default: t

end

module MultiformatMessageStringDictionary:
  Json_type with type t = MultiformatMessageString.t dict

module ArtifactContent: sig
  type t =
    { text: string;
      binary: string;
      rendered: MultiformatMessageString.t;
      properties: Properties.t;
    }
  [@@deriving of_yojson]

  val create:
    ?text:string -> ?binary:string ->
    ?rendered:MultiformatMessageString.t ->
    ?properties:Properties.t -> unit -> t

  val default: t
end

module Region: sig
  type t = {
    startLine: int;
    startColumn: int;
    endLine: int;
    endColumn: int;
    charOffset: int;
    charLength: int;
    byteOffset: int;
    byteLength: int;
    snippet: ArtifactContent.t;
    message: Message.t;
  }[@@deriving yojson]

  val create:
    ?startLine:int ->
    ?startColumn:int ->
    ?endLine:int ->
    ?endColumn:int ->
    ?charOffset:int ->
    ?charLength:int ->
    ?byteOffset:int ->
    ?byteLength: int ->
    ?snippet: ArtifactContent.t ->
    ?message: Message.t ->
    unit -> t

  val default: t

  val of_loc: Cil_datatype.Location.t -> t
end

module Rectangle: sig
  type t = {
    top: float;
    left: float;
    bottom: float;
    right: float;
    message: Message.t;
  }
  [@@deriving yojson]
end

module PhysicalLocation: sig
  type t = {
    id: string;
    artifactLocation: ArtifactLocation.t;
    region: Region.t;
    contextRegion: Region.t;
  }[@@deriving yojson]

  val create:
    ?id:string ->
    artifactLocation: ArtifactLocation.t ->
    ?region: Region.t ->
    ?contextRegion: Region.t ->
    unit -> t

  val default: t

  val of_loc: Cil_datatype.Location.t -> t

end

module Location: sig
  type t = {
    physicalLocation: PhysicalLocation.t;
    fullyQualifiedLogicalName: string;
    message: Message.t;
    annotations: Region.t list;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    physicalLocation: PhysicalLocation.t ->
    ?fullyQualifiedLogicalName: string ->
    ?message: Message.t ->
    ?annotations: Region.t list ->
    ?properties: Properties.t ->
    unit -> t

  val default: t

  val of_loc: Cil_datatype.Location.t -> t

end

module StackFrame: sig
  type t = {
    location: Location.t;
    stack_module: string;
    threadId: int;
    address: int;
    offset: int;
    parameters: string list;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Stack: sig
  type t = {
    message: Message.t;
    frames: StackFrame.t list;
    properties: Properties.t;
  }[@@deriving yojson]

  val default: t
end

module Additional_properties: Json_default with type t = string dict

module Stl_importance: sig
  include Json_type with type t = private string
  val important: t
  val essential: t
  val unimportant: t
end

module ThreadFlowLocation: sig
  type t = {
    step: int;
    location: Location.t;
    stack: Stack.t;
    kind: string;
    tfl_module: string;
    state: Additional_properties.t;
    nestingLevel: int;
    executionOrder: int;
    timestamp: string;
    importance: Stl_importance.t;
    properties: Properties.t;
  }[@@deriving yojson]
end

module ThreadFlow: sig
  type t = {
    id: string;
    message: Message.t;
    locations: ThreadFlowLocation.t list;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Attachment: sig
  type t = {
    description: Message.t;
    artifactLocation: ArtifactLocation.t;
    regions: Region.t list;
    rectangles: Rectangle.t list;
  } [@@deriving yojson]
end

module CodeFlow: sig
  type t = {
    description: Message.t;
    threadFlows: ThreadFlow.t list;
    properties: Properties.t;
  } [@@deriving yojson]
end

module Sarif_exception: sig
  type t = {
    kind: string;
    message: string;
    stack: Stack.t;
    innerExceptions: t list;
  }[@@deriving yojson]

  val default: t

end

module Notification_kind: sig
  include Json_type with type t = private string
  val note: t
  val warning: t
  val error: t
end

module Notification: sig
  type t = {
    id: string;
    ruleId: string;
    physicalLocation: PhysicalLocation.t;
    message: Message.t;
    level: Notification_kind.t;
    threadId: int;
    time: string;
    exn: Sarif_exception.t;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Driver: sig
  type t = {
    name: string;
    fullName: string;
    version: string;
    semanticVersion: string;
    fileVersion: string;
    downloadUri: string;
    informationUri: string;
    sarifLoggerVersion: string;
    language: string;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    name: string ->
    ?fullName: string ->
    ?version: string ->
    ?semanticVersion: string ->
    ?fileVersion: string ->
    ?downloadUri: string ->
    ?informationUri: string ->
    ?sarifLoggerVersion: string ->
    ?language: string ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module Tool: sig
  type t = {
    driver: Driver.t
  }[@@deriving yojson]

  val create: Driver.t -> t

  val default: t
end

module Invocation: sig

  type t =  {
    commandLine: string;
    arguments: string list;
    responseFiles: ArtifactLocation.t list;
    attachments: Attachment.t list;
    startTime: string;
    endTime: string;
    exitCode: int;
    toolNotifications: Notification.t list;
    configurationNotifications: Notification.t list;
    exitCodeDescription: string;
    exitSignalName: string;
    exitSignalNumber: int;
    processStartFailureMessage: string;
    executionSuccessful: bool;
    machine: string;
    account: string;
    processId: int;
    executableLocation: ArtifactLocation.t;
    workingDirectory: ArtifactLocation.t;
    environmentVariables: Additional_properties.t;
    stdin: ArtifactLocation.t;
    stdout: ArtifactLocation.t;
    stderr: ArtifactLocation.t;
    stdoutStderr: ArtifactLocation.t;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    commandLine: string ->
    ?arguments: string list ->
    ?responseFiles: ArtifactLocation.t list ->
    ?attachments: Attachment.t list ->
    ?startTime: string ->
    ?endTime: string ->
    ?exitCode: int ->
    ?toolNotifications: Notification.t list ->
    ?configurationNotifications: Notification.t list ->
    ?exitCodeDescription: string ->
    ?exitSignalName: string ->
    ?exitSignalNumber: int ->
    ?processStartFailureMessage: string ->
    ?executionSuccessful: bool ->
    ?machine: string ->
    ?account: string ->
    ?processId: int ->
    ?executableLocation: ArtifactLocation.t ->
    ?workingDirectory: ArtifactLocation.t ->
    ?environmentVariables: Additional_properties.t ->
    ?stdin: ArtifactLocation.t ->
    ?stdout: ArtifactLocation.t ->
    ?stderr: ArtifactLocation.t ->
    ?stdoutStderr: ArtifactLocation.t ->
    ?properties: Properties.t ->
    unit -> t

  val default: t

end

module Conversion: sig
  type t = {
    tool: Tool.t;
    invocation: Invocation.t;
    analysisToolLogFiles: ArtifactLocation.t;
  } [@@deriving yojson]

  val default: t

end

module Edge: sig
  type t  = {
    id: string;
    label: Message.t;
    sourceNodeId: string;
    targetNodeId: string;
    properties: Properties.t;
  } [@@deriving yojson]
end

module Node: sig
  type t = {
    id: string;
    label: string;
    location: Location.t;
    children: t list;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Edge_traversal: sig
  type t = {
    edgeId: string;
    message: Message.t;
    finalState: Additional_properties.t;
    stepOverEdgeCount: int;
    properties: Properties.t;
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

module Hash: sig
  type t = {
    value: string;
    algorithm: string
  } [@@deriving yojson]
end

module Graph: sig
  type t = {
    id : string;
    description: Message.t;
    nodes: Node.t list;
    edges: Edge.t list;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Graph_dictionary: Json_type with type t = Graph.t dict

module GraphTraversal: sig
  type t = {
    graphId: string;
    description: Message.t;
    initialState: Additional_properties.t;
    edgeTraversals: Edge_traversal.t list;
    properties: Properties.t;
  }[@@deriving yojson]
end

module Replacement: sig
  type t = {
    deletedRegion: Region.t;
    insertedContent: ArtifactContent.t;
  }[@@deriving yojson]
end

module Artifact: sig
  type t = {
    description: Message.t;
    location: ArtifactLocation.t;
    parentIndex: int;
    offset: int;
    length: int;
    roles: Role.t list;
    mimeType: string;
    contents: ArtifactContent.t;
    encoding: string;
    sourceLanguage: string;
    hashes: JsonStringDictionary.t;
    lastModifiedTimeUtc: string;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    ?description: Message.t ->
    ?location: ArtifactLocation.t ->
    ?parentIndex: int ->
    ?offset: int ->
    ?length: int ->
    ?roles: Role.t list ->
    ?mimeType: string ->
    ?contents: ArtifactContent.t ->
    ?encoding: string ->
    ?sourceLanguage: string ->
    ?hashes: JsonStringDictionary.t ->
    ?lastModifiedTimeUtc: string ->
    ?properties: Properties.t ->
    unit -> t

end

module FileChange: sig
  type t = {
    artifactLocation: ArtifactLocation.t;
    replacements: Replacement.t list
  }[@@deriving yojson]
end

module Fix: sig
  type t = {
    description: (Message.t [@defaut Message.default]);
    fileChanges: FileChange.t list;
  }[@@deriving yojson]
end

module ExternalFiles: sig
  type t = {
    conversion: ArtifactLocation.t;
    files: ArtifactLocation.t;
    graphs: ArtifactLocation.t;
    invocations: ArtifactLocation.t list;
    logicalLocations: ArtifactLocation.t;
    resources: ArtifactLocation.t;
    results: ArtifactLocation.t;
  }[@@deriving yojson]
end

module LogicalLocation: sig
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

module ReportingConfiguration: sig
  type t = {
    enabled: bool;
    defaultLevel: RuleConfigLevel.t;
    rank: int;
    parameters: Properties.t;
    properties: Properties.t;
  }[@@deriving yojson]

  val default: t

end

module ToolComponentReference: sig
  type t = {
    name: string;
    index: int;
    guid: string;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    ?name:string -> ?index:int -> ?guid:string -> ?properties:Properties.t ->
    unit -> t

  val default: t

end

module ReportingDescriptorReference: sig
  type t = {
    id: string;
    index: int;
    guid: string;
    toolComponent: ToolComponentReference.t;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    ?id: string -> ?index:int -> ?guid:string ->
    ?toolComponent:ToolComponentReference.t ->
    ?properties: Properties.t -> unit -> t

  val default: t
end

module ReportingDescriptorRelationship: sig
  type t = {
    target: ReportingDescriptorReference.t;
    kinds: string list;
    description: Message.t;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    target: ReportingDescriptorReference.t ->
    ?kinds: string list ->
    ?description:Message.t ->
    ?properties:Properties.t -> unit -> t

  val default: t

end

module ReportingDescriptor: sig
  type t = {
    id: string;
    deprecatedIds: string list;
    guid: string;
    deprecatedGuids: string list;
    name: string;
    deprecatedNames: string list;
    shortDescription: MultiformatMessageString.t;
    fullDescription: MultiformatMessageString.t;
    messageStrings: MultiformatMessageStringDictionary.t;
    defaultConfiguration: ReportingConfiguration.t;
    helpUri: string;
    help: MultiformatMessageString.t;
    relationships: ReportingDescriptorRelationship.t list;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    id: string ->
    ?deprecatedIds: string list ->
    ?guid: string ->
    ?deprecatedGuids: string list ->
    ?name: string ->
    ?deprecatedNames: string list ->
    ?shortDescription: MultiformatMessageString.t ->
    ?fullDescription: MultiformatMessageString.t ->
    ?messageStrings: MultiformatMessageStringDictionary.t ->
    ?defaultConfiguration: ReportingConfiguration.t ->
    ?helpUri: string ->
    ?help: MultiformatMessageString.t ->
    ?relationships: ReportingDescriptorRelationship.t list ->
    ?properties: Properties.t -> unit -> t

  val default: t

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

module Result_suppressionState: sig
  include Json_type with type t = private string
  val suppressedInSource: t
  val suppressedExternally: t
end

module Result_baselineState: sig
  include Json_type with type t = private string
  val bs_new: t
  val bs_existing: t
  val bs_absent: t
end

(* we can't use Result here, as this would conflict with
   Ppx_deriving_yojson_runtime.Result that is opened by the
   code generated by Ppx_deriving_yojson. *)
module Sarif_result: sig
  type t = {
    ruleId: string;
    kind: Result_kind.t;
    level: Result_level.t;
    message: Message.t;
    analysisTarget: ArtifactLocation.t;
    locations: Location.t list;
    instanceGuid: string;
    correlationGuid: string;
    occurrenceCount: int;
    partialFingerprints: Additional_properties.t;
    fingerprints: Additional_properties.t;
    stacks: Stack.t list;
    codeFlows: CodeFlow.t list;
    graphs: Graph_dictionary.t;
    graphTraversals: GraphTraversal.t list;
    relatedLocations: Location.t list;
    suppressionStates: Result_suppressionState.t list;
    baselineState: Result_baselineState.t;
    attachments: Attachment.t list;
    workItemsUris: string list;
    conversionProvenance: PhysicalLocation.t list;
    fixes: Fix.t list;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    ruleId: string ->
    ?kind: Result_kind.t ->
    ?level: Result_level.t ->
    ?message: Message.t ->
    ?analysisTarget: ArtifactLocation.t ->
    ?locations: Location.t list ->
    ?instanceGuid: string ->
    ?correlationGuid: string ->
    ?occurrenceCount: int ->
    ?partialFingerprints: Additional_properties.t ->
    ?fingerprints: Additional_properties.t ->
    ?stacks: Stack.t list ->
    ?codeFlows: CodeFlow.t list ->
    ?graphs: Graph_dictionary.t ->
    ?graphTraversals: GraphTraversal.t list ->
    ?relatedLocations: Location.t list ->
    ?suppressionStates: Result_suppressionState.t list ->
    ?baselineState: Result_baselineState.t ->
    ?attachments: Attachment.t list ->
    ?workItemsUris: string list ->
    ?conversionProvenance: PhysicalLocation.t list ->
    ?fixes: Fix.t list ->
    ?properties: Properties.t ->
    unit -> t

end

module VersionControlDetails: sig
  type t = {
    uri: string;
    revisionId: string;
    branch: string;
    tag: string;
    timestamp: string;
    properties: Properties.t;
  }[@@deriving yojson]
end

module ColumnKind: sig
  include Json_type with type t = private string
  val utf16CodeUnits: t
  val unicodeCodePoints: t
end

module RunAutomationDetails: sig
  type t = {
    description: Message.t;
    id: string;
    guid: string;
    correlationGuid: string;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?description: Message.t -> ?id: string -> ?guid: string ->
    ?correlationGuid: string -> ?properties: Properties.t ->
    unit -> t

  val default: t
end

module ExternalPropertyFileReferences: sig
  type t = {
    location: ArtifactLocation.t;
    guid: string;
    itemCount: int;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?location: ArtifactLocation.t ->
    ?guid: string ->
    ?itemCount: int ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module TranslationMetadata: sig
  type t = {
    name: string;
    fullName: string;
    shortDescription: MultiformatMessageString.t;
    fullDescription: MultiformatMessageString.t;
    downloadUri: string;
    informationUri: string;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    name: string ->
    ?fullName: string ->
    ?shortDescription: MultiformatMessageString.t ->
    ?fullDescription: MultiformatMessageString.t ->
    ?downloadUri: string ->
    ?informationUri: string ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module ToolComponent: sig
  module Contents: sig
    include Json_type with type t = private string
    val localizedData: t
    val nonLocalizedData: t
  end
  type t = {
    guid: string;
    name: string;
    organization: string;
    product: string;
    productSuite: string;
    shortDescription: MultiformatMessageString.t;
    fullDescription: MultiformatMessageString.t;
    fullName: string;
    version: string;
    semanticVersion: string;
    dottedQuadFileVersion: string;
    releaseDateUtc: string;
    downloadUri: string;
    informationUri: string;
    globalMessageStrings: MultiformatMessageStringDictionary.t;
    notifications: ReportingDescriptor.t list;
    rules: ReportingDescriptor.t list;
    taxa: ReportingDescriptor.t list;
    locations: ArtifactLocation.t list;
    language: string;
    contents: Contents.t list;
    isComprehensive: bool;
    localizedDataSemanticVersion: string;
    minimumRequiredLocalizedDataSemanticVersion: string;
    associateComponent: ToolComponentReference.t;
    translationMetadata: TranslationMetadata.t;
    supportedTaxonomies: ToolComponentReference.t list;
    properties: Properties.t;
  }[@@deriving yojson]

  val create:
    ?guid: string ->
    name: string ->
    ?organization: string ->
    ?product: string ->
    ?productSuite: string ->
    ?shortDescription: MultiformatMessageString.t ->
    ?fullDescription: MultiformatMessageString.t ->
    ?fullName: string ->
    ?version: string ->
    ?semanticVersion: string ->
    ?dottedQuadFileVersion: string ->
    ?releaseDateUtc: string ->
    ?downloadUri: string ->
    ?informationUri: string ->
    ?globalMessageStrings: MultiformatMessageStringDictionary.t ->
    ?notifications: ReportingDescriptor.t list ->
    ?rules: ReportingDescriptor.t list ->
    ?taxa: ReportingDescriptor.t list ->
    ?locations: ArtifactLocation.t list ->
    ?language: string ->
    ?contents: Contents.t list ->
    ?isComprehensive: bool ->
    ?localizedDataSemanticVersion: string ->
    ?minimumRequiredLocalizedDataSemanticVersion: string ->
    ?associateComponent: ToolComponentReference.t ->
    ?translationMetadata: TranslationMetadata.t ->
    ?supportedTaxonomies: ToolComponentReference.t list ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module Address: sig
  type t = {
    absoluteAddress: int;
    relativeAddress: int;
    length: int;
    kind: string;
    name: string;
    fullyQualifiedName: string;
    offsetFromParent: int;
    index: int;
    parentIndex: int;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?absoluteAddress: int ->
    ?relativeAddress: int ->
    ?length: int ->
    ?kind: string ->
    ?name: string ->
    ?fullyQualifiedName: string ->
    ?offsetFromParent: int ->
    ?index: int ->
    ?parentIndex: int ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module WebRequest: sig
  type t = {
    index: int;
    protocol: string;
    version: string;
    target: string;
    method_: string;
    headers: JsonStringDictionary.t;
    parameters: JsonStringDictionary.t;
    body: ArtifactContent.t;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?index: int ->
    ?protocol: string ->
    ?version: string ->
    ?target: string ->
    ?method_: string ->
    ?headers: JsonStringDictionary.t ->
    ?parameters: JsonStringDictionary.t ->
    ?body: ArtifactContent.t ->
    ?properties: Properties.t ->
    unit -> t

  val default: t

end

module WebResponse: sig
  type t = {
    index: int;
    protocol: string;
    version: string;
    statusCode: int;
    reasonPhrase: string;
    headers: JsonStringDictionary.t;
    body: ArtifactContent.t;
    noResponseReceived: bool;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?index: int ->
    ?protocol: string ->
    ?version: string ->
    ?statusCode: int ->
    ?reasonPhrase: string ->
    ?headers: JsonStringDictionary.t ->
    ?body: ArtifactContent.t ->
    ?noResponseReceived: bool ->
    ?properties: Properties.t ->
    unit -> t

  val default: t

end

module SpecialLocations: sig
  type t = {
    displayBase: ArtifactLocation.t;
    properties: Properties.t;
  } [@@deriving yojson]

  val create:
    ?displayBase: ArtifactLocation.t ->
    ?properties: Properties.t ->
    unit -> t

  val default: t
end

module Run: sig
  type t = {
    tool: Tool.t;
    invocations: Invocation.t list;
    conversion: Conversion.t;
    language: string;
    versionControlProvenance: VersionControlDetails.t list;
    originalUriBaseIds: ArtifactLocationDictionary.t;
    artifacts: Artifact.t list;
    logicalLocations: LogicalLocation.t list;
    graphs: Graph.t list;
    results: Sarif_result.t list;
    automationDetails: RunAutomationDetails.t;
    runAggregates: RunAutomationDetails.t list;
    baselineGuid: string;
    redactionToken: string list;
    defaultEncoding: string;
    defaultSourceLanguage: string;
    newlineSequences: string list;
    columnKind: ColumnKind.t;
    externalPropertyFileReferences: ExternalPropertyFileReferences.t;
    threadFlowLocations: ThreadFlowLocation.t list;
    taxonomies: ToolComponent.t list;
    addresses: Address.t list;
    translations: ToolComponent.t list;
    policies: ToolComponent.t list;
    webRequests: WebRequest.t list;
    webResponses: WebResponse.t list;
    specialLocations: SpecialLocations.t;
    properties: Properties.t;
  }
  [@@deriving yojson]

  val create:
    tool: Tool.t ->
    ?invocations: Invocation.t list ->
    ?conversion: Conversion.t ->
    ?language: string ->
    ?versionControlProvenance: VersionControlDetails.t list ->
    ?originalUriBaseIds: ArtifactLocationDictionary.t ->
    ?artifacts: Artifact.t list ->
    ?logicalLocations: LogicalLocation.t list ->
    ?graphs: Graph.t list ->
    ?results: Sarif_result.t list ->
    ?automationDetails:RunAutomationDetails.t ->
    ?runAggregates: RunAutomationDetails.t list ->
    ?baselineGuid: string ->
    ?redactionToken: string list ->
    ?defaultEncoding: string ->
    ?defaultSourceLanguage: string ->
    ?newlineSequences: string list ->
    ?columnKind: ColumnKind.t ->
    ?externalPropertyFileReferences: ExternalPropertyFileReferences.t ->
    ?threadFlowLocations: ThreadFlowLocation.t list ->
    ?taxonomies: ToolComponent.t list ->
    ?addresses: Address.t list ->
    ?translations: ToolComponent.t list ->
    ?policies: ToolComponent.t list ->
    ?webRequests: WebRequest.t list ->
    ?webResponses: WebResponse.t list ->
    ?specialLocations: SpecialLocations.t ->
    ?properties: Properties.t ->
    unit -> t
end

module Schema: sig
  type t = {
    schema: Uri.t;
    version: Version.t;
    runs: Run.t list
  } [@@deriving yojson]

  val create: ?schema: Uri.t -> ?version:Version.t -> runs: Run.t list ->
    unit -> t

end
