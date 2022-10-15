(**************************************************************************)
(*                                                                        *)
(*  This file was originally part of Menhir                               *)
(*                                                                        *)
(*  François Pottier and Yann Régis-Gianas, INRIA Rocquencourt            *)
(*                                                                        *)
(*  Copyright 2005 Institut National de Recherche en Informatique et      *)
(*  en Automatique. All rights reserved. This file is distributed         *)
(*  under the terms of the Q Public License version 1.0, with the         *)
(*  change described in the file licenses/Q_MODIFIED_LICENSE.             *)
(*                                                                        *)
(*  File modified by CEA (Commissariat à l'énergie atomique et aux        *)
(*                        énergies alternatives).                         *)
(*                                                                        *)
(**************************************************************************)

(** Signature for the {!Hptmap} module *)

(** Functions on hptmaps are divided into two module types:
    - [Shape] contains only functions that do not create or modify a map:
      comparisons, tests, finding an element or a key, iterators.
    - [S] includes [Shape], plus functions that create and modify maps:
      adding or removing elements, filter and maps, merge of two maps. *)

(** Some functions of this module may optionally use internal caches. It is
    the responsibility of the use to choose whether or not to use a cache,
    and whether this cache will be garbage-collectable by OCaml. *)
type cache_type =
  | NoCache
  (** The results of the function will not be cached. *)
  | PersistentCache of string
  (** The results of the function will be cached, and the function that uses
      the cache is a permanent closure (at the toplevel of an OCaml module).*)
  | TemporaryCache of string
  (** The results of the function will be cached, but the function itself
      is a local function which is garbage-collectable. *)

(** This module type contains only functions that do not create or modify maps.
    These functions can be applied to any maps from a given type [key],
    regardless of the type of values bound. *)
module type Shape = sig
  (** Type of the keys. *)
  type key

  (** Type of the maps from type [key] to type ['v]. *)
  type 'v map

  (** Bijective function. The ids are positive. *)
  val id: 'v map -> int

  val hash: 'v map -> int
  val equal : 'v map -> 'v map -> bool
  val compare: ('v -> 'v -> int) -> 'v map -> 'v map -> int
  val pretty: 'v Pretty_utils.formatter -> 'v map Pretty_utils.formatter

  val is_empty : 'v map -> bool
  (** [is_empty m] returns [true] if and only if the map [m] defines no
      bindings at all. *)

  val is_singleton: 'v map -> (key * 'v) option
  (** [is_singleton m] returns [Some (k, d)] if [m] is a singleton map
      that maps [k] to [d]. Otherwise, it returns [None]. *)

  val on_singleton: (key -> 'v -> bool) -> 'v map -> bool
  (** [on_singleton f m] returns [f k d] if [m] is a singleton map
      that maps [k] to [d]. Otherwise, it returns false. *)

  val cardinal: 'v map -> int
  (** [cardinal m] returns [m]'s cardinal, that is, the number of keys it
      binds, or, in other words, its domain's cardinal. *)

  val find : key -> 'v map -> 'v
  val find_check_missing: key -> 'v map -> 'v
  (** Both [find key m] and [find_check_missing key m] return the value
      bound to [key] in [m], or raise [Not_found] is [key] is unbound.
      [find] is optimised for the case where [key] is bound in [m], whereas
      [find_check_missing] is more efficient for the cases where [m]
      is big and [key] is missing. *)

  val find_key : key -> 'v map -> key
  (** This function is useful where there are multiple distinct keys that
      are equal for [Key.equal]. *)

  val mem :  key -> 'v map -> bool
  (** [mem k m] returns true if [k] is bound in [m], and false otherwise. *)

  val min_binding: 'v map -> key * 'v
  val max_binding: 'v map -> key * 'v

  (** {2 Iterators} *)

  val iter : (key -> 'v -> unit) -> 'v map -> unit
  (** [iter f m] applies [f] to all bindings of the map [m]. *)

  val for_all: (key -> 'v -> bool) -> 'v map -> bool
  (** [for_all p m] returns true if all the bindings of the map [m] satisfy
      the predicate [p]. *)

  val exists: (key -> 'v -> bool) -> 'v map -> bool
  (** [for_all p m] returns true if at least one binding of the map [m] satisfies
      the predicate [p]. *)

  val fold : (key -> 'v -> 'b -> 'b) -> 'v map -> 'b -> 'b
  (** [fold f m seed] invokes [f k d accu], in turn, for each binding from
      key [k] to datum [d] in the map [m]. Keys are presented to [f] in
      increasing order according to the map's ordering. The initial value of
      [accu] is [seed]; then, at each new call, its value is the value
      returned by the previous invocation of [f]. The value returned by
      [fold] is the final value of [accu]. *)

  val fold_rev : (key -> 'v -> 'b -> 'b) -> 'v map -> 'b -> 'b
  (** [fold_rev] performs exactly the same job as [fold], but presents keys
      to [f] in the opposite order. *)

  val cached_fold :
    cache_name:string ->
    temporary:bool ->
    f:(key -> 'v -> 'b) ->
    joiner:('b -> 'b -> 'b) ->
    empty:'b ->
    'v map -> 'b

  val fold2_join_heterogeneous:
    cache:cache_type ->
    empty_left:('b map -> 'c) ->
    empty_right:('a map -> 'c) ->
    both:(key -> 'a -> 'b -> 'c) ->
    join:('c -> 'c -> 'c) ->
    empty:'c ->
    'a map -> 'b map ->
    'c
  (** [fold2_join_heterogeneous ~cache ~empty_left ~empty_right ~both
        ~join ~empty m1 m2] iterates simultaneously on [m1] and [m2]. If a subtree
      [t] is present in [m1] but not in [m2] (resp. in [m2] but not in [m1]),
      [empty_right t] (resp. [empty_left t]) is called. If a key [k] is present
      in both trees, and bound to [v1] and [v2] respectively, [both k v1 v2] is
      called. If both trees are empty, [empty] is returned. The values of type
      ['b] returned by the auxiliary functions are merged using [join], which is
      called in an unspecified order. The results of the function may be cached,
      depending on [cache]. *)

  (** {2 Binary predicates} *)

  (** Existential ([||]) or universal ([&&]) predicates. *)
  type predicate_type = ExistentialPredicate | UniversalPredicate

  (** Does the given predicate hold or not. [PUnknown] indicates that the result
      is uncertain, and that the more aggressive analysis should be used. *)
  type predicate_result = PTrue | PFalse | PUnknown

  val binary_predicate:
    cache_type ->
    predicate_type ->
    decide_fast:('a map -> 'b map -> predicate_result) ->
    decide_fst:(key -> 'a -> bool) ->
    decide_snd:(key -> 'b -> bool) ->
    decide_both:(key -> 'a -> 'b -> bool) ->
    'a map -> 'b map -> bool
  (** [binary_predicate] decides whether some relation holds between two maps,
      according to the functions:
      - [decide_fst] and [decide_snd], called on keys present only
        in the first or second map respectively;
      - [decide_both], called on keys present in both trees;
      - [decide_fast], called on entire maps as an optimization. As its name
        implies, it must be fast. If can prevent the analysis of some maps by
        directly returning [PTrue] or [PFalse] when possible. Otherwise, it
        returns [PUnknown] and the maps are analyzed by calling the functions
        above on each binding.

      If the predicate is existential, then the function returns [true] as soon
      as one of the call to the functions above returns [true]. If the predicate
      is universal, the function returns [true] if all calls to the functions
      above return [true].

      The computation of this relation can be cached, according to [cache_type].
  *)

  val symmetric_binary_predicate:
    cache_type ->
    predicate_type ->
    decide_fast:('v map -> 'v map -> predicate_result) ->
    decide_one:(key -> 'v -> bool) ->
    decide_both:(key -> 'v -> 'v -> bool) ->
    'v map -> 'v map -> bool
  (** Same as [binary_predicate], but for a symmetric relation. [decide_fst]
      and [decide_snd] are thus merged into [decide_one]. *)

  val decide_fast_inclusion: 'v map -> 'v map -> predicate_result
  (** Function suitable for the [decide_fast] argument of [binary_predicate],
      when testing for inclusion of the first map into the second. If the two
      arguments are equal, or the first one is empty, the relation holds. *)

  val decide_fast_intersection: 'v map -> 'v map -> predicate_result
  (** Function suitable for the [decide_fast] argument of
      [symmetric_binary_predicate] when testing for a non-empty intersection
      between two maps. If one map is empty, the intersection is empty.
      Otherwise, if the two maps are equal, the intersection is non-empty. *)

  (** {2 Misc} *)

  val clear_caches: unit -> unit
  (** Clear all the persistent caches used internally by the functions of this
      module. Those caches are not project-aware, so this function must be
      called at least each time a project switch occurs. *)
end


(** Signature for hptmaps from hash-consed trees to values. *)
module type S = sig
  (** type of the keys *)
  type key

  (** type of the values *)
  type v
  type prefix

  include Shape with type key := key
  include Datatype.S_with_collections with type t = v map

  val self : State.t

  val empty : t
  (** the empty map *)

  val singleton: key -> v -> t
  (** [singleton k d] returns a map whose only binding is from [k] to [d]. *)

  val add : key -> v -> t -> t
  (** [add k d m] returns a map whose bindings are all bindings in [m], plus
      a binding of the key [k] to the datum [d]. If a binding already exists
      for [k], it is overridden. *)

  val remove : key -> t -> t
  (** [remove k m] returns the map [m] deprived from any binding involving
      [k]. *)

  val replace : (v option -> v option) -> key -> t -> t
  (** [replace f k m] returns a map whose bindings are all bindings in [m],
      except for the key [k] which is:
      - removed from the map if [f o] = None
      - bound to v' if [f o] = Some v'
        where [o] is (Some v) if [k] is bound to [v] in [m], or None if [k]
        is not bound in [m]. *)

  (** {2 Filters and maps} *)

  val filter: (key -> bool) -> t -> t
  (** [filter f t] keep only the bindings of [m] whose key verify [f].  *)

  val map : (v -> v) -> t -> t
  (** [map f m] returns the map obtained by composing the map [m] with the
      function [f]; that is, the map $k\mapsto f(m(k))$. *)

  val map': (key -> v -> v option) -> t -> t
  (** Same as [map], except if [f k v] returns [None]. In this case, [k] is not
      bound in the resulting map. *)

  val cached_map :
    cache:string * int ->
    temporary:bool ->
    f:(key -> v -> v) ->
    t -> t

  val replace_key: decide:(key -> v -> v -> v) -> key map -> t -> bool * t
  (** [replace_key ~decide shape map] substitute keys in [map] according to
      [shape]: it returns the [map] in which all bindings from [key] to [v] such
      that [key] is bound to [key'] in [shape] are replaced by a binding from
      [key'] to [v]. If the new key [key'] was already bound in the map, or if
      two keys are replaced by a same key [key'], the [decide] function is used
      to compute the final value bound to [key'].
      The returned boolean indicates whether the map has been modified: it is
      false if the intersection between [shape] and [map] is empty. *)

  (** {2 Merge of two maps} *)

  type empty_action = Neutral | Absorbing | Traversing of (key -> v -> v option)

  val merge :
    cache:cache_type ->
    symmetric:bool ->
    idempotent:bool ->
    decide_both:(key -> v -> v -> v option) ->
    decide_left:empty_action ->
    decide_right:empty_action ->
    t -> t -> t
  (** Merge of two trees, parameterized by a merge function.
      If [symmetric] holds, the function must verify [merge x y = merge y x].
      If [idempotent] holds, the function must verify [merge x x = x].
      For each key [k] present in both trees, and bound to [v1] and [v2] in the
      left and the right tree respectively, [decide_both k v1 v2] is called. If
      the decide function returns [None], the key will not be in the resulting
      map; otherwise, the new value computed will be bound to [k].
      The [decide_left] action is performed to the left subtree [t] when a right
      subtree is empty (and conversely for the [decide_right] action when a left
      subtree is empty):
      - Neutral returns the subtree [t] unchanged;
      - Absorbing returns the empty tree;
      - (Traversing f) applies the function [f] to each binding of the remaining
        subtree [t] (see [map']).

      The results of the function may be cached, depending on [cache]. If a
      cache is used, then the merge functions must be pure. *)

  val generic_join :
    cache:cache_type ->
    symmetric:bool ->
    idempotent:bool ->
    decide:(key -> v option -> v option -> v) ->
    t -> t -> t
  (** Merge of two trees, parameterized by the [decide] function. If [symmetric]
      holds, the function must verify [decide key v1 v2 = decide key v2 v1]. If
      [idempotent] holds, the function must verify
      [decide k (Some x) (Some x) = x]. *)

  val join :
    cache:cache_type ->
    symmetric:bool ->
    idempotent:bool ->
    decide:(key -> v -> v -> v) ->
    t -> t -> t
  (** Same as [generic_merge], but we assume that
      [decide key None (Some v) = decide key (Some v) None = v] holds. *)

  val inter :
    cache:cache_type ->
    symmetric:bool ->
    idempotent:bool ->
    decide:(key -> v -> v -> v option) ->
    t -> t -> t
  (** Intersection of two trees, parameterized by the [decide] function. If the
      [decide] function returns [None], the key will not be in the resulting
      map. Keys present in only one map are similarly unmapped in the result.
  *)

  val inter_with_shape: 'a map -> t -> t
  (** [inter_with_shape s m] keeps only the elements of [m] that are also
      bound in the  map [s]. No caching is used, but this function is more
      efficient than successive calls to {!remove} or {!add} to build the
      resulting map. *)

  val diff_with_shape: 'a map -> t -> t
  (** [diff_with_shape s m] keeps only the elements of [m] that are not
      bound in the map [s]. No caching is used, but this function is more
      efficient than successive calls to {!remove} or {!add} to build the
      resulting map. *)

  val partition_with_shape: 'a map -> t -> t * t
  (** [partition_with_shape s m] returns two maps [inter, diff] such that:
      - [inter] contains the elements of [m] bound in the shape [s];
      - [diff] contains the elements of [m] not bound in the shape [s]. *)

  (** {2 Misc} *)

  val from_shape: (key -> 'a -> v) -> 'a map -> t
  (** Build an entire map from another map indexed by the same keys.
      More efficient than just performing successive {!add} the elements
      of the other map *)

  val compositional_bool: t -> bool
  (** Value of the compositional boolean associated to the tree, as computed
      by the {!Compositional_bool} argument of the functor. *)

  val pretty_debug: Format.formatter -> t -> unit
  (** Verbose pretty printer for debug purposes. *)

  (** {2 Prefixes and subtree; Undocumented} *)

  type subtree
  exception Found_prefix of prefix * subtree * subtree
  val comp_prefixes : t -> t -> unit
  val pretty_prefix : prefix -> Format.formatter -> t -> unit
  val find_prefix : t -> prefix -> subtree option
  val hash_subtree : subtree -> int
  val equal_subtree : subtree -> subtree -> bool
end
