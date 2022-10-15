#!/usr/bin/env bash
set -eu

printf '(** Eva public API.

   The main modules are:
   - Analysis: run the analysis.
   - Results: access analysis results, especially the values of expressions
      and memory locations of lvalues at each program point.

   The following modules allow configuring the Eva analysis:
   - Parameters: change the configuration of the analysis.
   - Eva_annotations: add local annotations to guide the analysis.
   - Builtins: register ocaml builtins to be used by the cvalue domain
       instead of analysing the body of some C functions.

   Other modules are for internal use only. *)\n'

printf '\n(* This file is generated. Do not edit. *)\n'

for i in "$@"
do
    file=$(basename $i)
    module=${file%.*}
    printf '\nmodule %s: sig\n' ${module^}
    awk '/\[@@@ api_start\]/{flag=1;next} /\[@@@ api_end\]/{flag=0} flag{ print (NF ? "  ":"") $0 }' $i
    printf 'end\n'
done
