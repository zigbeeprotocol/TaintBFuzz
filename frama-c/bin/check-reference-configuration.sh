#!/bin/bash -eu

# Displays the current working configuration of OCaml dependencies of Frama-C,
# comparing them with the one in `reference-configuration.md`.

if ! type "opam" > /dev/null; then
    opam="NOT"
else
    opam="$(opam --version)"
    if [[ $opam =~ ^([0-9+]).([0-9+]) ]]; then
        major="${BASH_REMATCH[1]}"
        minor="${BASH_REMATCH[2]}"
        if [[ "$major" -eq 2 && "$minor" -eq 0 ]]; then
            echo "warning: opam > 2.1 expected, got $major.$minor."
            echo "         Suggested commands may not work properly."
        fi
    else
        echo "warning: unknown opam version."
        echo "         Suggested commands may not work properly."
    fi
fi

if ! type "ocaml" > /dev/null; then
    ocaml="NOT"
else
    ocaml=$(ocaml -vnum)
fi

version_via_opam() {
    v=$(opam info -f installed-version "$1" 2>/dev/null)
    if [ "$v" = "" ] || [ "$v" = "--" ]; then
        echo "NOT"
    else
        echo "$v"
    fi
}

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
refconf="$SCRIPT_DIR/../reference-configuration.md"

packages=$(grep '^- [^ ]*\.' "$refconf" | sed 's/^- //' | sed 's/ .*//')

bold=$(tput bold)
normal=$(tput sgr0)

has_any_diffs=0
# Check OCaml version separately (not same syntax as the packages)
working_ocaml=$(grep "\- OCaml " "$refconf" | sed 's/.*OCaml //')
if [ "$working_ocaml" != "$ocaml" ]; then
    echo -n "warning: OCaml ${bold}${ocaml}${normal} installed, "
    echo "expected ${bold}${working_ocaml}${normal}"
    has_any_diffs=1
fi

all_packages=""
for package in $packages; do
    name=${package%%.*}
    all_packages+=" $package"
    working_version=$(echo "$package" | sed 's/^[^.]*\.//')
    if [ "$opam" != "NOT" ]; then
        actual_version=$(version_via_opam "$name")
    else
        echo "error: opam not found."
        exit 1
    fi
    if [ "$working_version" != "$actual_version" ]; then
        has_any_diffs=1
        echo -n "warning: $name ${bold}${actual_version}${normal} installed, "
        echo "expected ${bold}${working_version}${normal}"
    fi
done

echo "All packages checked."
if [ $has_any_diffs -ne 0 ]; then
    echo "Useful commands:"
    echo "    opam switch create ${working_ocaml}"
    echo "    opam install$all_packages"
    echo "    rm -f ~/.why3.conf && why3 config detect"
fi
