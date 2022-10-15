#!/bin/sh -eu

DIR=$(dirname $0)

export FRAMA_CI_NIX=$DIR/frama-ci.nix
export FRAMA_CI=$(nix-instantiate --eval -E "((import <nixos-20.03> {}).callPackage $FRAMA_CI_NIX  { password = \"$TOKEN_FOR_API\";}).src.outPath")

FRAMA_CI=${FRAMA_CI#\"}
FRAMA_CI=${FRAMA_CI%\"}

export NIX_PATH="nixpkgs=$(eval echo $(nix-instantiate --eval -E "with import $FRAMA_CI/pkgs-ref.nix; url"))"
$FRAMA_CI/compile.sh $@
