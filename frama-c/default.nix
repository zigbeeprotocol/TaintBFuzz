# standalone derivation, for nix-build, nix-shell, etc
{ pkgs ? import <nixpkgs> {} }:
let
    src = builtins.fetchGit {
            "url" = ./.git;
            "name" = "frama-c";
            "rev" = "ffa925f404779a3a0c4aacff5bd78b1c502def11";
            "ref" = "test-nix-fetchGit";
    };
 in

pkgs.callPackage ./nix/default.nix {
	opam2nix = pkgs.callPackage ../Frama-CI/opam2nix-packages.nix {};
        src = src;
}
