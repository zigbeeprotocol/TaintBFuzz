#To copy in other repository
{ password}:

let
    src = builtins.fetchGit {
            "url" = "https://bobot:${password}@git.frama-c.com/frama-c/Frama-CI.git";
            "name" = "Frama-CI";
            "rev" = "e33541f771435c6b1014acf1b042f569deadb663";
            "ref" = "master";
    };
    pkgs = import "${src}/pkgs.nix" {};
 in
 {
  src = src;
  compiled = pkgs.callPackage "${src}/compile.nix" { inherit pkgs; };
 }
