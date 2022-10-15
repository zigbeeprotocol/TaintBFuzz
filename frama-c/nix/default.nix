# paramaterised derivation with dependencies injected (callPackage style)
{ pkgs, stdenv, src ? ../., opam2nix, ocaml ? pkgs.ocaml-ng.ocamlPackages_4_08.ocaml, plugins ? { } }:

let mydir = builtins.getEnv("PWD");
   mk-opam-selection = { name, opamSrc?{}, ... }: {
      inherit ocaml;
      src = opamSrc;
      selection = "${mydir}/${name}-${ocaml.version}-opam-selection.nix";
    };
     opamPackages =
      [ "ocamlfind" "zarith" "ocamlgraph" "yojson" "zmq"
        "ppx_import" "ppx_deriving" "ppx_deriving_yojson"
        "coq=8.13.0" "alt-ergo=2.2.0"
        "why3=1.5.0" "why3-coq=1.5.0"
        "menhir=20211012"
        "easy-format=1.3.2"
      ];
    # only pure nix packages. See mk_deriv below for adding opam2nix packages
    mk_buildInputs = { nixPackages ? [] } :
    [ pkgs.gnugrep pkgs.gnused  pkgs.autoconf pkgs.gnumake pkgs.gcc pkgs.ncurses pkgs.time pkgs.python3 pkgs.perl pkgs.file pkgs.which pkgs.dos2unix] ++ nixPackages;
    # Extends the call to stdenv.mkDerivation with parameters common for all
    # frama-c derivations
    mk_deriv = args:
      let my_opam_packages =
            if args?opamPackages then
              opamPackages ++ args.opamPackages
            else opamPackages
          ;
          opam-selection = mk-opam-selection args;
          buildInputs = args.buildInputs ++ opam2nix.buildInputs opam-selection;
      in
        stdenv.mkDerivation (
          args //
          {
            # Disable Nix's GCC hardening
            hardeningDisable = [ "all" ];
            inherit buildInputs;
          })
        //
        { gen-opam-selection =
            opam2nix.resolve opam-selection my_opam_packages; }
    ;
in

pkgs.lib.makeExtensible
(self: {
  inherit src mk_buildInputs opamPackages mk_deriv;
  buildInputs = mk_buildInputs {};
  installed = self.main.out;
  main = mk_deriv {
        name = "frama-c";
        src = self.src;
        buildInputs =self.buildInputs;
        outputs = [ "out" "build_dir" ];
        postPatch = ''
               patchShebangs .
        '';
        configurePhase = ''
               unset CC
               autoconf
               ./configure --prefix=$out
        '';
        buildPhase = ''
                make -j 4
        '';
        installPhase = ''
               make install
               mkdir -p $build_dir
               tar -cf $build_dir/dir.tar .
               pwd > $build_dir/old_pwd
        '';
        setupHook = pkgs.writeText "setupHook.sh" ''
          addFramaCPath () {
            if test -d "$1/lib/frama-c/plugins"; then
              export FRAMAC_PLUGIN="''${FRAMAC_PLUGIN:-}''${FRAMAC_PLUGIN:+:}$1/lib/frama-c/plugins"
              export OCAMLPATH="''${OCAMLPATH:-}''${OCAMLPATH:+:}$1/lib/frama-c/plugins"
            fi

            if test -d "$1/lib/frama-c"; then
              export OCAMLPATH="''${OCAMLPATH:-}''${OCAMLPATH:+:}$1/lib/frama-c"
            fi

            if test -d "$1/share/frama-c/"; then
              export FRAMAC_EXTRA_SHARE="''${FRAMAC_EXTRA_SHARE:-}''${FRAMAC_EXTRA_SHARE:+:}$1/share/frama-c"
            fi

          }

          addEnvHooks "$targetOffset" addFramaCPath
        '';
  };

  lint = mk_deriv {
        name = "frama-c-lint";
        src = self.src;
        opamPackages = [ "ocp-indent=1.8.1" "headache=1.05"];
        buildInputs =
          self.mk_buildInputs { nixPackages = [ pkgs.bc pkgs.clang_10 ]; };
        outputs = [ "out" ];
        postPatch = ''
               patchShebangs .
        '';
        configurePhase = ''
               unset CC
               autoconf
               ./configure --prefix=$out
        '';
        buildPhase = ''
               make lint
               make stats-lint
               STRICT_HEADERS=yes make check-headers
        '';
        installPhase = ''
               true
        '';
  };

  doc = mk_deriv {
        name = "frama-c-doc";
        buildInputs = self.buildInputs;
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postPatch = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
          true
        '';
        buildPhase = ''
               make doc
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "main";};

  tests = mk_deriv {
        name = "frama-c-test";
        buildInputs = self.buildInputs;
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postUnpack = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
           true
        '';
        buildPhase = ''
               make clean_share_link
               make create_share_link
               make tests -j4 PTESTS_OPTS="-error-code -j 4"
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "main"; };

  build-distrib-tarball = mk_deriv {
        name = "frama-c-build-distrib-tarball";
        src = self.src;
        buildInputs = self.buildInputs;
        opamPackages = [ "headache=1.05" ];
        outputs = [ "out" ];
        configurePhase = ''
               unset CC
               autoconf
               ./configure --prefix=$out
        '';
        buildPhase = ''
                make DISTRIB="frama-c-archive" src-distrib
                tar -zcf frama-c-tests-archive.tar.gz tests src/plugins/*/tests
        '';
        installPhase = ''
               tar -C $out --strip-components=1 -xzf frama-c-archive.tar.gz
               tar -C $out -xzf frama-c-tests-archive.tar.gz
        '';
  };

  build-from-distrib-tarball = mk_deriv {
        name = "frama-c-build-from-distrib-tarball";
        doCheck = true;
        buildInputs = self.buildInputs;
        opamPackages = self.build-distrib-tarball.opamPackages;
        src = self.build-distrib-tarball.out ;
        outputs = [ "out" ];
        postPatch = ''
               patchShebangs .
        '';
        configurePhase = ''
               unset CC
               autoconf
               ./configure --prefix=$out
        '';
        buildPhase = ''
                make -j 4
        '';
        checkPhase = ''
               make clean_share_link
               make create_share_link
               make tests -j4 PTESTS_OPTS="-error-code -j 4"
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "build-distrib-tarball"; };

  wp-qualif = mk_deriv {
        name = "frama-c-wp-qualif";
        buildInputs = self.mk_buildInputs { };
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postUnpack = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
           true
        '';
        buildPhase = ''
               make clean_share_link
               make create_share_link
               mkdir home
               HOME=$(pwd)/home
               why3 config detect
               make src/plugins/wp/tests/test_config_qualif
               export FRAMAC_WP_CACHE=replay
               export FRAMAC_WP_CACHEDIR=${plugins.wp-cache.src}
               bin/ptests.opt -error-code -config qualif src/plugins/wp/tests
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "main"; };

  aorai-prove = mk_deriv {
        name = "frama-c-aorai-prove";
        buildInputs = self.mk_buildInputs { };
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postUnpack = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "test_config*" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
           true
        '';

        buildPhase = ''
          make clean_share_link
          make create_share_link
          mkdir home
          HOME=$(pwd)/home
          why3 config detect
          make src/plugins/aorai/tests/ptests_config
          export AORAI_WP_CACHE=replay
          export AORAI_WP_CACHEDIR=${plugins.wp-cache.src}
          make PTESTS_OPTS="-error-code" aorai-test-prove
        '';

        installPhase = ''
          true
        '';
  } // { other-opam-selection = "main"; };

  eva-tests = mk_deriv {
        name = "frama-c-eva-tests";
        buildInputs = self.mk_buildInputs { };
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postUnpack = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
            true
        '';
        buildPhase = ''
               make clean_share_link
               make create_share_link
               export CONFIGS="equality bitwise symblocs gauges octagon"
               src/plugins/value/vtests -j 4 -error-code
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "main"; };

  e-acsl-tests-dev = mk_deriv {
        name = "frama-c-e-acsl-tests-dev";
        buildInputs = self.mk_buildInputs { nixPackages = [ pkgs.gmp pkgs.getopt ]; };
        build_dir = self.main.build_dir;
        src = self.main.build_dir + "/dir.tar";
        sourceRoot = ".";
        postUnpack = ''
               find . \( -name "Makefile*" -or -name ".depend" -o -name "ptests_config" -o -name "config.status" \) -exec bash -c "t=\$(stat -c %y \"\$0\"); sed -i -e \"s&$(cat $build_dir/old_pwd)&$(pwd)&g\" \"\$0\"; touch -d \"\$t\" \"\$0\"" {} \;
        '';
        configurePhase = ''
           true
        '';
        buildPhase = ''
               make clean_share_link
               make create_share_link
               make E_ACSL_TESTS PTESTS_OPTS="-error-code" DEV=yes
        '';
        installPhase = ''
               true
        '';
  } // { other-opam-selection = "main"; };

  internal = mk_deriv {
        name = "frama-c-internal";
        src = self.src;
        opamPackages = [ "xml-light" ];
        buildInputs =
          self.mk_buildInputs
            { nixPackages =
                [ pkgs.getopt pkgs.libxslt pkgs.libxml2 pkgs.autoPatchelfHook
                  pkgs.swiProlog stdenv.cc.cc.lib ];
            };
        genassigns_src = plugins.genassigns.src;
        frama_clang_src = plugins.frama-clang.src;
        pathcrawler_src = plugins.pathcrawler.src;
        mthread_src = plugins.mthread.src;
        caveat_importer_src = plugins.caveat-importer.src;
        acsl_importer_src = plugins.acsl-importer.src;
        volatile_src = plugins.volatile.src;
        security_src = plugins.security.src;
        context_from_precondition_src = plugins.context-from-precondition.src;
        metacsl_src = plugins.meta.src;
        postPatch = ''
               patchShebangs .
        '';
        postUnpack = ''
           cp -r --preserve=mode "$genassigns_src" "$sourceRoot/src/plugins/genassigns"
           chmod -R u+w -- "$sourceRoot/src/plugins/genassigns"
           # cp -r --preserve=mode "$frama_clang_src" "$sourceRoot/src/plugins/frama-clang"
           # chmod -R u+w -- "$sourceRoot/src/plugins/frama-clang"
           cp -r --preserve=mode "$pathcrawler_src" "$sourceRoot/src/plugins/pathcrawler"
           chmod -R u+w -- "$sourceRoot/src/plugins/pathcrawler"
           cp -r --preserve=mode "$mthread_src" "$sourceRoot/src/plugins/mthread"
           chmod -R u+w -- "$sourceRoot/src/plugins/mthread"
           cp -r --preserve=mode "$caveat_importer_src" "$sourceRoot/src/plugins/caveat-importer"
           chmod -R u+w -- "$sourceRoot/src/plugins/caveat-importer"
           cp -r --preserve=mode "$volatile_src" "$sourceRoot/src/plugins/volatile"
           chmod -R u+w -- "$sourceRoot/src/plugins/volatile"
           cp -r --preserve=mode "$acsl_importer_src" "$sourceRoot/src/plugins/acsl-importer"
           chmod -R u+w -- "$sourceRoot/src/plugins/acsl-importer"
           echo IN_FRAMA_CI=yes > "$sourceRoot/in_frama_ci"
           cp -r --preserve=mode "$context_from_precondition_src" "$sourceRoot/src/plugins/context-from-precondition"
           chmod -R u+w -- "$sourceRoot/src/plugins/context-from-precondition"
           cp -r --preserve=mode "$security_src" "$sourceRoot/src/plugins/security"
           chmod -R u+w -- "$sourceRoot/src/plugins/security"
           '';

        configurePhase = ''
               unset CC
               autoconf
               ./configure --prefix=$out
        '';
        buildPhase = ''
                make unpack-eclipse
                sed -i src/plugins/pathcrawler/extern/eclipseCLP/RUNME -e "s/chmod 2755/chmod 755/g"
                rm src/plugins/pathcrawler/extern/eclipseCLP/lib/x86_64_linux/dbi_mysql.so
                rm src/plugins/pathcrawler/extern/eclipseCLP/lib/x86_64_linux/ic.so
                rm src/plugins/pathcrawler/extern/eclipseCLP/lib/x86_64_linux/bitmap.so
                rm -fr src/plugins/pathcrawler/extern/eclipseCLP/lib/i386_linux
                rm src/plugins/pathcrawler/src/generator/COLIBRI/float_util_sparc_sunos5.so
                rm src/plugins/pathcrawler/src/generator/COLIBRI/float_util_i386_linux.so.*
                rm src/plugins/pathcrawler/share/bin/float_util_sparc_sunos5.so
                find src/plugins/pathcrawler -name '*_i386_*.so' -delete
                autoPatchelf src/plugins/pathcrawler/
                make -j 4
                ln -sr src/plugins/pathcrawler/share share/pc
                # Setup Why3
                mkdir home
                HOME=$(pwd)/home
                why3 config detect
                # Setup WP related
                export CAVEAT_IMPORTER_NIX_MODE=yes
                export GENASSIGNS_NIX_MODE=yes
                export FRAMAC_WP_CACHE=replay
                export FRAMAC_WP_CACHEDIR=${plugins.wp-cache.src}
                make tests -j4 PTESTS_OPTS="-error-code -j 4"
        '';
        installPhase = ''
               make install
        '';
  };

})
