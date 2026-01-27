{ lib,
  nix-filter,
  version ? null,
  coq,
  rocq,
  rocqPkgs,
  coqPkgs,
  perl,
  ... }:

{ vellvm =
    rocqPkgs.mkRocqDerivation {
      pname = "vellvm";
      owner = "vellvm";

      inherit version;

      buildInputs =
        with rocq.ocamlPackages;
        [ rocq
          coq # Needed to make QuickChick happy for now...
          dune_3
          perl
        ] ++
        # These ocaml packages have to come from rocq.ocamlPackages to
        # avoid disagreements between ocaml compiler versions.
        [ ocaml
          ocamlbuild
          findlib
          menhir
          qcheck
          cppo
        ];

      propagatedBuildInputs =
        # Rocq libraries
        with rocqPkgs;
        with coqPkgs;
        with rocq.ocamlPackages;
        [ ExtLib
          paco
          ITree
          flocq
          ceres
          simple-io
          zarith
          QuickChick
        ] ++
        # These ocaml packages have to come from rocq.ocamlPackages to
        # avoid disagreements between ocaml compiler versions.
        [ ocaml
          ocamlbuild
          findlib
          menhir
          qcheck
          cppo
        ];

      src =
        # Some filtering to ignore files that are unimportant for the build.
        # Helps with caching and preventing rebuilds when, e.g., only
        # a README changed.
        nix-filter {
          root = ./.;
          include = [
            ./lib
            ./src
            ./src/Makefile
            (nix-filter.matchExt "v")
            (nix-filter.matchExt "ml")
            (nix-filter.matchExt "patch")
            (nix-filter.matchName "dune")
            (nix-filter.matchName "dune-project")
          ];

          exclude = [
            ./src/doc
            ./src/cachix-push.sh
            ./utilities
            ./qc-test-failures
            (nix-filter.matchExt "org")
            (nix-filter.matchExt "md")
            (nix-filter.matchExt "txt")
            (nix-filter.matchExt "yml")
            (nix-filter.matchExt "cff")
            (nix-filter.matchName "README")
            ./.gitignore
            ./.git
          ];
        };

      buildPhase = ''
  runHook preBuild
  unset COQPATH
  make -C src/
  make -C src/ frontend
  runHook postBuild
  '';

      installPhase = ''
  runHook preInstall
  unset COQPATH
  mkdir -p $out/bin
  install src/vellvm $out/bin/vellvm
  install src/frontend $out/bin/frontend
  COQLIBINSTALL=$out/lib/coq/${rocq.rocq-version}/user-contrib make -C src/ install
  runHook postInstall
  '';

      meta = {
        description = "Vellvm, a formal specification and interpreter for LLVM";
        license = lib.licenses.gpl3Only;
      };
    };
}
