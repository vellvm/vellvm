{ lib,
  nix-filter,
  mkCoqDerivation,
  version ? null,
  coq,
  dune_3,
  perl,
  # All of these ocaml packages should probably come from the coq
  # version, or there will be disagreements between compiler versions.
  ocaml ? coq.ocaml,
  ocamlbuild ? coq.ocamlPackagse.ocamlbuild,
  findlib ? coq.ocamlPackagse.findlib,
  menhir ? coq.ocamlPackages.menhir,
  qcheck ? coq.ocamlPackages.qcheck,
  cppo ? coq.ocamlPackages.cppo,
  QuickChick,
  mathcomp, mathcomp-ssreflect, coq-ext-lib, paco, ITree, flocq, ceres, simple-io, zarith, ... }:

{ vellvm =
    mkCoqDerivation {
      namePrefix = [ "coq" ];
      pname = "vellvm";
      owner = "vellvm";

      inherit version;

      buildInputs =
        [ coq
          dune_3
          perl
        ] ++
        # These ocaml packages have to come from coq.ocamlPackages to
        # avoid disagreements between ocaml compiler versions.
        [ ocaml
          ocamlbuild
          findlib
          menhir
          qcheck
          cppo
        ];

      propagatedBuildInputs =
        # Coq libraries
        [ mathcomp
          mathcomp-ssreflect
          coq-ext-lib
          paco
          ITree
          flocq
          ceres
          simple-io
          zarith
          QuickChick
        ] ++
        # These ocaml packages have to come from coq.ocamlPackages to
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
            (nix-filter.matchName "README")
            ./.gitignore
            ./.git
          ];
        };

      buildPhase = ''
  runHook preBuild
  make -C src/
  make -C src/ frontend
  runHook postBuild
  '';

      installPhase = ''
  runHook preInstall
  mkdir -p $out/bin
  install src/vellvm $out/bin/vellvm
  install src/frontend $out/bin/frontend
  COQLIBINSTALL=$out/lib/coq/${coq.coq-version}/user-contrib make -C src/ install
  runHook postInstall
  '';

      meta = {
        description = "Vellvm, a formal specification and interpreter for LLVM";
        license = lib.licenses.gpl3Only;
      };
    };
}
