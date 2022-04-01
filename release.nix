{ lib,
  mkCoqDerivation,
  version ? null,
  coq,
  dune_3,
  # All of these ocaml packages should probably come from the coq
  # version, or there will be disagreements between compiler versions.
  ocaml ? coq.ocaml,
  ocamlbuild ? coq.ocamlPackagse.ocamlbuild,
  findlib ? coq.ocamlPackagse.findlib,
  menhir ? coq.ocamlPackages.menhir,
  qcheck ? coq.ocamlPackages.qcheck,
  cppo ? coq.ocamlPackages.cppo,
  mathcomp, mathcomp-ssreflect, coq-ext-lib, paco, ITree, flocq, ceres, simple-io, zarith, ... }:

{ vellvm =
    mkCoqDerivation {
      namePrefix = [ "coq" ];
      pname = "vellvm";
      owner = "vellvm";

      inherit version;

      propagatedBuildInputs =
        [ coq
          dune_3
        ] ++
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

      src = ./.;

      buildPhase = ''
  make -C src/
  '';

      installPhase = ''
  mkdir -p $out/bin
  install src/vellvm $out/bin/vellvm
  '';

      meta = {
        description = "Vellvm, a formal specification and interpreter for LLVM";
        license = lib.licenses.gpl3Only;
      };
    };
}
