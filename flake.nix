{
  description = "Vellvm, a formal specification and interpreter for LLVM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        coq = pkgs.coq;

        coqPkgs = pkgs.coqPackages.overrideScope'
          (self: super:
            { ITree = super.ITree.overrideAttrs
              (s : { version = "DeepSpec:78bf12c326e52f4d64bf03c43b937f7397559cbf";
                     src = fetchTarball {
                       url = "https://github.com/DeepSpec/InteractionTrees/archive/78bf12c326e52f4d64bf03c43b937f7397559cbf.zip";
                       sha256 = "0sfrrkrhr51qnc6rpxr2mq4fvhvwbgp453r5q4nafba32lhfima2";
                     };
                   });

              coq-ext-lib = super.coq-ext-lib.overrideAttrs
              (s : { version = "0.11.3";
                     src = fetchTarball {
                       url = "https://github.com/coq-community/coq-ext-lib/archive/refs/tags/v0.11.3.zip";
                       sha256 = "1w99nzpk72lffxis97k235axss5lmzhy5z3lga2i0si95mbpil42";
                     };
                   });
            });

        version = "vellvm:master";
      in {
        defaultPackage =
          (pkgs.callPackage ./release.nix (coq.ocamlPackages // coqPkgs // { inherit coq version; })).vellvm;
      });
}
