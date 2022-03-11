{
  description = "Vellvm, a formal specification and interpreter for LLVM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-21.11";
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
            });

        version = "vellvm:master";
      in {
        defaultPackage =
          (pkgs.callPackage ./release.nix (coq.ocamlPackages // coqPkgs // { inherit coq version; })).vellvm;
      });
}

  
