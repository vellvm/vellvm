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
        coq = pkgs.coq_8_15;
        ocamlPkgs = coq.ocamlPackages;
        coqPkgs = pkgs.coqPackages_8_15.overrideScope'
          (self: super:
            { simple-io = super.simple-io.overrideAttrs
                (s : { version = "1.7.0";
                       src = fetchTarball {
                         url = "https://github.com/Lysxia/coq-simple-io/archive/refs/tags/1.7.0.zip";
                         sha256 = "1a1q9x2abx71hqvjdai3n12jxzd49mhf3nqqh3ya2ssl2lj609ci";
                       };
                       propagatedBuildInputs = s.propagatedBuildInputs ++ [ ocamlPkgs.cppo ocamlPkgs.zarith ocamlPkgs.findlib ];
                       meta.broken = false;
                     });

              flocq = super.flocq.overrideAttrs
                (s : { version = "4.0.0";
                       src = fetchTarball {
                         url = "https://gitlab.inria.fr/flocq/flocq/-/archive/flocq-4.0.0/flocq-flocq-4.0.0.zip";
                         sha256 = "07bj7fha14iifnh0s17q0kxq9s1g5rq18l1swbydz29c3bmz3i41";
                       };
                });
            });

        version = "vellvm:master";
      in {
        defaultPackage =
          (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { inherit coq version; })).vellvm;
      });
}
