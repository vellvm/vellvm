{
  description = "Vellvm, a formal specification and interpreter for LLVM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter }:
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
            });

        version = "vellvm:master";
      in rec {
        packages = {
          default = (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { nix-filter = nix-filter.lib; inherit coq version; })).vellvm;
        };

        defaultPackage = packages.default;

        app.default = flake-utils.lib.mkApp { drv = packages.default; };

        devShells = {
          # Include a fixed version of clang in the development environment for testing.
          default = pkgs.mkShell {
            inputsFrom = [ packages.default ];
            buildInputs = [ pkgs.clang_13 ];
          };
        };

        devShell = devShells.default;
      });
}
