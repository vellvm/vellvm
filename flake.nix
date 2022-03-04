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

        version = "vellvm:master";
      in {
        defaultPackage =
          (pkgs.callPackage ./release.nix (coq.ocamlPackages // pkgs.coqPackages // { inherit coq version; })).vellvm;
      });
}
