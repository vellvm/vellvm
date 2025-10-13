{
  description = "Vellvm, a formal specification and interpreter for LLVM";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/master";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
    coinduction-repo = {
      url = "github:damien-pous/coinduction";
      flake = false;
    };
    relation-algebra-repo = {
      url = "github:damien-pous/relation-algebra";
      flake = false;
    };
    ctrees = {
      url = "github:Chobbes/ctrees/rocq9.0";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter, coinduction-repo, relation-algebra-repo, ctrees }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lib = pkgs.lib;
        rocq = pkgs.rocq-core;
        rocqPkgs = pkgs.rocqPackages_9_0;
        coqPkgs = pkgs.coqPackages_9_0;

        coinduction = rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "damien-pous";
              pname = "coinduction";
              version = "coinduction:master";
              src = coinduction-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq pkgs.coq dune_3 stdlib rocq-core findlib ];
              propagatedBuildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ rocq ];
            }) { inherit rocq; } ;

        relation-algebra = rocqPkgs.callPackage
          ( { rocq, stdenv }:
            rocqPkgs.mkRocqDerivation {
              owner = "damien-pous";
              pname = "relation-algebra";
              version = "relation-algebra:master";
              src = relation-algebra-repo;

              buildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ ocaml camlp5 rocq pkgs.coq dune_3 stdlib rocq-core findlib ];
              propagatedBuildInputs =
                with rocqPkgs;
                with coqPkgs;
                with rocq.ocamlPackages;
                [ rocq ];
            }) { inherit rocq; } ;

        version = "vellvm:master";
      in rec {
        packages = {
          default = (pkgs.callPackage ./release.nix ({ nix-filter = nix-filter.lib; perl = pkgs.perl; coq = pkgs.coq; ctrees = ctrees.packages.${system}.default; inherit rocq version rocqPkgs coqPkgs coinduction relation-algebra; })).vellvm;
        };

        defaultPackage = packages.default;

        app.default = flake-utils.lib.mkApp { drv = packages.default; };

        checks = {
          
          vellvm-test-suite =
            pkgs.stdenv.mkDerivation {
              name = "vellvm-test-suite";
              src = ./.;
              meta = {
                description = "Run the simple suite of vellvm tests";
              };
              buildInputs = [packages.default];
              installPhase = ''
              cd src
              ${packages.default}/bin/vellvm -test-suite
              if [[ $? == 0 ]]; then
                mkdir $out
              fi
              '';
            };
            
          org-lint =
            pkgs.stdenv.mkDerivation {
              name = "org-linting";
              src = ./.;
              meta = {
                description = "Ensure that links are still valid within some important org files for artifact submissions :).";
              };
              buildInputs = [pkgs.emacs];
              installPhase = ''
 ${pkgs.emacs}/bin/emacs --batch -f package-initialize --eval "(add-hook 'org-mode-hook  
      (lambda ()
          (let* ((file-name (current-buffer))
            (Col1 'Line)
            (Col2 'Trust)
            (Col3 'Warning)
            (lint-report (org-lint '(link-to-local-file)))
          )
          (princ (format \"file: %s\n%6s%6s%8s\n\" file-name Col1 Col2 Col3))
          (dolist (element lint-report)
           (setq report (car (cdr element)))
           (princ (format \"%6s%6s %7s\n\" (seq-elt report 0) (seq-elt report 1) (seq-elt report 2)))
          )
          (if (not (null lint-report))
            (kill-emacs 1))
          )))" MemoryTour.org

          if [[ $? == 0 ]]; then
             mkdir $out
          fi
              '';
            };
        };

        devShells = {
          # Include a fixed version of clang in the development environment for testing.
          default = pkgs.mkShell {
            inputsFrom = [ packages.default];
            buildInputs = [ pkgs.clang_19
                            pkgs.coq # Needed to make proof general happy for development.
                            pkgs.llvmPackages_19.libllvm
                            rocq.ocamlPackages.utop
                            rocq.ocamlPackages.bisect_ppx
                            rocq.ocamlPackages.ppxlib
                            pkgs.util-linux
                          ];
            shellHook = ''
              unset COQPATH
            '';
          };
        };

        devShell = devShells.default;
      });
}
