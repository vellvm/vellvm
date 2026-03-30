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
        rocq = rocqPkgs.rocq-core;
        rocqPkgs = pkgs.rocqPackages_9_1;
        coqPkgs = pkgs.coqPackages_9_1;
        libllvm = pkgs.llvmPackages_20.libllvm;
        clang = pkgs.clang_20;
        version = "vellvm:master";
      in rec {
        packages = {
          default = (pkgs.callPackage ./release.nix ({ nix-filter = nix-filter.lib; perl = pkgs.perl; coq = coqPkgs.coq; inherit rocq version rocqPkgs coqPkgs; })).vellvm;
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
              buildInputs = [packages.default libllvm clang];
              installPhase = ''
              cd src
              ${packages.default}/bin/vellvm -l libll/rust-intrinsics.ll -test
              if [[ $? == 0 ]]; then
                mkdir $out
              fi
              '';
            };
            
 #          org-lint =
 #            pkgs.stdenv.mkDerivation {
 #              name = "org-linting";
 #              src = ./.;
 #              meta = {
 #                description = "Ensure that links are still valid within some important org files for artifact submissions :).";
 #              };
 #              buildInputs = [pkgs.emacs];
 #              installPhase = ''
 # ${pkgs.emacs}/bin/emacs --batch -f package-initialize --eval "(add-hook 'org-mode-hook  
 #      (lambda ()
 #          (let* ((file-name (current-buffer))
 #            (Col1 'Line)
 #            (Col2 'Trust)
 #            (Col3 'Warning)
 #            (lint-report (org-lint '(link-to-local-file)))
 #          )
 #          (princ (format \"file: %s\n%6s%6s%8s\n\" file-name Col1 Col2 Col3))
 #          (dolist (element lint-report)
 #           (setq report (car (cdr element)))
 #           (princ (format \"%6s%6s %7s\n\" (seq-elt report 0) (seq-elt report 1) (seq-elt report 2)))
 #          )
 #          (if (not (null lint-report))
 #            (kill-emacs 1))
 #          )))" MemoryTour.org

 #          if [[ $? == 0 ]]; then
 #             mkdir $out
 #          fi
 #              '';
 #            };
        };

        devShells = {
          # Include a fixed version of clang in the development environment for testing.
          default = pkgs.mkShell {
            inputsFrom = [ packages.default];
            buildInputs = [ clang
                            coqPkgs.coq # Needed to make proof general happy for development.
                            libllvm
                            pkgs.lldb
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
