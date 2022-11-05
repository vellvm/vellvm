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
          default = (pkgs.callPackage ./release.nix (ocamlPkgs // coqPkgs // { nix-filter = nix-filter.lib; perl = pkgs.perl; inherit coq version; })).vellvm;
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
            (lint-report (org-lint))
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
            inputsFrom = [ packages.default ];
            buildInputs = [ pkgs.clang_13 ];
          };
        };

        devShell = devShells.default;
      });
}
