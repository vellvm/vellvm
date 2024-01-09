# Vellvm Developer Notes

Useful breadcrumbs for Vellvm developers.

## Makefile 

The `src/Makefile` follows the model suggested by [CoqMakefile](https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile).

For compability with `opam` it supports a `make install` target that installs 
- the Coq development so that it becomes available to users with the `Vellvm` module prefix
- the `vellvm` executable 

## Opam Metadata

### coq-vellvm.opam

The file `coq-vellvm.opam` contains the metadata needed for an opam release, following the guidelines outlined 
in the [Coq opam packaging](https://coq.inria.fr/opam-packaging.html) web pages. Follow the instructions
there to update `coq-vellvm.opam`.

In particular, this file should be kept up to date with respect to the library dependencies.

### coq-vellvm.install

Says where to put the `vellvm` executable.  It is needed by `opam-installer` to place the executable in the right `.opam` switch directory.


## Github Actions & CI

The file `.github/workflows/vellvm.yml` specifies the CI testing.  It uses 

- [Docker-Coq Action](https://github.com/marketplace/actions/docker-coq-action)

- see: [this list](https://hub.docker.com/r/coqorg/coq/) for available Coq + ocaml combinations

- The file `coq-vellvm.opam` specifies the opam dependencies installed by the workflow.



Since we need to maintain an `opam`-compatible build/deploy system, using that
infrastructure for CI too makes sense.
