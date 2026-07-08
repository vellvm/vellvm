# Vellvm Developer Notes

Useful breadcrumbs for Vellvm developers.

## Makefile 

The `src/Makefile` follows the model suggested by [RocqMakefile](https://rocq-prover.org/doc/V9.2.0/refman/practical-tools/utilities.html#building-a-rocq-project-with-rocq-makefile).

For compability with `opam` it supports a `make install` target that installs 
- the Rocq development so that it becomes available to users with the `Vellvm` module prefix
- the `vellvm` executable 

## Opam Metadata

### rocq-vellvm.opam

The file `rocq-vellvm.opam` contains the metadata needed for an opam release, following the guidelines outlined 
in the [Coq opam packaging](https://rocq-prover.org/docs/opam-packaging) web pages. Follow the instructions
there to update `rocq-vellvm.opam`.

In particular, this file should be kept up to date with respect to the library dependencies.

### rocq-vellvm.install

Says where to put the `vellvm` executable.  It is needed by `opam-installer` to place the executable in the right `.opam` switch directory.


## Github Actions & CI

The file `.github/workflows/vellvm.yml` specifies the CI testing.  It uses 

- [Docker-Rocq Action](https://github.com/marketplace/actions/docker-coq-action)

- see: [this list](https://hub.docker.com/r/coqorg/coq/) for available Rocq + OCaml combinations

- The file `rocq-vellvm.opam` specifies the opam dependencies installed by the workflow.

Since we need to maintain an `opam`-compatible build/deploy system, using that
infrastructure for CI too makes sense.
