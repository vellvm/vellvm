# Vellvm: Release Notes

## 3.0 (2026/07/07)

### Major Changes

- Complete revamp of the infrastructure: both the axiomatization of the memory
  model (notion of address, provenance, memory state, ...) and the
  parameterization of the semantics (infinite/finite pointer) now rely on type
  classes rather than modules and functors.

- Construction of the memory handler into two passes: a generic implementation
  in a dedicated free monad (`memM`) composed with a monad morphism from `memM`
  to either a deterministic stateful monad (to derive the infrastructure), or to
  a richer monad supporting non-determinism (not yet built in this release).

- Removal of `undef` values, and consequently of under-defined values
  (`uvalue`). We look forwards and move towards an `undef`-free world, in the
  spirit of Lobo et al.'s "Towards Removing Undef Values From LLVM IR"
  (PLDI'26).

- Extended the support for exceptions.

- Various bug fixes around the semantics of floats.

- New stepping debugger available with the interpreter.

- Meta-theory is temporarily unplugged, and intended to be progressively
  reincorporated in upcoming releases.

- New website! Sources in the `docs` directory, hosted at [vellvm.github.io/vellvm](https://vellvm.github.io/vellvm/).

### Minor Changes

- Cutting off some dependencies: QuickChick, QuickCheck, Ceres.

- Simplification and improvement of the code revolving around testing.
