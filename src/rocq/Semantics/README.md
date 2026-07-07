This folder contains the definition of the semantics of VIR programs.
Its content gets re-exported in `/rocq` as a module `Semantics` for easier external use.

VIR programs are denoted as interaction trees over a family of uninterpreted LLVM events
(`LLVMEvents.v`). The semantics is then obtained by interpreting these events away one
family at a time via the handlers in `Handlers/`. The whole development is parameterized
by a bundle of typeclasses (`Interfaces/`) capturing the memory-related components;
concrete instances live in `Implementations/`.

## Basic definitions

- `EOU.v`                    sum type for pure computations that may raise an error, run out of memory, or trigger UB
- `VellvmIntegers.v`         `VMemInt`/`VInt` typeclass interfaces for the integer operations used by the semantics
- `VellvmFloats.v`           `VFloat` typeclass interface for the floating-point operations
- `DynamicValues.v`          dynamic values (`dvalue`) computed by programs, and the operations over them
- `LLVMEvents.v`             inventory of the LLVM events (`GlobalE`, `LocalE`, `StackE`, `MemoryE`, `DrawE`, calls, intrinsics, exceptions, UB, OOM, failure, debug) and the event signatures (`CFGEtop`, `MCFGEtop`, ...) used at each interpretation level
- `MemoryBytes.v`            byte-level manipulation of integers (extraction/concatenation of bytes)

## Parameters of the semantics

- `Interfaces/`              typeclass interfaces the semantics is parameterized by:
  - `Provenance.v`           provenances and allocation identifiers
  - `Address.v`              addresses, overlap, and pointer/integer conversions
  - `IPtr.v`                 integers of pointer size (`intptr`)
  - `Sizeof.v`               size and alignment of dynamic types
  - `Memory.v`               memory model interface (`MemoryModelState`, `MemoryModelPrimitives`)
  - `Params.v`               `Params`, the bundle aggregating all of the above; most definitions take a `Context {Pa : Params}`
- `Implementations/`         concrete instances of these interfaces:
  - `IPtrFinite.v`           finite (64-bit) `intptr`, may run out of memory
  - `IPtrInfinite.v`         unbounded `intptr` (backed by `Z`)
  - `Provenance.v`, `Address.v`, `Sizeof.v`  default instances
  - `Memory.v`               executable memory model
  - `ParamsV.v`              `ParamsV`, the default `Params` bundle (parameterized by the choice of `IPtr`)

## Denotation

- `Operations/`              semantics of the individual operations: `Gep.v`, `Select.v`, `Compare.v`, `Conversion.v` (re-exported by `Operations.v`)
- `IntrinsicsDefinitions.v`  declarations and semantics of the supported LLVM intrinsics
- `Denotation.v`             representation function: VIR syntax to uninterpreted interaction trees
- `Libraries.v`              denotation of natively supported library functions (`putchar`, `puts`, ...) linked against programs

## Interpretation

- `Handlers/`                one handler per event family, each interpreting its events into a more concrete itree:
  `Global.v`, `Local.v`, `Stack.v` (state over the corresponding environments), `Intrinsics.v`, `Memory.v`,
  `Draw.v` (draws of an arbitrary `dvalue` at a type; the executable handler picks the canonical default),
  `LLVMExceptions.v` (currently not built). Re-exported by `Handlers.v`.
- `InterpretationStack.v`    composes the handlers into the full interpretation stack (`interp_mcfg`) and provides the `SemNotations` module
- `TopLevel.v`               plugs everything together: linking, construction of the global environment, `denote_vellvm`, and the executable `interpreter` extracted to OCaml
