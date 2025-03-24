The folder defines the semantic model and reference interpreter of VIR.

- `IntrinsicsDefinitions.v` : Declaration of the prototypes of supported intrinsics, and of the semantics of the pure ones
- `DynamicValues.v`         : Definition of the dynamic values manipulated by the semantics
- `MemoryAddress.v`         : Signature of memory addresses manipulated, concretely implemented by each memory model
- `LLVMEvents.v`            : Inventory of all events parameterizing the itrees representing VIR programs
- `Denotation.v`            : Representation functions of syntactic VIR constructs as uninterpreted itrees
- `InterpretationStack.v`   : Stack of partial (and full) interpreters introducing progressively the semantics of the events 
- `TopLevel.v`              : Definition of the semantic model of VIR, as well as of its reference interpreter
