This folder contains the files related to the internal syntax of VIR programs.
Its content gets re-exported in `/coq` as a module `Syntax` for easier external use.

- `LLVMAst.v`       the VIR front AST. Our parser of native llvm syntax returns an element of this AST
- `CFG.v`           the VIR internal AST as used for the semantics.
- `Traversal.v`     typeclass-based mechanism to define operations manipulating the whole ast painlessly
- `DynamicTypes.v`  definition of the dynamic types manipulated internally
- `TypToDtyp.v`     conversion of static types into dynamic types
- `AstLib.v`        utilities related to the ast (decidable eq, serialization, ..)
- `SurfaceSyntax.v` print-only (for now) notations displaying a LLVM-like surface syntax for VIR
- `Scope.v`         elementary definitions related to the scope of vir's programs w.r.t. both registers and labels
- `ScopeTheory.v`   reasoning principles about the scope-related definitions from `Scope.v`

Currently DEPRECATED:
- `TypUtil.v` historic reasoning on types and their normalization
