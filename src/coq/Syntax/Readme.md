This folder contains the files related to the internal syntax of VIR programs.

- `LLVMAst.v`      the VIR front AST. Our parser of native llvm syntax returns an element of this AST.
- `CFG.v`          the VIR internal AST as used for the semantics. 
- `Traversal.v`    typeclass-based mechanism to define operations manipulating the whole ast painlessly
- `DynamicTypes.v` definition of the dynamic types manipulated internally
- `TypToDtyp.v`    conversion of static types into dynamic types
- `AstLib.v`       utilities related to the ast (decidable eq, serialization, ..)

Currently DEPRECATED:
- `Dom.v`     reasoning about dominators in a graph.
- `TypUtil.v` historic reasoning on types and their normalization
