# Rocq source files: root

This directory contains all `rocq` source files, with the exception of the extraction entry points.

It gathers files per-folder covering the following categories, and reexport their content into an
eponym local file for easier import:
- `Utils.v`: range of utilities independent from LLVM IR
- `Syntax.v`: deeply embedded syntax and related files
- `Numeric.v`: arithmetic-related files inherited in parts from the CompCert and Flocq projects
- `Semantics.v`: core of the semantics, building a denotation of LLVM IR files


