# Instructions to internalize llvm ir code

Our interpreter allows for linking native llvm ir code via the -L option.
Alternatively, it can be useful to internalize code, notably in order to
formaly reason about this code. The process to do so goes as follows,
illustrated on the `printf.ll` file as example:

1. run `./vellvm -print-ast ./libll/printf.ll` from the `src` directory.
This will generate the file src/output/printf.v.ast 
2. copy the list appearing in the resulting file (by default output/printf.v.ast) to
be the definition of `printf_definition` (warning: it gets large).
3. add a `.` to the end of the list
4. replace all occurrences of slash double-quote (OCaml quoted quotes) 
into double-quote double-quote (Rocq quoted quotes)
5. add its definition to the `PREDEFINED_FUNCTIONS` list in `TopLevel.v`



