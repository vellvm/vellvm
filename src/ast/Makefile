.PHONY: clean

BASENAME := Ollvm_ast
V := $(BASENAME).v
VO := $(BASENAME).vo
ML := $(BASENAME).mli $(BASENAME).ml
LIB := $(BASENAME).cmo $(BASENAME).cmx

all: $(VO) $(ML) $(LIB)

$(VO) : $(V)
	coqc $(V)

$(ML): $(VO) Extract_$(V)
	coqc Extract_$(V)

$(BASENAME).cmo: $(ML)
	ocamlfind ocamlc -c $(ML)

$(BASENAME).cmx: $(ML)
	ocamlfind opt -c $(ML)

clean:
	rm -rf $(ML) *.cm* *.o
	rm -rf *.vo *.glob
