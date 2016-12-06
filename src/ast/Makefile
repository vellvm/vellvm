.PHONY: clean

BASENAME := Ollvm_ast
V := $(BASENAME).v
VO := $(BASENAME).vo
ML := Datatypes.mli Datatypes.ml $(BASENAME).mli $(BASENAME).ml 
LIB := $(BASENAME).cmo $(BASENAME).cmx

all: $(VO) $(ML) $(LIB)

Datatypes.ml Datatypes.mli: Extract_Datatypes.v
	coqc -Q "." "Vellvm" Extract_Datatypes.v

$(VO) : $(V)
	coqc -Q "." "Vellvm" $(V)

$(BASENAME).ml $(BASENAME).mli: $(VO) Extract_$(V)
	coqc -Q "." "Vellvm" Extract_$(V)

$(BASENAME).cmo: $(ML)
	ocamlfind ocamlc -c $(ML)

$(BASENAME).cmx: $(ML)
	ocamlfind opt -c $(ML)

clean:
	rm -rf $(ML) *.cm* *.o
	rm -rf *.vo *.glob
	rm -rf Datatypes.ml*
