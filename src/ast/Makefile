.PHONY: clean

BASENAME := Ollvm_ast
V := $(BASENAME).v
VO := $(BASENAME).vo
ML := Datatypes.mli Datatypes.ml $(BASENAME).mli $(BASENAME).ml 
HS := $(BASENAME).hs
LIB := $(BASENAME).cmo $(BASENAME).cmx

all: $(VO) $(ML) $(HS) $(LIB)

Datatypes.ml Datatypes.mli: Extract_Datatypes.v
	coqc -Q "." "Vellvm" Extract_Datatypes.v

$(VO) : $(V)
	coqc -Q "." "Vellvm" $(V)

$(BASENAME).ml $(BASENAME).mli: $(VO) Extract_$(V)
	coqc -Q "." "Vellvm" Extract_$(V)

$(BASENAME).hs: $(VO) Extract_Haskell_$(V)
	coqc -Q "." "Vellvm" Extract_Haskell_$(V)

$(BASENAME).cmo: $(ML)
	ocamlfind ocamlc -c $(ML)

$(BASENAME).cmx: $(ML)
	ocamlfind opt -c $(ML)

clean:
	rm -rf $(ML) *.hs *.cm* *.o
	rm -rf *.vo *.glob
	rm -rf Datatypes.ml*
