# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(COQLIBDIR)/paco/src Paco -R $(EXTRACTDIR) Extract -R ../lib/CompCert compcert
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES := LLVMAst Classes Util Misc AstLib Dom CFG CFGProp Trace MemoryAddress DynamicValues LLVMIO TypeUtil StepSemantics Memory Renaming DeadInstr Transform TopLevel
OLLVMFILES := 

VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vellvm

coq: $(VOFILES)

extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	touch $(EXTRACTDIR)/STAMP


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend



# Directories containing plain Caml code
OCAMLDIRS= $(EXTRACTDIR) $(MLDIR) 

COMMA=,
OCAMLINCLUDES=$(patsubst %,-I %, $(OCAMLDIRS))
print-ocaml-includes:
	@echo $(OCAMLINCLUDES)

OCAMLLIBS := unix,str

.PHONY: clean main.native test qc restore

main.native: 
	@echo "Compiling Vellvm"
	ocamlbuild -r -use-menhir -yaccflag --explain $(OCAMLINCLUDES) -libs $(OCAMLLIBS) main.native

vellvm: main.native
	cp main.native vellvm

test: vellvm
	./vellvm --test-pp-dir ../tests/ll

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	ocamlbuild -clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll


.PHONY: documentation
documentation: doc/coq2html $(VFILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

-include .depend
