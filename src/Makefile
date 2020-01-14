# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

ITREEDIR=../lib/InteractionTrees

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract -R $(ITREEDIR)/theories/ ITree 
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESINTERP := Numeric/Archi Numeric/Coqlib Numeric/Fappli_IEEE_extra Numeric/Integers Numeric/Floats\
									Util PropT Error LLVMAst AstLib Dom CFG CFGProp MemoryAddress DynamicTypes DynamicValues\
									LLVMEvents TypeUtil IntrinsicsDefinitions\
									Handlers/Intrinsics Handlers/Local Handlers/Global Handlers/Stack Handlers/Pick Handlers/Memory Handlers/UndefinedBehaviour\
									Denotation TransformTypes TopLevel

COQFILESOPT    := Transformations/Renaming Transformations/DeadInstr Transformations/Transform Transformations/Traversal Transformations/Transformation\
									ParserHelper Refinement Environment TopLevelRefinements

OLLVMFILES :=

VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)


VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vellvm

interp:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coqinterp
	$(MAKE) extracted
	$(MAKE) vellvm

coq: $(VOFILES)

coqinterp: $(COQFILESINTERP:%=coq/%.vo)

itrees:
	git submodule update --remote -- $(ITREEDIR)
	make -C $(ITREEDIR)

.PHONY: extracted itrees 
extracted: $(EXTRACTDIR)/STAMP $(VOFILES)

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	patch -p0 < CRelationClasses.mli.patch
	touch $(EXTRACTDIR)/STAMP


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: itrees $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test qc restore

EXE=_build/default/ml/main.exe

$(EXE): extracted ml/dune ml/extracted/dune
	@echo "Compiling Vellvm"
	dune build ml/main.exe 

vellvm: $(EXE)
	cp $(EXE) vellvm

test: vellvm
	./vellvm --test

print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	make -C $(ITREEDIR) clean

doc/coq2html: 
	make -C ../lib/coq2html
	cp ../lib/coq2html doc/coq2html
	chmod +x doc/coq2html

.PHONY: documentation
documentation: doc/coq2html $(VFILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -d doc/html doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp ../lib/coq2html/coq2html.css ../lib/coq2html/coq2html.js doc/html/

-include .depend
