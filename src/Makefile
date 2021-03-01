# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

ITREEDIR=../lib/InteractionTrees
QUICKCHICKDIR=../lib/QuickChick

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract -R $(ITREEDIR)/theories/ ITree -R $(QUICKCHICKDIR)/src/ QuickChick -I $(QUICKCHICKDIR)/src
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESINTERP := Numeric/Archi Numeric/Coqlib Numeric/Integers Numeric/Zbits Numeric/IEEE754_extra Numeric/Floats\
									Utils/ParserHelper Utils/Tactics Utils/Util Utils/AListFacts Utils/Error\
									Utils/PropT Utils/PostConditions Utils/NoFailure Utils/TFor\
                  Syntax/LLVMAst Syntax/AstLib Syntax/CFG\
									Syntax/Traversal Syntax/Dom Syntax/DynamicTypes Syntax/TypToDtyp\
									Syntax/Scope Syntax/SurfaceSyntax\
									Semantics/MemoryAddress Semantics/DynamicValues Semantics/LLVMEvents Semantics/IntrinsicsDefinitions\
									Handlers/Intrinsics Handlers/Local Handlers/Global Handlers/Stack Handlers/Pick Handlers/UndefinedBehaviour Handlers/Memory Handlers/MemoryTheory Handlers/Handlers\
								  Semantics/Denotation Semantics/InterpretationStack Semantics/TopLevel QC/GenAST QC/QCVellvm

COQFILESTHEORY := Theory/Refinement Theory/InterpreterMCFG Theory/InterpreterCFG Theory/ExpLemmas Theory/InstrLemmas Theory/DenotationTheory\
									Theory/TopLevelRefinements Theory/SymbolicInterpreter\
									Utils/NoEvent Utils/Commutation

COQFILESOPT    := Transformations/Transform
 # Transformations/Renaming Transformations/DeadInstr Transformations/Transformation

OLLVMFILES :=

VFILES  := $(COQFILESINTERP:%=coq/%.v) $(COQFILESTHEORY:%=coq/%.v) $(COQFILESOPT:%=coq/%.v)
VOFILES := $(COQFILESINTERP:%=coq/%.vo) $(COQFILESTHEORY:%=coq/%.vo) $(COQFILESOPT:%=coq/%.vo)

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

update-trees:
	git submodule update -- $(ITREEDIR)

itrees:
	make -C $(ITREEDIR)

quickchick:
	make -C $(QUICKCHICKDIR)

update-quickchick:
	git submodule update -- $(QUICKCHICKDIR)

update-submodules: update-trees update-quickchick

.PHONY: extracted update-trees update-quickchick update-submodules itrees quickchick
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

depend: itrees quickchick $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test qc restore

EXE=_build/default/ml/main.exe

$(EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Vellvm"
	dune build ml/main.exe 

vellvm: $(EXE)
	cp $(EXE) vellvm

test: vellvm
	./vellvm --test

print-includes:
	@echo $(COQINCLUDES)

clean: clean-vellvm clean-itrees
clean-vellvm:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	find $(COQLIBDIR) -name "*.vo" -delete
	find $(COQLIBDIR) -name "*.vio" -delete
	find $(COQLIBDIR) -name "*.vok" -delete
	find $(COQLIBDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
clean-itrees:
	make -C $(ITREEDIR) clean
	make -C $(QUICKCHICKDIR) clean

.PHONY: clean-vellvm clean-itrees

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
