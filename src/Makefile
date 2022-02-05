# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

OPAMPKGS=coq coq-ext-lib coq-paco coq-ceres coq-flocq coq-itree dune menhir ocamlbuild qcheck

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESNUMERIC := Numeric/Archi Numeric/Coqlib Numeric/Integers Numeric/Zbits Numeric/IEEE754_extra Numeric/Floats

COQFILESUTILS := Utils/ParserHelper Utils/Tactics Utils/Util Utils/AListFacts Utils/ListUtil Utils/Error\
		Utils/PropT Utils/PostConditions Utils/TFor Utils/NoFailure\
		Utilities

COQFILESSYNTAX := Syntax/LLVMAst Syntax/AstLib Syntax/CFG\
		Syntax/Traversal Syntax/DynamicTypes Syntax/TypToDtyp\
		Syntax/Scope Syntax/SurfaceSyntax\
		Syntax

COQFILESSEMANTICS := Semantics/MemoryAddress Semantics/DynamicValues Semantics/LLVMEvents\
		Semantics/IntrinsicsDefinitions\
		Handlers/Intrinsics Handlers/Local Handlers/Global Handlers/Stack\
		Handlers/Pick Handlers/Memory Handlers/MemoryTheory\
		Handlers/Handlers\
		Semantics/Denotation Semantics/InterpretationStack Semantics/TopLevel\
		Semantics

COQFILESANALYSIS := Analysis/Iteration Analysis/Kildall Analysis/Dom Analysis/DomKildall Analysis/ssa Analysis/DomId

COQFILESTHEORY := Syntax/ScopeTheory\
									Theory/StatePredicates\
									Theory/Refinement Theory/InterpreterMCFG Theory/InterpreterCFG\
									Theory/ExpLemmas Theory/InstrLemmas Theory/DenotationTheory\
									Theory/TopLevelRefinements Theory/SymbolicInterpreter\
									Utils/NoEvent Utils/Commutation\
							    Theory

COQFILESOPT    := Transformations/Transform\
		Transformations/EquivExpr Transformations/BlockFusion Transformations/DeadCodeElimination

COQFILESVIR      := $(COQFILESNUMERIC) $(COQFILESUTILS) $(COQFILESSYNTAX) $(COQFILESSEMANTICS)
COQFILESCOMPILER := $(COQFILESVIR) $(COQFILESANALYSIS)
COQFILESALL      := $(COQFILESCOMPILER) $(COQFILESTHEORY) $(COQFILESOPT)

VFILES  := $(COQFILESALL:%=coq/%.v)
VOFILES := $(COQFILESALL:%=coq/%.vo)

.PHONY: all
all: .depend
	$(MAKE) coq
	$(MAKE) extracted
	$(MAKE) vellvm

.PHONY: interp
interp: .depend
	$(MAKE) coqinterp
	$(MAKE) extracted
	$(MAKE) vellvm

.PHONY: coq
coq: .depend
	$(MAKE) $(VOFILES)

.PHONY: opam
opam:
	opam install $(OPAMPKGS)

.PHONY: coqinterp
coqinterp: $(COQFILESVIR:%=coq/%.vo)

.PHONY: extracted
extracted: .depend
	$(MAKE) $(EXTRACTDIR)/STAMP $(VOFILES)

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

.depend: $(VFILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

EXE=_build/default/ml/main.exe

$(EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Vellvm"
	dune build ml/main.exe

vellvm: $(EXE)
	cp $(EXE) vellvm

.PHONY: test
test: vellvm
	./vellvm --test

.PHONY: print-includes
print-includes:
	@echo $(COQINCLUDES)

.PHONY: clean
clean:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vellvm

.PHONY: distclean
distclean: clean

include .depend
