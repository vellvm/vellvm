# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

OPAMPKGS=coq coq-ext-lib coq-paco coq-ceres coq-flocq coq-mathcomp-ssreflect coq-simple-io coq-itree cppo dune menhir qcheck ocamlbuild

QUICKCHICKDIR=../lib/QuickChick
FLOCQQUICKCHICKDIR=../lib/flocq-quickchick

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract -R $(QUICKCHICKDIR)/src/ QuickChick -I $(QUICKCHICKDIR)/src -I $(QUICKCHICKDIR)/plugin -R $(FLOCQQUICKCHICKDIR) FlocqQuickChick
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILESNUMERIC := Numeric/Archi Numeric/Coqlib Numeric/Integers Numeric/Zbits Numeric/IEEE754_extra Numeric/Floats

COQFILESUTILS := Utils/ParserHelper Utils/Tactics Utils/Util Utils/AListFacts Utils/Error Utils/ListUtil Utils/IntMaps Utils/NMaps\
		Utils/Monads Utils/StateMonads Utils/MonadEq1Laws Utils/MonadExcLaws\
		Utils/MonadReturnsLaws Utils/PropT Utils/RefineProp\
		Utils/PostConditions Utils/TFor Utils/NoFailure Utils/NonEmpty Utils/Default Utils/OptionUtil Utils/MapMonadExtra\
		Utilities

COQFILESSYNTAX := Syntax/DataLayout Syntax/LLVMAst Syntax/AstLib Syntax/CFG\
		Syntax/Traversal Syntax/DynamicTypes Syntax/TypToDtyp\
		Syntax/TypeUtil\
		Syntax/Scope Syntax/SurfaceSyntax\
		Syntax

COQFILESSEMANTICS := Semantics/MemoryAddress Semantics/Memory/Sizeof Semantics/GepM Semantics/Memory/MemBytes\
		Semantics/Memory/Overlaps Semantics/Memory/FiniteProvenance Semantics/Memory/StoreId\
		Semantics/VellvmIntegers Semantics/Memory/ErrSID \
		Semantics/DynamicValues Semantics/LLVMEvents Semantics/LLVMParams\
		Utils/ITreeRaise Semantics/ItreeRaiseMReturns Utils/Raise\
		Semantics/MemoryParams Semantics/SerializationParams\
		Semantics/IntrinsicsDefinitions\
		Semantics/Denotation Semantics/InterpretationStack Semantics/TopLevel\
		Semantics/Lang Semantics/InfiniteToFinite\
		Handlers/Intrinsics Handlers/Local Handlers/Global Handlers/Stack\
		Handlers/Pick Handlers/UndefinedBehaviour Handlers/OOM\
		Handlers/Serialization Handlers/SerializationTheory\
		Handlers/MemPropT\
		Handlers/MemoryModel Handlers/MemoryInterpreters Handlers/MemoryModelImplementation\
		Handlers/MemoryHelpers\
		Handlers/Handlers\
		Semantics

COQFILESANALYSIS := Analysis/Iteration Analysis/Kildall Analysis/Dom Analysis/DomKildall Analysis/ssa Analysis/DomId 

COQFILESQC := Syntax/TypeUtil QC/Utils QC/GenAST QC/ShowAST QC/ReprAST QC/QCVellvm

COQFILESTHEORY := Syntax/ScopeTheory\
		Theory/StatePredicates\
		Theory/ContainsUB\
		Theory/Refinement Theory/InterpreterMCFG Theory/InterpreterCFG\
		Theory/ExpLemmas Theory/InstrLemmas Theory/DenotationTheory\
		Theory/LocalFrame\
		Theory/TopLevelRefinements Theory/SymbolicInterpreter\
		Utils/NoEvent Utils/Commutation\
		Theory

COQFILESOPT    := Transformations/Transform\
		Transformations/EquivExpr Transformations/BlockFusion Transformations/DeadCodeElimination

COQFILESVIR      := $(COQFILESNUMERIC) $(COQFILESUTILS) $(COQFILESSYNTAX) $(COQFILESSEMANTICS)
COQFILESCOMPILER := $(COQFILESVIR) $(COQFILESANALYSIS)
COQFILESALL      := $(COQFILESCOMPILER) $(COQFILESTHEORY) $(COQFILESOPT) $(COQFILESQC)

VFILES  := $(COQFILESALL:%=coq/%.v)
VOFILES := $(COQFILESALL:%=coq/%.vo)
QCVOFILES := $(COQFILESQC:%=coq/%.vo)

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
	$(MAKE) quickchick flocq-quickchick $(VOFILES)

.PHONY: qc-tests
qc-tests: rm-qc-test-vo coq $(QCVOFILES)

.PHONY: rm-qc-test-vo
rm-qc-test-vo:
	rm -f coq/QC/QCVellvm.vo

.PHONY: opam
opam:
	opam install $(OPAMPKGS)

.PHONY: coqinterp
coqinterp: $(COQFILESVIR:%=coq/%.vo)

.PHONY: quickchick
quickchick:
	$(MAKE) -C $(QUICKCHICKDIR) compat
	$(MAKE) -C $(QUICKCHICKDIR)

.PHONY: flocq-quickchick
flocq-quickchick: quickchick
	make -C $(FLOCQQUICKCHICKDIR)

.PHONY: update-quickchick
update-quickchick:
	git submodule update -- $(QUICKCHICKDIR)

.PHONY: update-flocq-quickchick
update-flocq-quickchick:
	git submodule update -- $(FLOCQQUICKCHICKDIR)

.PHONY: update-submodules
update-submodules: update-quickchick update-flocq-quickchick

.PHONY: extracted
extracted: .depend
	$(MAKE) quickchick $(EXTRACTDIR)/STAMP $(VOFILES)

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	patch -p0 < CRelationClasses.mli.patch
	./fix-extraction.sh
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
	chmod u+w vellvm

.PHONY: test
test: vellvm
	./vellvm -test

.PHONY: print-includes
print-includes:
	@echo $(COQINCLUDES)

.PHONY: clean
clean: extractedclean
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	dune clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.ml

.PHONY: distclean
distclean: clean
	make -C $(QUICKCHICKDIR) clean
	make -C $(FLOCQQUICKCHICKDIR) clean

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

include .depend
