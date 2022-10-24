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
COQMAKEFILE="$(COQBIN)coq_makefile"
MENHIR=menhir
CP=cp

FRONTEND_EXE=_build/default/ml/frontend.exe
COQFILES_FRONTEND := QC/ShowAST QC/ReprAST Utils/ParserHelper
FRONTEND_VOFILES := $(COQFILES_FRONTEND:%=coq/%.vo)

KNOWNTARGETS := CoqMakefile extracted $(EXTRACTDIR)/STAMP interp .depend coq qc-tests opam frontend frontend_exe $(FRONTEND_EXE) distclean update-quickchick update-flocq-quickchick rm-qc-test-vo quickchick flocq-quickchick vellvm test check
SKIPTARGETS := frontend frontend_exe $(FRONTEND_EXE) .depend
KNOWNFILES := Makefile _CoqProject .depend

.DEFAULT_GOAL := all

CoqMakefile: Makefile _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
ifeq ($(MAKECMDGOALS),)
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
else
ifeq ($(filter-out $(SKIPTARGETS),$(MAKECMDGOALS)),)
	@true
else
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
endif
endif

clean-coqmakefile: CoqMakefile
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS)) clean

.PHONY: all invoke-coqmakefile clean-coqmakefile $(KNOWNFILES) vok
all: quickchick flocq-quickchick vok extracted vellvm

.PHONY: interp
interp: coqinterp extracted vellvm

.PHONY: coq
coq: quickchick flocq-quickchick $(VOFILES)

.PHONY: qc-tests
qc-tests: rm-qc-test-vo coq $(QCVOFILES) $(QCVOFILESTEST)

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
extracted: vok $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: vok $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Patching extraction"
	patch -p0 < CRelationClasses.mli.patch
	bash fix-extraction.sh
	touch $(EXTRACTDIR)/STAMP

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

.PHONY: check
check: test

.PHONY: print-includes
print-includes:
	@echo $(COQINCLUDES)

.PHONY: clean
clean: extractedclean clean-coqmakefile
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
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli

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

############
### Facilities for building only the frontend - parser and pretty printer

$(EXTRACTDIR)/FRONTEND_STAMP: $(FRONTEND_VOFILES) $(EXTRACTDIR)/ExtractFrontend.v
	@echo "Extracting Frontend"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/ExtractFrontend.v
	patch -p0 < CRelationClasses.mli.patch
	touch $(EXTRACTDIR)/FRONTEND_STAMP

$(FRONTEND_EXE): $(EXTRACTDIR)/FRONTEND_STAMP ml/dune ml/extracted/dune ml/testing/dune ml/frontend.ml ml/IO.ml
	@echo "Compiling Vellvm (Frontend Only)"
	dune build ml/frontend.exe

.PHONY: frontend
frontend: .depend
	$(MAKE) $(FRONTEND_VOFILES)
	$(MAKE) frontend_exe

.PHONY: frontend_exe
frontend_exe:
	make $(FRONTEND_EXE)
	cp $(FRONTEND_EXE) frontend
	chmod u+w frontend

%: invoke-coqmakefile
	@true
