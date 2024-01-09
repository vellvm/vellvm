## Vellvm Project Makefile

## Follows the model suggested by:
## https://coq.inria.fr/refman/practical-tools/utilities.html#building-a-coq-project-with-coq-makefile

#### Build Configuration Information

######## Tested/Recommended versions of Coq and OCaml
########    If these are changed, update .travis.yml too
COQ_VERSION=8.15.2
OCAML_VERSION=4.14.0

## Project Source Locations
# Coq sources
COQDIR = coq
COQLIBDIR = ../lib
QUICKCHICKDIR=../lib/QuickChick

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract -R $(QUICKCHICKDIR)/src/ QuickChick -I $(QUICKCHICKDIR)/src -I $(QUICKCHICKDIR)/plugin 
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
COQMAKEFILE="$(COQBIN)coq_makefile"
MENHIR=menhir
CP=cp

######## The full vellvm executable
VELLVM_EXE=_build/default/ml/main.exe
VELLVM_BC =_build/default/ml/main.bc

######## The "frontend" is only the parser/pretty-printer 
FRONTEND_EXE=_build/default/ml/frontend.exe
COQFILES_FRONTEND := QC/ShowAST QC/ReprAST Utils/ParserHelper
FRONTEND_VOFILES := $(COQFILES_FRONTEND:%=coq/%.vo)

.DEFAULT_GOAL := all

######## targets not in this "KNOWNTARGETS" list will be forwarded to CoqMakefile via invoke-coqmakefile
######## WARNING - every target of *this* Makefile must be listed here
KNOWNTARGETS := CoqMakefile invoke-coqmakefile coq extracted $(EXTRACTDIR)/STAMP $(VELLVM_EXE) vellvm vellvmbc test check qc-tests yarpgen-tests rm-qc-test-vo clean extractedclean clean-coqmakefile doc/coq2html documentation $(EXTRACTDIR)/FRONTEND_STAMP $(FRONTEND_EXE) frontend frontend_exe pin-coq opam print-opam print-includes

KNOWNFILES := Makefile _CoqProject

CoqMakefile: _CoqProject
	$(COQMAKEFILE) -docroot ../doc -f _CoqProject -o CoqMakefile

######## defer to CoqMakefile for anything not in $(KNOWNTARGETS)
.PHONY: invoke-coqmakefile 
invoke-coqmakefile: CoqMakefile
ifeq ($(MAKECMDGOALS),)
	$(MAKE) -j --no-print-directory -f CoqMakefile
else
ifeq ($(filter-out $(KNOWNTARGETS), $(MAKECMDGOALS)),)
	@true
else
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
endif
endif

.PHONY: all $(KNOWNFILES)
all: vellvm

.PHONY: coq
coq: real-all

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(VFILES) $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Patching extraction"
	# patch -p0 < CRelationClasses.mli.patch
	# patch -u $(EXTRACTDIR)/GenAlive2.ml -i GenAlive2.ml.patch
	@echo "Fixing Extraction"
	bash fix-extraction.sh
	touch $(EXTRACTDIR)/STAMP

$(VELLVM_EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Vellvm"
	dune build ml/main.exe

vellvm: $(VELLVM_EXE)
	cp $(VELLVM_EXE) vellvm
	chmod u+w vellvm

.PHONY: vellvmbc
vellvmbc: $(VELLVM_BC)
	@echo "Something"
	cp $(VELLVM_BC) vellvmbc
	chmod u+w vellvmbc

$(VELLVM_BC): extracted ml/dune ml/extracted/dune ml/testing/dune
	dune build ml/main.bc


######## testing the Vellvm interperter

.PHONY: test
test: vellvm
	./vellvm -test

.PHONY: check
check: test

####### Yarpgen testing targets
.PHONY: yarpgen-tests
yarpgen-tests: rm-qc-test-vo coq
	$(COQEXEC) coq/QC/QCVellvm.v

######## QuickChick testing targets

.PHONY: qc-tests
qc-tests: rm-qc-test-vo coq
	$(COQEXEC) coq/QC/QCVellvm.v

.PHONY: rm-qc-test-vo
rm-qc-test-vo:
	rm -f coq/QC/QCVellvm.vo


######## cleaning the project

.PHONY: clean
clean: extractedclean clean-coqmakefile
	rm -rf doc/html doc/*.glob
	rm -rf output
	rm -f vellvm
	rm -f frontend
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

clean-coqmakefile: CoqMakefile
	$(MAKE) -j --no-print-directory -f CoqMakefile clean

######## documentation

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


####### Facilities for building only the frontend - parser and pretty printer

$(EXTRACTDIR)/FRONTEND_STAMP: $(FRONTEND_VOFILES) $(EXTRACTDIR)/ExtractFrontend.v
	@echo "Extracting Frontend"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/ExtractFrontend.v
	patch -p0 < CRelationClasses.mli.patch
	patch -p0 < GenAlive2.ml.patch
	touch $(EXTRACTDIR)/FRONTEND_STAMP
	rm -f $(EXTRACTDIR)/STAMP   # invalidate "normal" extraction

.PHONY: $(FRONTEND_EXE)
$(FRONTEND_EXE): $(EXTRACTDIR)/FRONTEND_STAMP ml/dune ml/extracted/dune ml/testing/dune ml/frontend.ml ml/IO.ml
	@echo "Compiling Vellvm (Frontend Only)"
	dune build ml/frontend.exe

.PHONY: frontend
frontend: 
	$(MAKE) $(FRONTEND_VOFILES)
	$(MAKE) frontend_exe

.PHONY: frontend_exe
frontend_exe:
	make $(FRONTEND_EXE)
	cp $(FRONTEND_EXE) frontend
	chmod u+w frontend

#### configuring / inspecting the build process

######## WARNING: clobbers coq installation
########   after doing `make pin-coq` you should do `eval $(opam env)`
.PHONY: pin-coq
pin-coq:
	opam pin add coq $(COQ_VERSION) -y

######## opam packages (except for Coq) that Vellvm depends on
########    use `make opam` to install these
########    also used by .travis ci to configure the build process
OPAMPKGS= coq-ext-lib\
	coq-paco\
	coq-ceres\
	coq-flocq\
	coq-mathcomp-ssreflect\
	coq-simple-io\
	coq-itree\
	coq-quickchick\
	cppo\
	dune\
	menhir\
	qcheck\
	ocamlbuild


######## WARNING: clobbers opam installation
########   after doing `make opam` you should do `eval $(opam env)`
.PHONY: opam
opam:
	opam install -y --verbose $(OPAMPKGS) 

print-opam:
	@echo $(OPAMPKGS)

.PHONY: print-includes
print-includes:
	@echo $(COQINCLUDES)

######## Any other target gets "forwarded" to the generated CoqMakefile
%: invoke-coqmakefile
	@true
