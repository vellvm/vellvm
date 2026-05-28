## Vellvm Project Makefile

#### Build Configuration Information

## Project Source Locations
# Rocq sources
ROCQDIR = rocq
ROCQLIBDIR = ../lib

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

ROCQINCLUDES=$(foreach d, $(ROCQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract
ROCQC="$(ROCQBIN)rocq" c -q $(ROCQINCLUDES) $(ROCQCOPTS)
ROCQDEP="$(ROCQBIN)rocq" dep $(ROCQINCLUDES)
ROCQEXEC="$(ROCQBIN)rocq" top -q -w none $(ROCQINCLUDES) -batch -load-vernac-source
ROCQMAKEFILE="$(ROCQBIN)rocq" makefile
MENHIR=menhir
CP=cp

######## The full vellvm executable
VELLVM_EXE=_build/default/ml/main.exe
VELLVM_BC =_build/default/ml/main.bc

######## The "frontend" is only the parser/pretty-printer
FRONTEND_EXE=_build/default/ml/frontend.exe
AGGREGATE_EXE=_build/default/ml/aggregate.exe
ROCQFILES_FRONTEND := Transformations/Transform QC/ShowAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib
ROCQFILES_EXEC := QC/ShowAST QC/ReprAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib Semantics/TopLevel Handlers Utilities Numeric/Floats
ROCQFILES_QC := QC/GenAST QC/GenMetadata QC/ECS QC/Lens QC/GenAlive2 QC/Generators QC/ReprAST QC/ShowAST QC/Utils QC/DList
FRONTEND_VOFILES := $(ROCQFILES_FRONTEND:%=rocq/%.vo)
EXEC_VFILES := $(ROCQFILES_EXEC:%=rocq/%.v)
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)
QC_VFILES := $(ROCQFILES_QC:%=rocq/%.v)
QC_VOFILES := $(ROCQFILES_QC:%=rocq/%.vo)
VFILES := $(shell find rocq -name "*.v")

.DEFAULT_GOAL := all

######## targets not in this "KNOWNTARGETS" list will be forwarded to RocqMakefile via invoke-rocqmakefile
######## WARNING - every target of *this* Makefile must be listed here
KNOWNTARGETS := RocqMakefile invoke-rocqmakefile rocq extracted $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/Extract.v $(VELLVM_EXE) vellvm vellvmbc test check qc-tests yarpgen-tests rm-qc-test-vo clean extractedclean clean-rocqmakefile doc/rocq2html documentation $(EXTRACTDIR)/FRONTEND_STAMP $(FRONTEND_EXE) frontend frontend_exe pin-rocq opam print-opam print-includes qc-files

KNOWNFILES := Makefile _RocqProject

RocqMakefile: _RocqProject
	$(ROCQMAKEFILE) -docroot ../doc -f _RocqProject -o RocqMakefile

######## defer to RocqMakefile for anything not in $(KNOWNTARGETS)
.PHONY: invoke-rocqmakefile
invoke-rocqmakefile: RocqMakefile
ifeq ($(MAKECMDGOALS),)
	$(MAKE) -j --no-print-directory -f RocqMakefile
else
ifeq ($(filter-out $(KNOWNTARGETS), $(MAKECMDGOALS)),)
	@true
else
	$(MAKE) -j --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
endif
endif

.PHONY: all $(KNOWNFILES)
all: vellvm

.PHONY: rocq
rocq: real-all

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(EXEC_VFILES) $(EXEC_VOFILES) $(EXTRACTDIR)/Extract.v
	make $(EXEC_VOFILES)
	@echo "Extracting"
	$(ROCQEXEC) $(EXTRACTDIR)/Extract.v
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

######## testing the Vellvm interperter

.PHONY: test
test: vellvm
	./vellvm -l libll/rust-intrinsics.ll -test

.PHONY: check
check: test

####### Yarpgen testing targets
.PHONY: yarpgen-tests
yarpgen-tests: rm-qc-test-vo rocq
	$(ROCQEXEC) rocq/QC/QCVellvm.v

######## QuickChick testing targets

.PHONY: qc-tests
qc-tests: rm-qc-test-vo qc-files vellvm
	$(ROCQEXEC) rocq/QC/QCVellvm.v

.PHONY: qc-files
qc-files: $(QC_VFILES)
	make $(QC_VOFILES)

.PHONY: rm-qc-test-vo
rm-qc-test-vo:
	rm -f rocq/QC/QCVellvm.vo

######## cleaning the project

.PHONY: clean
clean: extractedclean clean-rocqmakefile
	rm -rf doc/html doc/*.glob
	rm -rf output
	rm -f vellvm
	rm -f frontend
	rm -f aggregate
	rm -f doc/rocq2html.ml doc/rocq2html doc/*.cm? doc/*.o
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

clean-rocqmakefile: RocqMakefile
	$(MAKE) -j --no-print-directory -f RocqMakefile clean

######## documentation

.PHONY: documentation
documentation: $(VFILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	rocq2html -d doc/html $^

####### Facilities for building only the frontend - parser and pretty printer

$(EXTRACTDIR)/FRONTEND_STAMP: $(FRONTEND_VOFILES) $(EXTRACTDIR)/ExtractFrontend.v
	@echo "Extracting Frontend"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(ROCQEXEC) $(EXTRACTDIR)/ExtractFrontend.v
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

######## WARNING: clobbers opam installation
########   after doing `make opam` you should do `eval $(opam env)`
.PHONY: opam
opam:
	opam install -y --verbose --deps-only ..

.PHONY: print-includes
print-includes:
	@echo $(ROCQINCLUDES)

.PHONY: c2rust-tests
c2rust-tests:
	make -C ../tractor/c2rust-tests

######## Any other target gets "forwarded" to the generated RocqMakefile
%: invoke-rocqmakefile
	@true
