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
ROCQFILES_FRONTEND := Syntax/ShowAST Syntax/ReprAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib
ROCQFILES_EXEC := $(ROCQFILES_FRONTEND) Semantics
FRONTEND_VOFILES := $(ROCQFILES_FRONTEND:%=rocq/%.vo)
EXEC_VFILES := $(ROCQFILES_EXEC:%=rocq/%.v)
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)
VFILES := $(shell find rocq -name "*.v")

.DEFAULT_GOAL := all

######## targets not in this "KNOWNTARGETS" list will be forwarded to RocqMakefile via invoke-rocqmakefile
######## WARNING - every target of *this* Makefile must be listed here
KNOWNTARGETS := RocqMakefile invoke-rocqmakefile rocq extracted $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/Extract.v $(VELLVM_EXE) vellvm vellvmbc interp timing test check perf clean extractedclean clean-rocqmakefile doc/rocq2html documentation $(EXTRACTDIR)/FRONTEND_STAMP $(FRONTEND_EXE) frontend frontend_exe pin-rocq opam print-opam print-includes qc-files

KNOWNFILES := Makefile _RocqProject

RocqMakefile: _RocqProject
	$(ROCQMAKEFILE) -f _RocqProject -o RocqMakefile

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
	touch $(EXTRACTDIR)/STAMP

$(VELLVM_EXE): extracted ml/dune ml/extracted/dune ml/testing/dune 
	@echo "Compiling Vellvm"
	dune build ml/main.exe

vellvm: $(VELLVM_EXE)
	cp $(VELLVM_EXE) vellvm
	chmod u+w vellvm

######## building only the executable interpreter
# Only compiles the Rocq files the extraction depends on (the closure of
# $(EXEC_VOFILES): Syntax/Semantics/Handlers) — in particular rocq/Theory
# is never compiled, unlike the default target.
.PHONY: interp
interp:
	$(MAKE) $(EXEC_VOFILES)
	$(MAKE) vellvm

######## timing the Rocq compilation
# Compiles sequentially (-j1), printing each file's compilation time as it
# goes, then a summary table sorted by duration. Only out-of-date files are
# recompiled; `make clean-rocqmakefile` first to time the whole library.
# NB: the summary table requires GNU time (`brew install gnu-time` on macOS);
# without it you still get the per-file times, but "No timing data" at the end.
.PHONY: timing
timing: RocqMakefile
	rm -f time-of-build.log
	$(MAKE) -j1 --no-print-directory -f RocqMakefile pretty-timed

######## testing the Vellvm interpreter

.PHONY: test
test: vellvm
	./vellvm -L libll -test

.PHONY: check
check: test

######## timing the interpreter performance stress tests (see ../perf/README.md)

.PHONY: perf
perf: vellvm
	../perf/run.sh

######## cleaning the project

.PHONY: clean
clean: extractedclean clean-rocqmakefile
	rm -rf output
	find rocq  \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" -o -name ".*.aux" \)  -delete
	rm -f vellvm
	rm -f frontend
	rm -f aggregate
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

clean-rocqmakefile: RocqMakefile
	$(MAKE) -j --no-print-directory -f RocqMakefile clean

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
