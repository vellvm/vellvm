## Vellvm Project Makefile

#### Build Configuration Information

## Project Source Locations
# Rocq sources
ROCQDIR = rocq

# OCaml sources
EXTRACTDIR = ml/extracted

ROCQINCLUDES=$(foreach d, $(ROCQDIR), -R $(d) Vellvm) -R $(EXTRACTDIR) Extract
ROCQEXEC="$(ROCQBIN)rocq" top -q -w none $(ROCQINCLUDES) -batch -load-vernac-source
ROCQMAKEFILE="$(ROCQBIN)rocq" makefile

######## The full vellvm executable
VELLVM_EXE=_build/default/ml/main.exe
# Override with `make DUNE_PROFILE=dev` for debug builds.
DUNE_PROFILE?=dev
# DUNE_PROFILE?=release

######## The "frontend" is only the parser/pretty-printer
FRONTEND_EXE=_build/default/ml/frontend.exe
ROCQFILES_FRONTEND := Syntax/ShowAST Syntax/ReprAST Utils/ParserHelper Syntax/LLVMAst Syntax/AstLib
ROCQFILES_EXEC := $(ROCQFILES_FRONTEND) Semantics
FRONTEND_VOFILES := $(ROCQFILES_FRONTEND:%=rocq/%.vo)
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)

.DEFAULT_GOAL := all

RocqMakefile: _RocqProject
	$(ROCQMAKEFILE) -f _RocqProject -o RocqMakefile

######## Use `make interp` to skip rocq/Theory and only build the executable.
.PHONY: all
all:
	$(MAKE) rocq
	$(MAKE) vellvm

.PHONY: rocq
rocq: real-all

.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(EXEC_VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	$(ROCQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Post-processing extraction: unbox the itree node wrapper"
	perl -i -pe 's/^(\| Coq_go of .* itreeF)$$/$$1 [\@\@unboxed]/' $(EXTRACTDIR)/ITreeDefinition.ml $(EXTRACTDIR)/ITreeDefinition.mli
	touch $(EXTRACTDIR)/STAMP

$(VELLVM_EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Vellvm"
	dune build --profile $(DUNE_PROFILE) ml/main.exe

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

.PHONY: test-full
test-full: vellvm
	./vellvm -L libll -test

.PHONY: test
test: vellvm
	./vellvm -L libll -test-dir ../tests

.PHONY: check
check: test

######## timing the interpreter performance stress tests (see ../tests/perf/README.md)

.PHONY: perf
perf: vellvm
	../tests/perf/run.sh

######## cleaning the project

.PHONY: clean
clean: extractedclean clean-rocqmakefile
	rm -rf output
	find rocq -name ".*.aux" -delete
	rm -f vellvm
	rm -f frontend
	rm -f aggregate
	dune clean

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

.PHONY: clean-rocqmakefile
clean-rocqmakefile: RocqMakefile
	$(MAKE) -j --no-print-directory -f RocqMakefile clean

####### Facilities for building only the frontend - parser and pretty printer

$(EXTRACTDIR)/FRONTEND_STAMP: $(FRONTEND_VOFILES) $(EXTRACTDIR)/ExtractFrontend.v
	@echo "Extracting Frontend"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(ROCQEXEC) $(EXTRACTDIR)/ExtractFrontend.v
	touch $(EXTRACTDIR)/FRONTEND_STAMP
	rm -f $(EXTRACTDIR)/STAMP   # invalidate "normal" extraction

$(FRONTEND_EXE): $(EXTRACTDIR)/FRONTEND_STAMP ml/dune ml/extracted/dune ml/testing/dune ml/frontend.ml ml/IO.ml
	@echo "Compiling Vellvm (Frontend Only)"
	dune build --profile $(DUNE_PROFILE) ml/frontend.exe

.PHONY: frontend
frontend:
	$(MAKE) $(FRONTEND_VOFILES)
	$(MAKE) frontend_exe

.PHONY: frontend_exe
frontend_exe:
	$(MAKE) $(FRONTEND_EXE)
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
	$(MAKE) -C ../tractor/c2rust-tests

######## Hand-written source files used as prerequisites above: an empty
######## recipe marks them "terminal" so the catch-all pattern rule below
######## never mistakes one of them for a stale RocqMakefile-generated
######## target (which would otherwise happen the moment RocqMakefile
######## itself is regenerated and becomes newer than these).
Makefile _RocqProject \
$(EXTRACTDIR)/Extract.v $(EXTRACTDIR)/ExtractFrontend.v \
ml/dune ml/extracted/dune ml/testing/dune ml/frontend.ml ml/IO.ml: ;

######## $(EXEC_VOFILES)/$(FRONTEND_VOFILES) are each forwarded as ONE
######## combined batch call (not one sub-make per file — avoids racing
######## independent sub-makes over a file shared between them, e.g.
######## Utils.vo). A plain top-level mtime check ("is this .vo newer than
######## RocqMakefile") is NOT enough to decide whether to forward: an
######## existing-but-transitively-stale .vo (e.g. after deleting something
######## it Requires) still looks "newer than RocqMakefile" from here, so
######## these depend on an always-out-of-date .PHONY target instead,
######## guaranteeing RocqMakefile's own (accurate, coqdep-based) check
######## actually runs every time.
.PHONY: rocqmakefile-exec
rocqmakefile-exec:
	+$(MAKE) -j --no-print-directory -f RocqMakefile $(EXEC_VOFILES)

.PHONY: rocqmakefile-frontend
rocqmakefile-frontend:
	+$(MAKE) -j --no-print-directory -f RocqMakefile $(FRONTEND_VOFILES)

# $(FRONTEND_VOFILES) is a subset of $(EXEC_VOFILES) (Semantics.vo is the
# one extra file) — give each .vo exactly one rule so Make doesn't warn
# about overriding commands: everything in the frontend set forwards via
# the (smaller, faster) frontend batch, the rest via the exec batch.
$(FRONTEND_VOFILES): RocqMakefile rocqmakefile-frontend ;
$(filter-out $(FRONTEND_VOFILES),$(EXEC_VOFILES)): RocqMakefile rocqmakefile-exec ;

######## Anything else (a bare Rocq target such as `rocq/Foo/Bar.vo`, or a
######## target only defined by the generated RocqMakefile, e.g. `real-all`,
######## `html`, `install`) is forwarded there, scoped to just that target.
######## Same always-ask-RocqMakefile reasoning as above, via a shared
######## .PHONY marker rather than a plain file-mtime prerequisite.
.PHONY: invoke-rocqmakefile
invoke-rocqmakefile: RocqMakefile

%: invoke-rocqmakefile
	+$(MAKE) -j --no-print-directory -f RocqMakefile $@
