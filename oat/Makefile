# Coq sources
COQDIR = coq
COQLIBDIR = ../lib
VELLVMDIR = ../src/coq

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted

ITREEDIR=../lib/InteractionTrees

COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Oat) -R $(VELLVMDIR) Vellvm -R $(ITREEDIR)/theories/ ITree 
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source
MENHIR=menhir
CP=cp

COQFILES_OAT    := Ast DynamicValues OatEvents Denotation Plumbing CompilerCtxt Compiler

VFILES  := $(COQFILES_OAT:%=coq/%.v)
VOFILES := $(COQFILES_OAT:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq

coq: $(VOFILES)

update-trees:
	git submodule update -- $(ITREEDIR)

itrees:
	make -C $(ITREEDIR)

.PHONY: extracted itrees 

extracted: $(EXTRACTDIR)/STAMP $(VOFILES)

$(EXTRACTDIR)/STAMP: $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
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

$(EXE): extracted ml/dune ml/extracted/dune ml/testing/dune
	@echo "Compiling Oat"
	dune build ml/main.exe 

oatc: $(EXE)
	cp $(EXE) oatc


test: vellvm
	./vellvm --test

print-includes:
	@echo $(COQINCLUDES)

clean: clean-vellvm clean-oat clean-itrees

clean-oat:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	chmod +wx -R $(MLDIR)/_build
	dune clean

clean-vellvm:
	rm -f .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
	rm -f $(VOFILES)
	rm -rf doc/html doc/*.glob
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	dune clean
	rm -rf output
	rm -f vellvm
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
clean-itrees:
	make -C $(ITREEDIR) clean

.PHONY: clean-vellv clean-oat clean-itrees

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
