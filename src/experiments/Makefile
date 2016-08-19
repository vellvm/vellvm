MODULES := CoqEqDec LTS block_model conc_model SetsAndMaps Util llvm_model sync_patterns
VS := $(MODULES:%=%.v)

COMPCERTDIR ?= "/cygdrive/c/Users/William/Documents/GitHub/compcomp"
COQFLAGS := -R $(COMPCERTDIR) compcert
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQFLAGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
