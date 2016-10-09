.PHONY: clean all extract

MODULES := Vellvm Ollvm_ast Transform Util Extract

VFILES := $(MODULES:%=%.v)

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -R . "" $(VFILES) -o Makefile.coq -extra-phony clean "" "rm -rf *.ml *.mli"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
