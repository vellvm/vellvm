COQSRCDIR := ../../coq

.PHONY: all clean extract

all: ollvm_ast.cma

$(COQSRCDIR)/Makefile.coq:
	$(MAKE) -C $(COQSRCDIR) Makefile.coq

extract: $(COQSRCDIR)/Makefile.coq
	rm -rf $(COQSRCDIR)/Extract.vo	
	$(MAKE) -C $(COQSRCDIR) -f Makefile.coq Extract.vo

ollvm_ast.cma: extract
	cp $(COQSRCDIR)/*.ml* .
	mv VellvmAst.ml ollvm_ast.ml
	mv VellvmAst.mli ollvm_ast.mli
	ocamlbuild ollvm_ast.cma

clean:
	ocamlbuild -clean
	rm -rf *.ml*

