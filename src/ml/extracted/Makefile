COQSRCDIR := ../../coq

EXTRACTED:= Transform.ml Transform.mli

.PHONY: all clean extract

all: $(EXTRACTED)

$(COQSRCDIR)/Makefile.coq:
	$(MAKE) -C $(COQSRCDIR) Makefile.coq

$(EXTRACTED): $(COQSRCDIR)/Makefile.coq
	rm -rf $(COQSRCDIR)/Extract.vo	
	$(MAKE) -C $(COQSRCDIR) -f Makefile.coq Extract.vo
	cp $(COQSRCDIR)/*.ml* .

clean:
	rm -rf *.ml*

