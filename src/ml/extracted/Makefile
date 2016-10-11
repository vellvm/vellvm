COQSRCDIR := ../../coq

.PHONY: all clean extract

all: extract

$(COQSRCDIR)/Makefile.coq:
	$(MAKE) -C $(COQSRCDIR) Makefile.coq

extract: $(COQSRCDIR)/Makefile.coq
	rm -rf $(COQSRCDIR)/Extract.vo	
	$(MAKE) -C $(COQSRCDIR) -f Makefile.coq Extract.vo
	cp $(COQSRCDIR)/*.ml* .

clean:
	rm -rf *.ml*

