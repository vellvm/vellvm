COQC   ?= coqc
COQDEP ?= coqdep

COQCFLAGS ?= -q # -impredicative-set


# source ------------------------------------------------------------------
SRCDIR  = .
VFILES   = $(shell find $(SRCDIR) -name "*.v" -not -name '.*')
VOFILES  = $(patsubst %.v,%.vo,$(VFILES))

INCFLAGS = -R $(SRCDIR) Vminus

# targets -----------------------------------------------------------------
.PHONY: all coq clean tags

all: 
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq

# coq src -----------------------------------------------------------------

coq: $(VOFILES)

%.vo: %.v
	@echo "COQC $*.v"
	@$(COQC) $(COQCFLAGS) $(INCFLAGS) $*.v

.depend: $(VFILES) $(GENFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

# don't include generated coq deps for these goals:
ifeq ($(findstring $(MAKECMDGOALS), ott tags clean .depend),)
-include .depend
endif

# -------------------------------------------------------------------------
tags:
	@coqtags $(shell find $(SRCDIR) -name '*.v')

clean:
	rm -f $(VOFILES) $(VOFILES:.vo=.glob)
	rm -f .depend
