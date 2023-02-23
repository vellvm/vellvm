COQDIR := .
KNOWNTARGETS := CoqMakefile
SKIPTARGETS := 
KNOWNFILES := Makefile _CoqProject .depend

invoke-coqmakefile: CoqMakefile
ifeq ($(MAKECMDGOALS),)
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
else
ifeq ($(filter-out $(SKIPTARGETS),$(MAKECMDGOALS)),)
	@true
else
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
endif
endif

.PHONY: all invoke-coqmakefile clean-coqmakefile

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean-coqmakefile: CoqMakefile
	$(MAKE) -j --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS)) clean


.PHONY: clean
clean: clean-coqmakefile
	rm -rf .depend
	find $(COQDIR) -name "*.vo" -delete
	find $(COQDIR) -name "*.vio" -delete
	find $(COQDIR) -name "*.vok" -delete
	find $(COQDIR) -name "*.vos" -delete
