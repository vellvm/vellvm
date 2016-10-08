# Eventually this will be the master Makefile

SUBDIRS = coq ml ollvm

.PHONY: clean all subdirs $(SUBDIRS)

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

ollvm: ml

clean:
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir clean; \
	done	
