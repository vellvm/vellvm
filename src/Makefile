# Eventually this will be the master Makefile

SUBDIRS = ast ollvm coq ml

.PHONY: clean all ollvm

all:
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir ; \
	done

clean:
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir clean; \
	done
