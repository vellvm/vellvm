SUBDIRS = extracted
BASE_DIR  := $(realpath $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST))))..))
OLLVM_LIBDIR := $(BASE_DIR)/ollvm/src/ollvm
LIBS := ollvm,unix,str

.PHONY: clean all subdirs $(SUBDIRS)

all:	$(SUBDIRS)
	ocamlbuild -cflags -I,$(OLLVM_LIBDIR) -lflags -I,$(OLLVM_LIBDIR) -libs $(LIBS) main.native


subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

clean:
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir clean; \
	done
	ocamlbuild -clean


