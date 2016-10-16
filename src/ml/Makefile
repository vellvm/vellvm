SUBDIRS = extracted
BASE_DIR  := $(realpath $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST))))..))
OLLVM_LIBDIR := $(BASE_DIR)/ollvm/src/ollvm
ASTDIR := $(BASE_DIR)/ast
LIBS := ollvm,unix,str

.PHONY: clean all subdirs main.native $(SUBDIRS)

all:	vellvm

main.native: $(SUBDIRS)
	ocamlbuild -cflags -I,$(ASTDIR) -cflags -I,$(OLLVM_LIBDIR) -lflags -I,$(ASTDIR) -lflags -I,$(OLLVM_LIBDIR) -libs $(LIBS) main.native


vellvm: main.native
	cp main.native vellvm

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

test: vellvm
	./vellvm --test

clean:
	for dir in $(SUBDIRS); do \
	  $(MAKE) -C $$dir clean; \
	done
	ocamlbuild -clean
	rm vellvm
	rm -rf output

