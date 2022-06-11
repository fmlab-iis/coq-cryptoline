LIBS=lib/coq-qfbv
COQMAKEFILE=Makefile.coq
MAKE=make

.PHONY: default libs

default:
	$(MAKE) -f $(COQMAKEFILE)

libs:
	for lib in $(LIBS); do \
		$(MAKE) -C $$lib all; \
	done

all: libs default

clean:
	make -f $(COQMAKEFILE) clean

distclean:
	for lib in $(LIBS); do \
		make -C $$lib distclean; \
	done
	make -f $(COQMAKEFILE) clean
