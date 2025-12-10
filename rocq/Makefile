COQC      ?= coqc
COQDEP    ?= coqdep
COQFLAGS  ?= -Q . Notes

VFILES    := $(wildcard *.v)
VOFILES   := $(VFILES:.v=.vo)

# Default: show help
help:
	@echo "Usage:"
	@echo "  make <file>.vo    - Compile a single file (e.g., make Adam.vo)"
	@echo "  make all          - Compile all .v files"
	@echo "  make clean        - Remove compiled files"
	@echo "  make deps         - Show dependencies"

all: $(VOFILES)

# Pattern rule for compiling individual .v files
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# Generate and include dependencies
.depend: $(VFILES)
	@$(COQDEP) $(COQFLAGS) $(VFILES) > .depend 2>/dev/null || true

deps: .depend
	@cat .depend

-include .depend

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .depend

# Allow building without dependencies for quick single-file compilation
quick: COQFLAGS += -vos
quick: ;

%.vos: %.v
	$(COQC) $(COQFLAGS) -vos $<

.PHONY: help all clean deps quick
