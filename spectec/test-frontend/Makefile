# Configuration

NAME = spectec
EXE = $(PWD)/../$(NAME)
EXT = $(NAME)
LOG = _log

OWNDIR = $(PWD)
SPECDIR = ../../specification
SPECFILES = $(shell cd $(SPECDIR) && ls -d wasm-*)
TESTFILES = $(shell ls *.$(EXT))
SPECS = $(SPECFILES:%=test-%)
TESTS = $(TESTFILES:%.$(EXT)=test-%)


# Main targets

.PHONY: all

all: test


# Test

.PHONY: test $(SPECS) $(TESTS)

test: $(SPECS) $(TESTS)

$(SPECS): test-%: $(EXE)
	(cd $(SPECDIR)/$* && $(EXE) -l *.$(EXT))

$(TESTS): test-%: %.$(EXT) $(EXE)
	($(EXE) -l $<)


# Executable

$(EXE): exe

exe:
	@(cd ..; make exe)


# Cleanup

.PHONY: clean distclean

clean:
	rm -f $(LOG)

distclean: clean
