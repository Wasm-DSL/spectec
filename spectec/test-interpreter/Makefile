# Configuration

NAME = spectec
EXE = $(PWD)/../$(NAME)
EXT = $(NAME)
LOG = _log

OWNDIR = $(PWD)
SPECDIR = ../../specification/wasm-3.0
SPECFILES = $(shell ls $(SPECDIR)/*.$(EXT))


# Main targets

.PHONY: all

all: test


# Test

.PHONY: test

test: $(SPECDIR) $(EXE)
	(cd $(SPECDIR) && $(EXE) -l *.$(EXT))


# Executable

$(EXE): exe

exe:
	@(cd ..; make exe)


# Cleanup

.PHONY: clean distclean

clean:
	rm -f $(LOG)

distclean: clean
