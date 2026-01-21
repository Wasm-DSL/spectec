# Configuration

NAME = spectec
EXE = $(PWD)/../$(NAME)
EXT = $(NAME)
LOG = _log

# Main targets

.PHONY: all

all: test


# Test

.PHONY: test

test:

# Executable

$(EXE): exe

exe:
	@(cd ..; make exe)


# Cleanup

.PHONY: clean distclean

clean:
	rm -f $(LOG)

distclean: clean
