# This Makefile is for building the complete Chip-8 project, including the
# emulator, assembler, disassembler and manual.  If you only care about the
# programmatic components (everything except the manual), you can build the
# project using Cargo alone.

# Metadata
MANUAL_VERSION = 0.1.0

# Programs
CARGO ?= cargo
TEXI2ANY ?= texi2any

# Local file locations
DOCDIR = info/
MANUAL_HTML = manual_html/

ARTIFACTS = chip8.info $(MANUAL_HTML) target/

# Flags
BUILDFLAGS ?= --release
TEXIFLAGS ?=

# Rules
.PHONY: all cargo clean manual

all: cargo manual

cargo:
	$(CARGO) build $(BUILDFLAGS)

clean:
	@rm -rf $(ARTIFACTS)

manual: chip8.info $(MANUAL_HTML)

chip8.info: $(DOCDIR)/chip8.texi $(DOCDIR)/version.texi
	$(TEXI2ANY) $(TEXIFLAGS) --info -I $(DOCDIR) -o $@ $<

$(MANUAL_HTML): $(DOCDIR)/chip8.texi $(DOCDIR)/version.texi
	$(TEXI2ANY) $(TEXIFLAGS) --html -I $(DOCDIR) -o $@ $<

$(DOCDIR)/version.texi:
	@echo >$@ @set VERSION $(MANUAL_VERSION)
