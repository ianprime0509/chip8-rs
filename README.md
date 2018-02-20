# Chip-8

[![Travis](https://img.shields.io/travis/ianprime0509/chip8.svg)]()

This is a [Chip-8](https://en.wikipedia.org/wiki/CHIP-8) emulator, assembler
and disassembler, written in Rust.  It began as a port of my original [C
version](https://github.com/ianprime0509/chip8-c), and I've fixed at least a
few bugs that were present in the original.  It is by no means finished, but it
should be at least usable for playing games (as well as
assembling/disassembling them).

## Building

You can run `cargo build --release` to build the project; it will produce the
binaries `chip8`, `chip8asm` and `chip8disasm`.  I also transplanted the manual
from the C version into the `info` directory, which you can build using
`texi2any --info chip8.texi` (you will also get some warnings because I haven't
set up a proper build system for it).

## License

This is free software, distributed under the [MIT
license](https://opensource.org/licenses/MIT).
