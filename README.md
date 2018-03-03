# Chip-8

[![Travis](https://img.shields.io/travis/ianprime0509/chip8.svg)]()

This is a [Chip-8](https://en.wikipedia.org/wiki/CHIP-8) emulator, assembler
and disassembler, written in Rust.  It began as a port of my original [C
version](https://github.com/ianprime0509/chip8-c), and I've fixed at least a
few bugs that were present in the original.  It is by no means finished, but it
should be at least usable for playing games (as well as
assembling/disassembling them).

## Building

You can run `cargo build --release` to build the programs; it will produce the
binaries `chip8`, `chip8asm` and `chip8disasm`.

To build everything, including the manual, you will need Texinfo installed on
your system as well as some `make` utility (I've only tested it with GNU Make).
Then, you can run the `make` command to build the programs and the manual.

## Usage

There are some games in the `games` directory that you can use with the
emulator.  See the `README.md` file in that directory for more information
about them.

## License

This is free software, distributed under the [MIT
license](https://opensource.org/licenses/MIT).
