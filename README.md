# Chip-8

[![Travis](https://img.shields.io/travis/ianprime0509/chip8.svg)]()

This is a [Chip-8](https://en.wikipedia.org/wiki/CHIP-8) emulator, assembler
and disassembler, written in Rust.  It is a rewrite of my original [C
version](https://github.com/ianprime0509/chip8) since I wanted to see how it
would look in Rust.  Ideally, it should work as well as the original, but might
be lacking some features (since I expect to work more frequently on the
original version).

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
