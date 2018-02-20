/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! Tests whether a simple disassemble -> assemble process produces output
//! identical to the original input.

extern crate chip8;

use std::io::Cursor;

use chip8::{Assembler, Disassembler};

static FONTTEST: &[u8] = include_bytes!("assembled/fonttest.bin");
static SPRITETEST: &[u8] = include_bytes!("assembled/spritetest.bin");

#[test]
fn fonttest() {
    let mut input = Cursor::new(FONTTEST);
    let disasm = Disassembler::new(&mut input).unwrap();
    let mut output = Vec::new();
    disasm.dump(&mut output).unwrap();

    let asm = Assembler::new();
    let mut input = Cursor::new(output);
    let mut output = Vec::new();
    asm.assemble(&mut input, &mut output).unwrap();

    assert_eq!(output, FONTTEST);
}

#[test]
fn spritetest() {
    let mut input = Cursor::new(SPRITETEST);
    let disasm = Disassembler::new(&mut input).unwrap();
    let mut output = Vec::new();
    disasm.dump(&mut output).unwrap();

    let asm = Assembler::new();
    let mut input = Cursor::new(output);
    let mut output = Vec::new();
    asm.assemble(&mut input, &mut output).unwrap();

    assert_eq!(output, SPRITETEST);
}
