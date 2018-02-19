/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! Main module stuff.

#[macro_use]
extern crate combine;
#[macro_use]
extern crate enum_primitive;
extern crate failure;
#[macro_use]
extern crate failure_derive;
#[macro_use]
extern crate log;
#[macro_use]
extern crate maplit;
extern crate num;
extern crate rand;
extern crate time;

/// The size of the Chip-8's memory, in bytes.
pub const MEM_SIZE: usize = 0x1000;
/// The address where programs should be loaded.
pub const PROG_START: usize = 0x200;
/// The maximum size of a Chip-8 program, in bytes.
pub const PROG_SIZE: usize = MEM_SIZE - PROG_START;

pub mod assembler;
pub mod disassembler;
pub mod display;
pub mod input;
pub mod instruction;
pub mod interpreter;
mod timer;
mod util;

pub use assembler::Assembler;
pub use instruction::{Address, AddressMisalignedError, AddressOutOfBoundsError, AlignedAddress,
                      Instruction, Opcode, Register};
pub use interpreter::Interpreter;
