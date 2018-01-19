// Copyright 2018 Ian Johnson

// This file is part of Chip-8.

// Chip-8 is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Chip-8 is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Chip-8.  If not, see <http://www.gnu.org/licenses/>.

//! Main module stuff.

#[macro_use]
extern crate enum_primitive;
extern crate failure;
#[macro_use]
extern crate failure_derive;
#[macro_use]
extern crate log;
extern crate num;
extern crate rand;
extern crate time;

/// The size of the Chip-8's memory, in bytes.
pub const MEM_SIZE: usize = 0x1000;
/// The address where programs should be loaded.
pub const PROG_START: usize = 0x200;
/// The maximum size of a Chip-8 program, in bytes.
pub const PROG_SIZE: usize = MEM_SIZE - PROG_START;

pub mod display;
pub mod input;
pub mod instruction;
pub mod interpreter;
mod timer;

pub use instruction::{Address, AlignedAddress, Instruction, Opcode, Register};
pub use interpreter::Interpreter;
