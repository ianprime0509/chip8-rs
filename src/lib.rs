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

enum_from_primitive! {
/// A Chip-8 register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
    V0 = 0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    VA,
    VB,
    VC,
    VD,
    VE,
    VF,
}
}

#[cfg(test)]
mod tests {
    use std::u8;

    use instruction::Instruction;
    use interpreter::{Interpreter, Options};

    /// Tests the `ADD` operation (both `ADD Vx, byte` and `ADD Vx, Vy`).
    #[test]
    fn instruction_add() {
        use Register::*;

        // Test cases, in the format (Vx, Vy, b1, b2).
        let cases = [
            (V0, V1, 24u8, 67u8),
            (V5, VD, 54u8, 102u8),
            (V7, VE, 255u8, 255u8),
            (V2, V4, 1u8, 255u8),
            (V5, V6, 0u8, 78u8),
        ];
        let mut interpreter = Interpreter::with_options(Options::testing());

        for &(vx, vy, b1, b2) in cases.into_iter() {
            let case = (vx, vy, b1, b2);
            let sum = b1.wrapping_add(b2);
            let overflow = b1 as u32 + b2 as u32 > u8::MAX as u32;

            // Test `ADD Vx, byte`.
            interpreter.set_register(vx, b1);
            interpreter.execute(Instruction::AddByte(vx, b2)).unwrap();
            assert_eq!(interpreter.register(vx), sum, "case {:?}", case);
            assert_eq!(interpreter.register(VF), overflow as u8, "case {:?}", case);

            // Test `ADD Vx, Vy`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::AddReg(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), sum, "case {:?}", case);
            assert_eq!(interpreter.register(VF), overflow as u8, "case {:?}", case);
        }
    }

    /// Tests opcode to instruction translation.
    #[test]
    fn opcode_translation() {
        use Register::*;
        use instruction::Address;
        use instruction::Instruction;
        use instruction::Instruction::*;
        use instruction::Opcode;

        let cases = [
            (0x00C4, Scd(4)),
            (0x00E0, Cls),
            (0x00EE, Ret),
            (0x00FB, Scr),
            (0x00FC, Scl),
            (0x00FD, Exit),
            (0x00FE, Low),
            (0x00FF, High),
            (
                0x1234,
                Jp(Address::from_u16(0x234).unwrap().aligned().unwrap()),
            ),
            (
                0x2456,
                Call(Address::from_u16(0x456).unwrap().aligned().unwrap()),
            ),
            (0x342A, SeByte(V4, 0x2A)),
            (0x4A75, SneByte(VA, 0x75)),
            (0x5AE0, SeReg(VA, VE)),
            (0x63F5, LdByte(V3, 0xF5)),
            (0x7B12, AddByte(VB, 0x12)),
            (0x8590, LdReg(V5, V9)),
            (0x8101, Or(V1, V0)),
            (0x8642, And(V6, V4)),
            (0x87F3, Xor(V7, VF)),
            (0x8264, AddReg(V2, V6)),
            (0x8C45, Sub(VC, V4)),
            (0x8106, Shr(V1)),
            (0x86D7, Subn(V6, VD)),
            (0x8E0E, Shl(VE)),
            (0x9990, SneReg(V9, V9)),
            (0xA568, LdI(Address::from_u16(0x568).unwrap())),
            (0xBABC, JpV0(Address::from_u16(0xABC).unwrap())),
            (0xC5AF, Rnd(V5, 0xAF)),
            (0xD7B0, Drw(V7, VB, 0)),
            (0xE49E, Skp(V4)),
            (0xECA1, Sknp(VC)),
            (0xF907, LdRegDt(V9)),
            (0xFD0A, LdKey(VD)),
            (0xF315, LdDtReg(V3)),
            (0xF718, LdSt(V7)),
            (0xF91E, AddI(V9)),
            (0xFF29, LdF(VF)),
            (0xF230, LdHf(V2)),
            (0xF533, LdB(V5)),
            (0xF655, LdDerefIReg(V6)),
            (0xF865, LdRegDerefI(V8)),
            (0xF175, LdRReg(V1)),
            (0xF485, LdRegR(V4)),
        ];

        for &(opcode, ref instr) in cases.iter() {
            assert_eq!(
                Instruction::from_opcode(Opcode(opcode), false).unwrap(),
                *instr
            );
        }
    }
}
