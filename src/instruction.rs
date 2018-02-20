/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! Chip-8 instructions and opcodes.
//!
//! This module provides the basic types and functions for working with Chip-8
//! instructions and opcodes, including (most notably) the translation of
//! opcodes to the internal `Instruction` type.  The design of this module is
//! intended to make higher-level components, like the interpreter, as simple
//! and understandable as possible.  For example, the presence of the
//! `Instruction` type as an intermediate stage between opcodes and execution
//! makes the interpreter code much nicer and prevents it from having to deal
//! with errors (such as misaligned jump instructions) which should be dealt
//! with at a lower level.

use std::fmt;
use std::str::FromStr;
use std::ops::Add;
use std::ops::Deref;

use failure::Error;
use num::FromPrimitive;

use MEM_SIZE;

/// An error resulting from an out-of-bounds address.
#[derive(Debug, Fail, PartialEq, Eq)]
#[fail(display = "address out of bounds: {:#04X}", _0)]
pub struct AddressOutOfBoundsError(pub usize);

/// An error resulting from a misaligned address.
#[derive(Debug, Fail, PartialEq, Eq)]
#[fail(display = "misaligned address: {:#04X}", _0)]
pub struct AddressMisalignedError(pub usize);

/// An error resulting from an invalid opcode.
#[derive(Debug, Fail, PartialEq, Eq)]
#[fail(display = "invalid opcode: {}", _0)]
struct InvalidOpcodeError(Opcode);

/// An error resulting from trying to parse a non-register as a register.
#[derive(Debug, Fail)]
#[fail(display = "'{}' is not a register", _0)]
pub struct NotARegisterError(String);

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

impl FromStr for Register {
    type Err = NotARegisterError;

    fn from_str(s: &str) -> Result<Self, NotARegisterError> {
        let mut chars = s.chars().map(|c| c.to_ascii_uppercase());
        if chars.next() != Some('V') {
            return Err(NotARegisterError(s.to_owned()));
        }
        if let Some(c) = chars.next() {
            if '0' <= c && c <= '9' {
                Ok(Register::from_u32(c as u32 - '0' as u32).unwrap())
            } else if 'A' <= c && c <= 'F' {
                Ok(Register::from_u32(c as u32 - 'A' as u32 + 10).unwrap())
            } else {
                Err(NotARegisterError(s.to_owned()))
            }
        } else {
            Err(NotARegisterError(s.to_owned()))
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self)
    }
}

/// A Chip-8 opcode.
///
/// Having this as a wrapper around an ordinary `u16` allows for some nice
/// helper methods to be implemented, which make decoding opcodes much easier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opcode(pub u16);

impl Opcode {
    /// Returns the opcode corresponding to the two bytes given in big-endian order.
    pub fn from_bytes(b1: u8, b2: u8) -> Self {
        Opcode(((b1 as u16) << 8) | b2 as u16)
    }

    /// Returns a tuple containing the bytes of this opcode, in big-endian order.
    pub fn bytes(&self) -> (u8, u8) {
        ((self.0 >> 8) as u8, self.0 as u8)
    }

    /// Returns the `Vx` register corresponding to this opcode.
    ///
    /// This does not guarantee that the result is actually meaningful.
    fn vx(&self) -> Register {
        Register::from_u16((self.0 & 0x0F00) >> 8).unwrap()
    }

    /// Sets the `Vx` register corresponding to this opcode, returning a new
    /// opcode.
    fn with_vx(self, vx: Register) -> Self {
        Opcode(self.0 & 0xF0FF | ((vx as u16) << 8))
    }

    /// Returns the `Vy` register corresponding to this opcode.
    ///
    /// This does not guarantee that the result is actually meaningful.
    fn vy(&self) -> Register {
        Register::from_u16((self.0 & 0x00F0) >> 4).unwrap()
    }

    /// Sets the `Vy` register corresponding to this opcode, returning a new
    /// opcode.
    fn with_vy(self, vy: Register) -> Self {
        Opcode(self.0 & 0xFF0F | ((vy as u16) << 4))
    }

    /// Returns the `nibble` corresponding to this opcode.
    ///
    /// This does not guarantee that the result is actually meaningful.
    fn nibble(&self) -> u8 {
        self.0 as u8 & 0xF
    }

    /// Sets the `nibble` corresponding to this opcode, returning a new opcode.
    fn with_nibble(self, nibble: u8) -> Self {
        Opcode(self.0 & 0xFFF0 | (nibble & 0xF) as u16)
    }

    /// Returns the `byte` corresponding to this opcode.
    ///
    /// This does not guarantee that the result is actually meaningful.
    fn byte(&self) -> u8 {
        self.0 as u8
    }

    /// Sets the `byte` corresponding to this opcode, returning a new opcode.
    fn with_byte(self, byte: u8) -> Self {
        Opcode(self.0 & 0xFF00 | byte as u16)
    }

    /// Returns the `addr` corresponding to this opcode.
    ///
    /// This does not guarantee that the result is actually meaningful.
    fn addr(&self) -> Result<Address, AddressOutOfBoundsError> {
        Address::from_u16(self.0 & 0xFFF)
    }

    /// Sets the `addr` corresponding to this opcode, returning a new opcode.
    fn with_addr(self, addr: Address) -> Self {
        Opcode(self.0 & 0xF000 | addr.addr() as u16)
    }
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{:04X}", self.0)
    }
}

impl From<Instruction> for Opcode {
    fn from(instr: Instruction) -> Self {
        use Instruction::*;

        match instr {
            Scd(n) => Opcode(0x00C0).with_nibble(n),
            Cls => Opcode(0x00E0),
            Ret => Opcode(0x00EE),
            Scr => Opcode(0x00FB),
            Scl => Opcode(0x00FC),
            Exit => Opcode(0x00FD),
            Low => Opcode(0x00FE),
            High => Opcode(0x00FF),
            Jp(addr) => Opcode(0x1000).with_addr(*addr),
            Call(addr) => Opcode(0x2000).with_addr(*addr),
            SeByte(vx, b) => Opcode(0x3000).with_vx(vx).with_byte(b),
            SneByte(vx, b) => Opcode(0x4000).with_vx(vx).with_byte(b),
            SeReg(vx, vy) => Opcode(0x5000).with_vx(vx).with_vy(vy),
            LdByte(vx, b) => Opcode(0x6000).with_vx(vx).with_byte(b),
            AddByte(vx, b) => Opcode(0x7000).with_vx(vx).with_byte(b),
            LdReg(vx, vy) => Opcode(0x8000).with_vx(vx).with_vy(vy),
            Or(vx, vy) => Opcode(0x8001).with_vx(vx).with_vy(vy),
            And(vx, vy) => Opcode(0x8002).with_vx(vx).with_vy(vy),
            Xor(vx, vy) => Opcode(0x8003).with_vx(vx).with_vy(vy),
            AddReg(vx, vy) => Opcode(0x8004).with_vx(vx).with_vy(vy),
            Sub(vx, vy) => Opcode(0x8005).with_vx(vx).with_vy(vy),
            Shr(vx) => Opcode(0x8006).with_vx(vx),
            ShrQuirk(vx, vy) => Opcode(0x8006).with_vx(vx).with_vy(vy),
            Subn(vx, vy) => Opcode(0x8007).with_vx(vx).with_vy(vy),
            Shl(vx) => Opcode(0x800E).with_vx(vx),
            ShlQuirk(vx, vy) => Opcode(0x800E).with_vx(vx).with_vy(vy),
            SneReg(vx, vy) => Opcode(0x9000).with_vx(vx).with_vy(vy),
            LdI(addr) => Opcode(0xA000).with_addr(addr),
            JpV0(addr) => Opcode(0xB000).with_addr(addr),
            Rnd(vx, b) => Opcode(0xC000).with_vx(vx).with_byte(b),
            Drw(vx, vy, n) => Opcode(0xD000).with_vx(vx).with_vy(vy).with_nibble(n),
            Skp(vx) => Opcode(0xE09E).with_vx(vx),
            Sknp(vx) => Opcode(0xE0A1).with_vx(vx),
            LdRegDt(vx) => Opcode(0xF007).with_vx(vx),
            LdKey(vx) => Opcode(0xF00A).with_vx(vx),
            LdDtReg(vx) => Opcode(0xF015).with_vx(vx),
            LdSt(vx) => Opcode(0xF018).with_vx(vx),
            AddI(vx) => Opcode(0xF01E).with_vx(vx),
            LdF(vx) => Opcode(0xF029).with_vx(vx),
            LdHf(vx) => Opcode(0xF030).with_vx(vx),
            LdB(vx) => Opcode(0xF033).with_vx(vx),
            LdDerefIReg(vx) => Opcode(0xF055).with_vx(vx),
            LdRegDerefI(vx) => Opcode(0xF065).with_vx(vx),
            LdRReg(vx) => Opcode(0xF075).with_vx(vx),
            LdRegR(vx) => Opcode(0xF085).with_vx(vx),
        }
    }
}

/// An address pointing to a Chip-8 memory location.
///
/// All addresses must be within the addressable range, and some addresses (but
/// not all) must be aligned on a 2-byte boundary.  The former condition is
/// guaranteed to be satisfied for any instance of this type; the latter
/// condition is satisfied by the `AlignedAddress` type, which can be produced
/// from an `Address` using the `aligned` method.
///
/// # Examples
///
/// Addresses must be within the proper bounds, and can be further verified as
/// properly aligned:
///
/// ```
/// use chip8::Address;
///
/// let addr = Address::from_u16(0x204).unwrap();
/// assert_eq!(addr.addr(), 0x204);
/// let aligned = addr.aligned().unwrap();
/// assert_eq!(aligned.addr(), 0x204);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Address(usize);

impl Address {
    /// Verifies whether the given `u16` address value is valid, returning the
    /// corresponding `Address` if it is.
    pub fn from_u16(addr: u16) -> Result<Self, AddressOutOfBoundsError> {
        Address::from_usize(addr as usize)
    }

    /// Verifies whether the given `usize` address is valid, returning the
    /// corresponding `Address` if it is.
    pub fn from_usize(addr: usize) -> Result<Self, AddressOutOfBoundsError> {
        if addr >= MEM_SIZE {
            Err(AddressOutOfBoundsError(addr))
        } else {
            Ok(Address(addr))
        }
    }

    /// Returns the value of the address.
    pub fn addr(&self) -> usize {
        self.0
    }

    /// Returns the corresponding `AlignedAddress` if the address is aligned,
    /// and an error if not.
    pub fn aligned(&self) -> Result<AlignedAddress, AddressMisalignedError> {
        if self.0 & 1 == 0 {
            Ok(AlignedAddress(*self))
        } else {
            Err(AddressMisalignedError(self.0))
        }
    }
}

impl Add<usize> for Address {
    type Output = Result<Self, AddressOutOfBoundsError>;

    fn add(self, rhs: usize) -> Self::Output {
        Address::from_usize(self.0 + rhs)
    }
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#{:03X}", self.0)
    }
}

/// A Chip-8 address which is guaranteed to be aligned.
///
/// An `AlignedAddress` is like an `Address` (and dereferences to one), but is
/// guaranteed to be aligned to a 2-byte boundary.  Thus, it is suitable for
/// use as a program counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AlignedAddress(Address);

impl AlignedAddress {
    /// Converts the given `usize` to an `AlignedAddress` if it is possible.
    pub fn from_usize(addr: usize) -> Result<AlignedAddress, Error> {
        Ok(Address::from_usize(addr)?.aligned()?)
    }
}

impl Add<usize> for AlignedAddress {
    type Output = Result<Self, Error>;

    fn add(self, rhs: usize) -> Self::Output {
        Ok((self.0 + rhs)?.aligned()?)
    }
}

impl Deref for AlignedAddress {
    type Target = Address;

    fn deref(&self) -> &Address {
        &self.0
    }
}

impl fmt::Display for AlignedAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A Chip-8 instruction.
///
/// See the manual for more complete explanations of what each operation does.
/// This is an internal representation used to make working with instructions
/// easier; if this type were not present, then opcodes would have to be
/// deciphered every time an instruction is used, which would quickly become
/// inconvenient.  Also, this type guarantees that the instruction it
/// represents is valid, so there is no need to check opcode validity on every
/// use.
///
/// # Examples
///
/// Instructions can be created from opcodes:
///
/// ```
/// use chip8::{Instruction, Opcode, Register};
///
/// // We don't use shift quirks in this example.
/// let instr = Instruction::from_opcode(Opcode(0x7510), false).unwrap();
/// assert_eq!(instr, Instruction::AddByte(Register::V5, 0x10));
/// ```
///
/// Invalid instructions, such as misaligned jumps, are not accepted:
///
/// ```
/// use chip8::{Instruction, Opcode};
///
/// assert!(Instruction::from_opcode(Opcode(0x1201), false).is_err());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    /// `SCD nibble` (`00Cn`).
    Scd(u8),
    /// `CLS` (`00E0`).
    Cls,
    /// `RET` (`00EE`).
    Ret,
    /// `SCR` (`00FB`).
    Scr,
    /// `SCL` (`00FC`).
    Scl,
    /// `EXIT` (`00FD`).
    Exit,
    /// `LOW` (`00FE`).
    Low,
    /// `HIGH` (`00FF`).
    High,
    /// `JP addr` (`1nnn`).
    Jp(AlignedAddress),
    /// `CALL addr` (`2nnn`).
    Call(AlignedAddress),
    /// `SE Vx, byte` (`3xkk`).
    SeByte(Register, u8),
    /// `SNE Vx, byte` (`4xkk`).
    SneByte(Register, u8),
    /// `SE Vx, Vy` (`5xy0`).
    SeReg(Register, Register),
    /// `LD Vx, byte` (`6xkk`).
    LdByte(Register, u8),
    /// `ADD Vx, byte` (`7xkk`).
    AddByte(Register, u8),
    /// `LD Vx, Vy` (`8xy0`).
    LdReg(Register, Register),
    /// `OR Vx, Vy` (`8xy1`).
    Or(Register, Register),
    /// `AND Vx, Vy` (`8xy2`).
    And(Register, Register),
    /// `XOR Vx, Vy` (`8xy3`).
    Xor(Register, Register),
    /// `ADD Vx, Vy` (`8xy4`).
    AddReg(Register, Register),
    /// `SUB Vx, Vy` (`8xy5`).
    Sub(Register, Register),
    /// `SHR Vx` (`8x06`).
    Shr(Register),
    /// `SHR Vx, Vy` (`8xy6`).
    ShrQuirk(Register, Register),
    /// `SUBN Vx, Vy` (`8xy7`).
    Subn(Register, Register),
    /// `SHL Vx` (`8x0E`).
    Shl(Register),
    /// `SHL Vx, Vy` (`8xyE`).
    ShlQuirk(Register, Register),
    /// `SNE Vx, Vy` (`9xy0`).
    SneReg(Register, Register),
    /// `LD I, addr` (`Annn`).
    LdI(Address),
    /// `JP V0, addr` (`Bnnn`).
    JpV0(Address),
    /// `RND Vx, byte` (`Cxkk`).
    Rnd(Register, u8),
    /// `DRW Vx, Vy, nibble` (`Dxyn`).
    Drw(Register, Register, u8),
    /// `SKP Vx` (`Ex9E`).
    Skp(Register),
    /// `SKNP Vx` (`ExA1`).
    Sknp(Register),
    /// `LD Vx, DT` (`Fx07`).
    LdRegDt(Register),
    /// `LD Vx, K` (`Fx0A`).
    LdKey(Register),
    /// `LD DT, Vx` (`Fx15`).
    LdDtReg(Register),
    /// `LD ST, Vx` (`Fx18`).
    LdSt(Register),
    /// `ADD I, Vx` (`Fx1E`).
    AddI(Register),
    /// `LD F, Vx` (`Fx29`).
    LdF(Register),
    /// `LD HF, Vx` (`Fx30`).
    LdHf(Register),
    /// `LD B, Vx` (`Fx33`).
    LdB(Register),
    /// `LD [I], Vx` (`Fx55`).
    LdDerefIReg(Register),
    /// `LD Vx, [I]` (`Fx65`).
    LdRegDerefI(Register),
    /// `LD R, Vx` (`Fx75`).
    LdRReg(Register),
    /// `LD Vx, R` (`Fx85`).
    LdRegR(Register),
}

impl Instruction {
    /// Returns the instruction corresponding to the given opcode.
    ///
    /// The `shift_quirks` parameter can be used to specify whether shift
    /// quirks mode should be used in the translation.  If it is `false` and a
    /// quirky shift instruction is encountered, the instruction will be
    /// rejected.
    pub fn from_opcode(opcode: Opcode, shift_quirks: bool) -> Result<Self, Error> {
        use self::Instruction::*;

        Ok(match (opcode.0 & 0xF000) >> 12 {
            0x0 => if opcode.0 & 0xF0 == 0xC0 {
                Scd(opcode.nibble())
            } else {
                match opcode.0 & 0xFF {
                    0xE0 => Cls,
                    0xEE => Ret,
                    0xFB => Scr,
                    0xFC => Scl,
                    0xFD => Exit,
                    0xFE => Low,
                    0xFF => High,
                    _ => Err(InvalidOpcodeError(opcode))?,
                }
            },
            0x1 => Jp(opcode.addr()?.aligned()?),
            0x2 => Call(opcode.addr()?.aligned()?),
            0x3 => SeByte(opcode.vx(), opcode.byte()),
            0x4 => SneByte(opcode.vx(), opcode.byte()),
            0x5 => if opcode.0 & 0xF == 0 {
                SeReg(opcode.vx(), opcode.vy())
            } else {
                Err(InvalidOpcodeError(opcode))?
            },
            0x6 => LdByte(opcode.vx(), opcode.byte()),
            0x7 => AddByte(opcode.vx(), opcode.byte()),
            0x8 => match opcode.0 & 0xF {
                0x0 => LdReg(opcode.vx(), opcode.vy()),
                0x1 => Or(opcode.vx(), opcode.vy()),
                0x2 => And(opcode.vx(), opcode.vy()),
                0x3 => Xor(opcode.vx(), opcode.vy()),
                0x4 => AddReg(opcode.vx(), opcode.vy()),
                0x5 => Sub(opcode.vx(), opcode.vy()),
                0x6 => if shift_quirks {
                    ShrQuirk(opcode.vx(), opcode.vy())
                } else if opcode.0 & 0xF0 == 0x00 {
                    Shr(opcode.vx())
                } else {
                    Err(InvalidOpcodeError(opcode))?
                },
                0x7 => Subn(opcode.vx(), opcode.vy()),
                0xE => if shift_quirks {
                    ShlQuirk(opcode.vx(), opcode.vy())
                } else if opcode.0 & 0xF0 == 0x00 {
                    Shl(opcode.vx())
                } else {
                    Err(InvalidOpcodeError(opcode))?
                },
                _ => Err(InvalidOpcodeError(opcode))?,
            },
            0x9 => if opcode.0 & 0xF == 0 {
                SneReg(opcode.vx(), opcode.vy())
            } else {
                Err(InvalidOpcodeError(opcode))?
            },
            0xA => LdI(opcode.addr()?),
            0xB => JpV0(opcode.addr()?),
            0xC => Rnd(opcode.vx(), opcode.byte()),
            0xD => Drw(opcode.vx(), opcode.vy(), opcode.nibble()),
            0xE => match opcode.0 & 0xFF {
                0x9E => Skp(opcode.vx()),
                0xA1 => Sknp(opcode.vx()),
                _ => Err(InvalidOpcodeError(opcode))?,
            },
            0xF => match opcode.0 & 0xFF {
                0x07 => LdRegDt(opcode.vx()),
                0x0A => LdKey(opcode.vx()),
                0x15 => LdDtReg(opcode.vx()),
                0x18 => LdSt(opcode.vx()),
                0x1E => AddI(opcode.vx()),
                0x29 => LdF(opcode.vx()),
                0x30 => LdHf(opcode.vx()),
                0x33 => LdB(opcode.vx()),
                0x55 => LdDerefIReg(opcode.vx()),
                0x65 => LdRegDerefI(opcode.vx()),
                0x75 => LdRReg(opcode.vx()),
                0x85 => LdRegR(opcode.vx()),
                _ => Err(InvalidOpcodeError(opcode))?,
            },
            _ => unreachable!("4-bit quantity didn't match 0-15"),
        })
    }

    /// Returns the address referenced by the instruction, if any.
    pub fn addr(&self) -> Option<Address> {
        use self::Instruction::*;

        match *self {
            Jp(addr) => Some(*addr),
            Call(addr) => Some(*addr),
            LdI(addr) => Some(addr),
            JpV0(addr) => Some(addr),
            _ => None,
        }
    }

    /// Formats the instruction into a string, using the given label name in
    /// place of any address operand that may be in the instruction.
    ///
    /// # Examples
    ///
    /// ```
    /// use chip8::{AlignedAddress, Instruction};
    ///
    /// let instr = Instruction::Call(AlignedAddress::from_usize(0x200).unwrap());
    /// assert_eq!(instr.to_string_with_address_label(Some("label")), "CALL label");
    /// ```
    pub fn to_string_with_address_label(&self, label: Option<&str>) -> String {
        use self::Instruction::*;

        if let Some(label) = label {
            match *self {
                Jp(_) => format!("JP {}", label),
                Call(_) => format!("CALL {}", label),
                LdI(_) => format!("LD I, {}", label),
                JpV0(_) => format!("JP V0, {}", label),
                _ => self.to_string(),
            }
        } else {
            self.to_string()
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Instruction::*;

        match *self {
            Scd(n) => write!(f, "SCD {}", n),
            Cls => write!(f, "CLS"),
            Ret => write!(f, "RET"),
            Scr => write!(f, "SCR"),
            Scl => write!(f, "SCL"),
            Exit => write!(f, "EXIT"),
            Low => write!(f, "LOW"),
            High => write!(f, "HIGH"),
            Jp(addr) => write!(f, "JP {}", addr),
            Call(addr) => write!(f, "CALL {}", addr),
            SeByte(reg, b) => write!(f, "SE {}, #{:02X}", reg, b),
            SneByte(reg, b) => write!(f, "SNE {}, #{:02X}", reg, b),
            SeReg(reg1, reg2) => write!(f, "SE {}, {}", reg1, reg2),
            LdByte(reg, b) => write!(f, "LD {}, #{:02X}", reg, b),
            AddByte(reg, b) => write!(f, "ADD {}, #{:02X}", reg, b),
            LdReg(reg1, reg2) => write!(f, "LD {}, {}", reg1, reg2),
            Or(reg1, reg2) => write!(f, "OR {}, {}", reg1, reg2),
            And(reg1, reg2) => write!(f, "AND {}, {}", reg1, reg2),
            Xor(reg1, reg2) => write!(f, "XOR {}, {}", reg1, reg2),
            AddReg(reg1, reg2) => write!(f, "ADD {}, {}", reg1, reg2),
            Sub(reg1, reg2) => write!(f, "SUB {}, {}", reg1, reg2),
            Shr(reg) => write!(f, "SHR {}", reg),
            ShrQuirk(reg1, reg2) => write!(f, "SHR {}, {}", reg1, reg2),
            Subn(reg1, reg2) => write!(f, "SUBN {}, {}", reg1, reg2),
            Shl(reg) => write!(f, "SHL {}", reg),
            ShlQuirk(reg1, reg2) => write!(f, "SHL {}, {}", reg1, reg2),
            SneReg(reg1, reg2) => write!(f, "SNE {}, {}", reg1, reg2),
            LdI(addr) => write!(f, "LD I, {}", addr),
            JpV0(addr) => write!(f, "JP V0, {}", addr),
            Rnd(reg, b) => write!(f, "RND {}, #{:02X}", reg, b),
            Drw(reg1, reg2, n) => write!(f, "DRW {}, {}, {}", reg1, reg2, n),
            Skp(reg) => write!(f, "SKP {}", reg),
            Sknp(reg) => write!(f, "SKNP {}", reg),
            LdRegDt(reg) => write!(f, "LD {}, DT", reg),
            LdKey(reg) => write!(f, "LD {}, K", reg),
            LdDtReg(reg) => write!(f, "LD DT, {}", reg),
            LdSt(reg) => write!(f, "LD ST, {}", reg),
            AddI(reg) => write!(f, "ADD I, {}", reg),
            LdF(reg) => write!(f, "LD F, {}", reg),
            LdHf(reg) => write!(f, "LD HF, {}", reg),
            LdB(reg) => write!(f, "LD B, {}", reg),
            LdDerefIReg(reg) => write!(f, "LD [I], {}", reg),
            LdRegDerefI(reg) => write!(f, "LD {}, [I]", reg),
            LdRReg(reg) => write!(f, "LD R, {}", reg),
            LdRegR(reg) => write!(f, "LD {}, R", reg),
        }
    }
}

#[cfg(test)]
mod tests {
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
            let new_instr = Instruction::from_opcode(Opcode(opcode), false).unwrap();
            assert_eq!(new_instr, *instr);
            let new_opcode: Opcode = new_instr.into();
            assert_eq!(new_opcode, Opcode(opcode));
        }
    }
}
