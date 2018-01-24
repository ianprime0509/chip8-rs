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

//! The Chip-8 assembler.
//!
//! The syntax used by the assembler is described in detail in the manual,
//! along with all the names of the operations.  See the documentation on the
//! `Assembler` struct for more details on how exactly it's implemented.

use std::collections::{HashMap, VecDeque};
use std::default::Default;
use std::fmt;
use std::ops::{Add, AddAssign};

use combine::Parser;
use failure::{Backtrace, Error, Fail};

use {Address, AddressOutOfBoundsError, AlignedAddress, Instruction, PROG_SIZE, PROG_START};
use util;

mod parse;

/// An error resulting from an attempt to give a new value to a label.
#[derive(Debug, Fail)]
#[fail(display = "label '{}' already has a value", _0)]
pub struct LabelAlreadyDefinedError(String);

/// An error resulting from having more than one label associated with a single
/// statement.
#[derive(Debug, Fail)]
#[fail(display = "more than one label found for the same statement")]
pub struct TooManyLabelsError;

/// An error produced during the first pass.
#[derive(Debug, Fail)]
#[fail(display = "in first pass: {}", _0)]
pub struct FirstPassError(String);

/// An error resulting from being given the wrong number of operands for an
/// operation.
#[derive(Debug, Fail)]
#[fail(display = "wrong number of operands to '{}': expected {}, got {}", operation, expected, got)]
pub struct WrongOperandsError {
    pub operation: String,
    pub expected: usize,
    pub got: usize,
}

/// Fails immediately with an error if the wrong number of operands was given.
macro_rules! expect_operands {
    ($op:expr, $expected:expr, $got:expr) => {
        if $expected != $got {
            return Err(WrongOperandsError {
                operation: $op.to_owned(),
                expected: $expected,
                got: $got
            }.into());
        }
    }
}

/// An error resulting from the use of an unknown operation.
#[derive(Debug, Fail)]
#[fail(display = "unknown operation '{}'", _0)]
pub struct UnknownOperationError(String);

/// An error with an associated line number.
#[derive(Debug)]
pub struct ErrorWithLine {
    /// The line number where the error occurred.
    line: usize,
    /// The underlying error.
    inner: Error,
}

impl fmt::Display for ErrorWithLine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "on line {}: {}", self.line, self.inner)
    }
}

impl Fail for ErrorWithLine {
    fn cause(&self) -> Option<&Fail> {
        Some(self.inner.cause())
    }

    fn backtrace(&self) -> Option<&Backtrace> {
        Some(self.inner.backtrace())
    }
}

/// Options for use with the assembler.
pub struct Options {
    /// Whether to use shift quirks mode.
    pub shift_quirks: bool,
}

impl Options {
    /// Returns the default set of options.
    pub fn new() -> Self {
        Options { shift_quirks: true }
    }
}

impl Default for Options {
    fn default() -> Self {
        Options::new()
    }
}

/// A nesting type, which specifies whether we're skipping an `IF` or and
/// `ELSE` block.
///
/// For example, if we're skipping an `IF` block, then we should stop doing so
/// when we reach the corresponding `ELSE` or `ENDIF`.
enum NestingType {
    /// An `IF` block.
    If,
    /// An `ELSE` block.
    Else,
}

/// An error resulting from an out-of-bounds `ProgramIndex` being accessed.
#[derive(Debug, Fail)]
#[fail(display = "program index is out of bounds: {:#04X}", _0)]
pub struct ProgramIndexOutOfBoundsError(usize);

/// An error resulting from attempting to create a `ProgramIndex` referencing
/// the reserved interpreter area.
#[derive(Debug, Fail)]
#[fail(display = "address points to reserved interpreter area: {}", _0)]
pub struct ReservedAddressError(Address);

/// An index into a Chip-8 program.
///
/// This type is intended to make implementing the assembler a little easier by
/// not requiring constant bounds checks on the program index and making
/// conversions to/from `Address`es easier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProgramIndex(usize);

impl ProgramIndex {
    /// Returns a new `ProgramIndex` wrapping the given index.
    ///
    /// No bounds checks are performed on creation; bounds checking is only
    /// done when the index is used.  This is intended to make it possible to
    /// assemble programs which take up all usable space; if bounds checks were
    /// performed on creation, then a program attempting to assemble an
    /// instruction into the last two usable bytes would cause an error, since
    /// the program index would be incremented past the end of the buffer (even
    /// though it would never be accessed at that location).
    pub fn new(index: usize) -> Self {
        ProgramIndex(index)
    }

    /// Returns the `Address` corresponding to this index.
    pub fn address(&self) -> Result<Address, AddressOutOfBoundsError> {
        Address::from_usize(self.0 + PROG_START)
    }

    /// Aligns the index to the next two-byte boundary, if it is not already
    /// aligned.
    pub fn align(&mut self) {
        self.0 = (self.0 + 1) & !1;
    }

    /// Returns the index, as long as it is in bounds.
    pub fn index(&self) -> Result<usize, ProgramIndexOutOfBoundsError> {
        if self.0 < PROG_SIZE {
            Ok(self.0)
        } else {
            Err(ProgramIndexOutOfBoundsError(self.0))
        }
    }
}

impl Add<usize> for ProgramIndex {
    type Output = ProgramIndex;

    fn add(self, other: usize) -> ProgramIndex {
        ProgramIndex(self.0 + other)
    }
}

impl AddAssign<usize> for ProgramIndex {
    fn add_assign(&mut self, other: usize) {
        self.0 += other;
    }
}

/// An instruction after being processed by the first pass.
#[derive(Debug)]
struct FirstPassInstruction {
    /// The line number of the instruction.
    line: usize,
    /// The program index where the instruction should be put.
    index: ProgramIndex,
    /// The operation name.
    operation: String,
    /// The operands.
    operands: Vec<String>,
}

impl FirstPassInstruction {
    /// Attempts to compile this instruction into an `Instruction`.
    ///
    /// If this fails, the returned error will have the line number which was
    /// stored in this instance.
    pub fn compile(self, ltable: &HashMap<String, u16>) -> Result<Instruction, ErrorWithLine> {
        let line = self.line;
        self.compile_inner(ltable)
            .map_err(|e| ErrorWithLine { line, inner: e })
    }

    /// The actual logic for `compile`, but without a line number on the error
    /// (for convenience).
    fn compile_inner(mut self, ltable: &HashMap<String, u16>) -> Result<Instruction, Error> {
        use Instruction::*;
        use self::parse::eval;

        self.operation.make_ascii_uppercase();
        let op = self.operation.as_str();
        let ops = self.operands;
        let lt = ltable;

        Ok(match op {
            "SCD" => {
                expect_operands!(op, 1, ops.len());
                Scd(eval(&ops[0], lt)? as u8)
            }
            "CLS" => {
                expect_operands!(op, 0, ops.len());
                Cls
            }
            "RET" => {
                expect_operands!(op, 0, ops.len());
                Ret
            }
            "SCR" => {
                expect_operands!(op, 0, ops.len());
                Scr
            }
            "SCL" => {
                expect_operands!(op, 0, ops.len());
                Scl
            }
            "EXIT" => {
                expect_operands!(op, 0, ops.len());
                Exit
            }
            "LOW" => {
                expect_operands!(op, 0, ops.len());
                Low
            }
            "HIGH" => {
                expect_operands!(op, 0, ops.len());
                High
            }
            "JP" => {
                if ops[0].eq_ignore_ascii_case("V0") {
                    expect_operands!("JP V0", 1, ops.len() - 1);
                    JpV0(Address::from_u16(eval(&ops[1], lt)?)?)
                } else {
                    expect_operands!(op, 1, ops.len());
                    Jp(AlignedAddress::from_usize(eval(&ops[0], lt)? as usize)?)
                }
            }
            "CALL" => {
                expect_operands!(op, 1, ops.len());
                Call(AlignedAddress::from_usize(eval(&ops[0], lt)? as usize)?)
            }
            "SE" => {
                expect_operands!(op, 2, ops.len());
                if let Ok(vy) = ops[1].parse() {
                    SeReg(ops[0].parse()?, vy)
                } else {
                    SeByte(ops[0].parse()?, eval(&ops[1], lt)? as u8)
                }
            }
            "SNE" => {
                expect_operands!(op, 2, ops.len());
                if let Ok(vy) = ops[1].parse() {
                    SneReg(ops[0].parse()?, vy)
                } else {
                    SneByte(ops[0].parse()?, eval(&ops[1], lt)? as u8)
                }
            }
            "LD" => {
                expect_operands!(op, 2, ops.len());
                // We have a lot of overloads here, and we need to check the
                // most specific ones first.  Let's start by checking the ones
                // with special first arguments, then check the ones with
                // special second arguments, and then check the register/byte
                // variants.
                if ops[0].eq_ignore_ascii_case("I") {
                    LdI(Address::from_u16(eval(&ops[1], lt)?)?)
                } else if ops[0].eq_ignore_ascii_case("DT") {
                    LdDtReg(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("ST") {
                    LdSt(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("F") {
                    LdF(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("HF") {
                    LdHf(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("B") {
                    LdB(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("[I]") {
                    LdDerefIReg(ops[1].parse()?)
                } else if ops[0].eq_ignore_ascii_case("R") {
                    LdRReg(ops[1].parse()?)
                } else if ops[1].eq_ignore_ascii_case("DT") {
                    LdRegDt(ops[0].parse()?)
                } else if ops[1].eq_ignore_ascii_case("[I]") {
                    LdRegDerefI(ops[0].parse()?)
                } else if ops[1].eq_ignore_ascii_case("R") {
                    LdRegR(ops[0].parse()?)
                } else if let Ok(vy) = ops[1].parse() {
                    LdReg(ops[0].parse()?, vy)
                } else {
                    LdByte(ops[0].parse()?, eval(&ops[1], lt)? as u8)
                }
            }
            "ADD" => {
                expect_operands!(op, 2, ops.len());
                if ops[0].eq_ignore_ascii_case("I") {
                    AddI(ops[1].parse()?)
                } else if let Ok(vy) = ops[1].parse() {
                    AddReg(ops[0].parse()?, vy)
                } else {
                    AddByte(ops[0].parse()?, eval(&ops[1], lt)? as u8)
                }
            }
            "OR" => {
                expect_operands!(op, 2, ops.len());
                Or(ops[0].parse()?, ops[1].parse()?)
            }
            "AND" => {
                expect_operands!(op, 2, ops.len());
                And(ops[0].parse()?, ops[1].parse()?)
            }
            "XOR" => {
                expect_operands!(op, 2, ops.len());
                Xor(ops[0].parse()?, ops[1].parse()?)
            }
            "SUB" => {
                expect_operands!(op, 2, ops.len());
                Sub(ops[0].parse()?, ops[1].parse()?)
            }
            "SHR" => {
                if ops.len() == 2 {
                    ShrQuirk(ops[0].parse()?, ops[1].parse()?)
                } else {
                    expect_operands!(op, 1, ops.len());
                    Shr(ops[0].parse()?)
                }
            }
            "SUBN" => {
                expect_operands!(op, 2, ops.len());
                Subn(ops[0].parse()?, ops[1].parse()?)
            }
            "SHL" => {
                if ops.len() == 2 {
                    ShlQuirk(ops[0].parse()?, ops[1].parse()?)
                } else {
                    expect_operands!(op, 1, ops.len());
                    Shl(ops[0].parse()?)
                }
            }
            "RND" => {
                expect_operands!(op, 2, ops.len());
                Rnd(ops[0].parse()?, eval(&ops[1], lt)? as u8)
            }
            "DRW" => {
                expect_operands!(op, 3, ops.len());
                Drw(ops[0].parse()?, ops[1].parse()?, eval(&ops[2], lt)? as u8)
            }
            "SKP" => {
                expect_operands!(op, 1, ops.len());
                Skp(ops[0].parse()?)
            }
            "SKNP" => {
                expect_operands!(op, 1, ops.len());
                Sknp(ops[0].parse()?)
            }
            op => return Err(UnknownOperationError(op.to_owned()).into()),
        })
    }
}

/// A Chip-8 assembler.
///
/// This is a pretty straight-forward two-pass assembler: the first pass goes
/// through and parses the assembly syntax, assigning values to labels and
/// storing the instructions it finds, while the second pass actually processes
/// the instructions so that it can substitute any label values that it needs.
pub struct Assembler {
    /// The program buffer where assembly output will be stored.
    program: [u8; PROG_SIZE],
    /// The current index in the program buffer.
    index: ProgramIndex,
    /// The current input line.
    line: usize,
    /// A queue containing instructions after the first pass.
    instructions: VecDeque<FirstPassInstruction>,
    /// The label that should be associated with the next instruction
    /// processed.
    ///
    /// The reason why this label is held until the corresponding instruction
    /// is processed is because there could be alignment issues that the
    /// assembler can't know about until it actually sees the next instruction.
    /// Per the manual, we also don't allow more than one label per
    /// instruction.
    label: Option<String>,
    /// A map of label names to addresses for the labels that have been found
    /// in the first pass.
    label_table: HashMap<String, u16>,
    /// The current level of `IF`/`ENDIF` nesting that the assembler is in.
    ///
    /// The usual level is `0`, and is increased by one every time we enter a
    /// new `IF` block.
    if_nest_level: u32,
    /// The current level and type of the block that we're skipping.
    ///
    /// We need both level and type so that we can handle nested `IF` blocks
    /// correctly.  If this is `None`, then we aren't skipping anything.
    if_skip: Option<(u32, NestingType)>,

    /// Whether to use shift quirks mode.
    shift_quirks: bool,
}

impl Assembler {
    /// Returns a new assembler using the default options.
    pub fn new() -> Self {
        Assembler::with_options(Options::default())
    }

    /// Returns a new assembler using the given options.
    pub fn with_options(options: Options) -> Self {
        Assembler {
            program: [0; PROG_SIZE],
            index: ProgramIndex::new(0),
            line: 1,
            instructions: VecDeque::new(),
            label: None,
            label_table: HashMap::new(),
            if_nest_level: 0,
            if_skip: None,
            shift_quirks: options.shift_quirks,
        }
    }

    /// Performs the second pass on all instructions in the queue, emitting the
    /// resulting opcodes into the program buffer.
    pub fn emit(&mut self) -> Result<(), ErrorWithLine> {
        for ins in self.instructions.drain(..) {
            let instr = ins.compile(&self.label_table)?;
            println!("{}", instr);
        }

        Ok(())
    }

    /// Performs the first pass on the given line.
    pub fn process_line(&mut self, line: &str) -> Result<(), ErrorWithLine> {
        self.process_line_inner(line).map_err(|e| ErrorWithLine {
            line: self.line,
            inner: e,
        })?;
        self.line += 1;
        Ok(())
    }

    /// The actual logic for `process_line` which returns a normal `Result<(),
    /// Error>`.
    fn process_line_inner(&mut self, line: &str) -> Result<(), Error> {
        let parsed = parse::line()
            .parse(line)
            .map_err(|e| FirstPassError(util::format_parse_error(&e)))?
            .0;

        if let Some(lbl) = parsed.0 {
            if self.label.is_some() {
                return Err(TooManyLabelsError.into());
            } else {
                self.label = Some(lbl);
            }
        }
        if let Some((operation, operands)) = parsed.1 {
            self.first_pass_instruction(operation, operands)?;
        }

        Ok(())
    }

    /// Assigns the given value to the given (case-insensitive) label.
    fn define_label(&mut self, label: &str, value: u16) -> Result<(), LabelAlreadyDefinedError> {
        match self.label_table.insert(label.to_owned(), value) {
            Some(_) => Err(LabelAlreadyDefinedError(label.to_owned())),
            None => Ok(()),
        }
    }

    /// Performs the first pass on the given instruction (operation and
    /// operands).
    ///
    /// This will add the instruction to the instruction buffer, after
    /// adjusting the program index for alignment and dealing with the
    /// associated label (if present).
    fn first_pass_instruction(
        &mut self,
        operation: String,
        operands: Vec<String>,
    ) -> Result<(), Error> {
        if operation.eq_ignore_ascii_case("DB") {
            self.add_first_pass_instruction(operation, operands)?;
            self.index += 1;
        } else if operation.eq_ignore_ascii_case("DW") {
            self.add_first_pass_instruction(operation, operands)?;
            self.index += 2;
        } else {
            self.index.align();
            self.add_first_pass_instruction(operation, operands)?;
            self.index += 2;
        }

        Ok(())
    }

    /// Adds the given instruction (operation and operands) to the first pass
    /// instructions queue.
    ///
    /// The line and program index will be determined from the current state of
    /// the assembler, and the current label will also be processed.
    fn add_first_pass_instruction(
        &mut self,
        operation: String,
        operands: Vec<String>,
    ) -> Result<(), Error> {
        self.instructions.push_back(FirstPassInstruction {
            line: self.line,
            index: self.index,
            operation,
            operands,
        });
        if let Some(lbl) = self.label.take() {
            let addr = self.index.address()?.addr();
            self.define_label(&lbl, addr as u16)?;
            self.label = None;
        }

        Ok(())
    }
}
