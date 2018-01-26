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
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::ops::{Add, AddAssign};

use combine::Parser;
use failure::{Backtrace, Error, Fail, ResultExt};

use {Address, AddressOutOfBoundsError, AlignedAddress, Instruction, Opcode, PROG_SIZE, PROG_START};
use util;

mod parse;

/// An error resulting from an attempt to give a new value to a label.
#[derive(Debug, Fail)]
#[fail(display = "label '{}' already has a value", _0)]
pub struct LabelAlreadyDefinedError(pub String);

/// An error resulting from having more than one label associated with a single
/// statement.
#[derive(Debug, Fail)]
#[fail(display = "more than one label found for the same statement")]
pub struct TooManyLabelsError;

/// An error produced during the first pass.
#[derive(Debug, Fail)]
#[fail(display = "in first pass: {}", _0)]
pub struct FirstPassError(pub String);

/// An error resulting from being given the wrong number of operands for an
/// operation.
#[derive(Debug, Fail)]
#[fail(display = "wrong number of operands to '{}': expected {}, got {}", operation, expected, got)]
pub struct WrongOperandsError {
    pub operation: String,
    pub expected: usize,
    pub got: usize,
}

impl WrongOperandsError {
    /// Returns an error if the expected number of operands is given from the
    /// actual number given.
    pub fn test(operation: &str, expected: usize, got: usize) -> Result<(), Self> {
        if expected != got {
            Err(WrongOperandsError {
                operation: operation.to_owned(),
                expected,
                got,
            })
        } else {
            Ok(())
        }
    }
}

/// Fails immediately with an error if the wrong number of operands was given.
macro_rules! expect_operands {
    ($op:expr, $expected:expr, $got:expr) => {
        WrongOperandsError::test($op, $expected, $got)?
    }
}

/// An error resulting from the use of an unknown operation.
#[derive(Debug, Fail)]
#[fail(display = "unknown operation '{}'", _0)]
pub struct UnknownOperationError(String);

/// An error resulting from an unclosed conditional block.
#[derive(Debug, Fail)]
#[fail(display = "unclosed conditional block; expected 'ENDIF'")]
pub struct UnclosedConditionalError;

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
    pub fn compile(
        self,
        ltable: &HashMap<String, u16>,
        shift_quirks: bool,
    ) -> Result<Instruction, ErrorWithLine> {
        let line = self.line;
        self.compile_inner(ltable, shift_quirks)
            .map_err(|e| ErrorWithLine { line, inner: e })
    }

    /// The actual logic for `compile`, but without a line number on the error
    /// (for convenience).
    fn compile_inner(
        mut self,
        ltable: &HashMap<String, u16>,
        shift_quirks: bool,
    ) -> Result<Instruction, Error> {
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
                if !ops.is_empty() && ops[0].eq_ignore_ascii_case("V0") {
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
                } else if ops[1].eq_ignore_ascii_case("K") {
                    LdKey(ops[0].parse()?)
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
                if shift_quirks || ops.len() == 2 {
                    expect_operands!(op, 2, ops.len());
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
                if shift_quirks || ops.len() == 2 {
                    expect_operands!(op, 2, ops.len());
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

    /// Assembles the given input program, writing the result (as binary data)
    /// to the given output.
    ///
    /// This consumes the assembler, because using the same `Assembler` for two
    /// different programs would have unexpected results (it would be
    /// equivalent to assembling the concatenation of the two inputs; if this
    /// is desired, you can just concatenate the inputs before passing them to
    /// this function).
    pub fn assemble<R: Read, W: Write>(
        mut self,
        input: &mut R,
        output: &mut W,
    ) -> Result<(), Error> {
        let input = BufReader::new(input);
        for line in input.lines() {
            self.process_line(&line?)?;
        }

        self.emit()?;
        // We only want to output the data in the program buffer that actually
        // matters, and not the empty data at the end.  Thus, we only output up
        // through the last non-zero byte in the program buffer.
        let last = self.program
            .iter()
            .rposition(|&b| b != 0)
            .map(|pos| pos + 1)
            .unwrap_or(self.program.len());
        let mut output = BufWriter::new(output);
        output.write_all(&self.program[..last])?;

        if let Some(lbl) = self.label {
            warn!(
                "found label '{}' at end of file with nothing to refer to",
                lbl
            );
        }
        if self.if_nest_level != 0 {
            return Err(UnclosedConditionalError.into());
        }

        Ok(())
    }

    /// Performs the second pass on all instructions in the queue, emitting the
    /// resulting opcodes into the program buffer.
    fn emit(&mut self) -> Result<(), ErrorWithLine> {
        // TODO: this code is somewhat ugly and might be able to be cleaned up
        // a bit.
        use self::parse::eval;

        let mut opcodes = VecDeque::with_capacity(self.instructions.len());
        // We need another queue to store any individual bytes that are
        // generated using `DB`.
        let mut bytes = VecDeque::new();
        for ins in self.instructions.drain(..) {
            let index = ins.index;
            let line = ins.line;
            match ins.operation.as_str() {
                "DW" => {
                    WrongOperandsError::test("DW", 1, ins.operands.len()).map_err(|e| {
                        ErrorWithLine {
                            line,
                            inner: e.into(),
                        }
                    })?;
                    opcodes.push_back((
                        index,
                        line,
                        Opcode(eval(&ins.operands[0], &self.label_table)
                            .map_err(|e| ErrorWithLine { line, inner: e })?),
                    ));
                }
                "DB" => {
                    WrongOperandsError::test("DW", 1, ins.operands.len()).map_err(|e| {
                        ErrorWithLine {
                            line,
                            inner: e.into(),
                        }
                    })?;
                    bytes.push_back((
                        index,
                        line,
                        eval(&ins.operands[0], &self.label_table)
                            .map_err(|e| ErrorWithLine { line, inner: e })?
                            as u8,
                    ));
                }
                _ => {
                    let instr = ins.compile(&self.label_table, self.shift_quirks)?;
                    opcodes.push_back((index, line, instr.into()));
                }
            }
        }

        // Having a separate loop to process all the opcodes is necessary to
        // satisfy the borrow checker; we can't insert an instruction while
        // we're draining the instructions queue, because both operations
        // require a mutable borrow of `self`.
        for (index, line, instr) in opcodes.drain(..) {
            self.insert_opcode(instr, index)
                .context("resulting program is too big")
                .map_err(|e| ErrorWithLine {
                    line,
                    inner: e.into(),
                })?;
        }
        for (index, line, byte) in bytes.drain(..) {
            let idx = index
                .index()
                .context("resulting program is too big")
                .map_err(|e| ErrorWithLine {
                    line,
                    inner: e.into(),
                })?;
            self.program[idx] = byte;
        }

        Ok(())
    }

    /// Inserts the given opcode at the given program location.
    fn insert_opcode(
        &mut self,
        opcode: Opcode,
        index: ProgramIndex,
    ) -> Result<(), ProgramIndexOutOfBoundsError> {
        let (b1, b2) = opcode.bytes();
        self.program[index.index()?] = b1;
        self.program[(index + 1).index()?] = b2;
        Ok(())
    }

    /// Performs the first pass on the given line.
    fn process_line(&mut self, line: &str) -> Result<(), ErrorWithLine> {
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
        use self::parse::Line;

        let parsed = parse::line()
            .parse(line)
            .map_err(|e| FirstPassError(util::format_parse_error(&e)))?
            .0;

        match parsed {
            Line::Assignment(lbl, expr) => {
                if self.should_process() {
                    let value = parse::eval(&expr, &self.label_table)?;
                    self.define_label(&lbl, value)?;
                }
            }
            Line::Instruction(lbl, instruction) => {
                if let Some(lbl) = lbl {
                    if self.label.is_some() {
                        return Err(TooManyLabelsError.into());
                    } else {
                        self.label = Some(lbl);
                    }
                }
                if let Some((operation, operands)) = instruction {
                    self.first_pass_instruction(operation, operands)?;
                }
            }
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
        use self::parse;

        if operation.eq_ignore_ascii_case("IFDEF") {
            expect_operands!("IFDEF", 1, operands.len());

            self.if_nest_level += 1;
            // Parsing the identifer from the operand here was the simplest way
            // I could think of to verify that the given operand really is an
            // identifier.  There's an extra copy involved which isn't terribly
            // efficient, but it probably doesn't matter.
            let ident = parse::ident_only(&operands[0])?;
            if self.should_process() && !self.label_table.contains_key(&ident) {
                self.if_skip = Some((self.if_nest_level, NestingType::If));
            }
        } else if operation.eq_ignore_ascii_case("IFNDEF") {
            expect_operands!("IFNDEF", 1, operands.len());

            self.if_nest_level += 1;
            let ident = parse::ident_only(&operands[0])?;
            if self.should_process() && self.label_table.contains_key(&ident) {
                self.if_skip = Some((self.if_nest_level, NestingType::If));
            }
        } else if operation.eq_ignore_ascii_case("ELSE") {
            expect_operands!("ELSE", 0, operands.len());

            // There are a few cases to consider here, and they should mostly
            // be self-explanatory.  The `if_skip` member contains the nesting
            // level and the type of the thing we're skipping, making it easy
            // to check if we should stop skipping an IF block or if we
            // encountered some error (like a double ELSE block or an ELSE
            // outside any conditional structure).
            match self.if_skip {
                Some((lvl, NestingType::If)) if lvl == self.if_nest_level => self.if_skip = None,
                Some((lvl, NestingType::Else)) if lvl == self.if_nest_level => {
                    return Err(FirstPassError("unexpected duplicate 'ELSE' found".into()).into())
                }
                None => if self.if_nest_level != 0 {
                    self.if_skip = Some((self.if_nest_level, NestingType::Else));
                } else {
                    return Err(FirstPassError(
                        "unexpected 'ELSE' found outside of conditional block".into(),
                    ).into());
                },
                _ => {}
            }
        } else if operation.eq_ignore_ascii_case("ENDIF") {
            expect_operands!("ENDIF", 0, operands.len());

            // This is pretty similar to the `match` statement for `ELSE`, but
            // a little simpler since we don't have to consider what type of
            // block we might be skipping.
            match self.if_skip {
                Some((lvl, _)) if lvl == self.if_nest_level => self.if_skip = None,
                None if self.if_nest_level == 0 => {
                    return Err(FirstPassError(
                        "unexpected 'ENDIF' found outside of conditional block".into(),
                    ).into())
                }
                _ => {}
            }
            self.if_nest_level -= 1;
        } else if operation.eq_ignore_ascii_case("DEFINE") {
            expect_operands!("DEFINE", 1, operands.len());

            let ident = parse::ident_only(&operands[0])?;
            if self.should_process() {
                self.define_label(&ident, 0)?;
            }
        } else if operation.eq_ignore_ascii_case("DB") {
            if self.should_process() {
                self.add_first_pass_instruction(operation, operands)?;
                self.index += 1;
            }
        } else if operation.eq_ignore_ascii_case("DW") {
            if self.should_process() {
                self.add_first_pass_instruction(operation, operands)?;
                self.index += 2;
            }
        } else {
            if self.should_process() {
                self.index.align();
                self.add_first_pass_instruction(operation, operands)?;
                self.index += 2;
            }
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

    /// Returns whether the assembler should be processing instructions.
    ///
    /// This returns `false` if, for example, we're inside a conditional
    /// assembly block whose condition was not satisfied.
    fn should_process(&self) -> bool {
        self.if_skip.is_none()
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use {Address, AlignedAddress, Assembler};

    /// Tests basic instruction assembly.
    ///
    /// This tests whether input strings get assembled down to the correct
    /// instructions, where the input strings may have strange variations in
    /// case (etc.) and other minor bits that might make them more difficult to
    /// assemble.
    #[test]
    fn single_instructions() {
        use Instruction::*;
        use Register::*;

        let cases = vec![
            ("scd #A", Scd(0xA)),
            ("    cLs    \t\t   ", Cls),
            ("\tRET", Ret),
            ("SCR", Scr),
            ("Scl", Scl),
            ("EXIT  ; Exits the program", Exit),
            ("  LOW", Low),
            ("high\t", High),
            (
                "jp #200 + $10",
                Jp(AlignedAddress::from_usize(0x200 + 0b10).unwrap()),
            ),
            (
                "\tCaLL 301 * 2\t",
                Call(AlignedAddress::from_usize(301 * 2).unwrap()),
            ),
            ("SE    vD   ,\t #45 > 2  ", SeByte(VD, 0x45 >> 2)),
            ("\tSne   \tVa\t,\t  75 / 2\t", SneByte(VA, 75 / 2)),
            ("se  v7, V8 ;; comments are fun ;;", SeReg(V7, V8)),
            ("  LD  v2,  $10101 < 3;2", LdByte(V2, 0b10101 << 3)),
            ("ADD  VC  ,255", AddByte(VC, 255)),
            (" ld v8, V3;V4\t", LdReg(V8, V3)),
            ("\tOR  V1, vF\t", Or(V1, VF)),
            ("aND\tv0 ,\tv1", And(V0, V1)),
            ("XoR   V8, va;", Xor(V8, VA)),
            ("add  v7, v7;;;;;", AddReg(V7, V7)),
            ("suB v8 ,V9", Sub(V8, V9)),
            (" SHR v1", Shr(V1)),
            ("   sHr v8, v0", ShrQuirk(V8, V0)),
            ("SUBN V0, V0", Subn(V0, V0)),
            ("SHL v9", Shl(V9)),
            ("SHl v8, v2", ShlQuirk(V8, V2)),
            ("sne v6, ve", SneReg(V6, VE)),
            (
                "LD  i \t,  #201;#201",
                LdI(Address::from_usize(0x201).unwrap()),
            ),
            (
                "jp   V0 , #300\t",
                JpV0(Address::from_usize(0x300).unwrap()),
            ),
            ("RnD  v9 , - (1) \t", Rnd(V9, 255)),
            ("\tDRW\tVA\t,\tVB\t,\t$101\t;", Drw(VA, VB, 0b101)),
            ("  skp  v8", Skp(V8)),
            ("sKnP   v9", Sknp(V9)),
            ("  ld  v9\t,\t dt;", LdRegDt(V9)),
            ("  LD   VA , k", LdKey(VA)),
            ("lD\tdT,\tV0", LdDtReg(V0)),
            ("LD ST, V9", LdSt(V9)),
            ("aDD  I , V7", AddI(V7)),
            ("ld  f, v2", LdF(V2)),
            ("ld  HF   , Va", LdHf(VA)),
            ("LD B, V8", LdB(V8)),
            ("LD [i] , v3", LdDerefIReg(V3)),
            ("ld   vA, [I]\t;", LdRegDerefI(VA)),
            ("ld  R,  v8", LdRReg(V8)),
            ("Ld  v9 , r", LdRegR(V9)),
        ];

        let mut asm = Assembler::new();
        for &(ref instr, _) in cases.iter() {
            if let Err(e) = asm.process_line(instr) {
                panic!("assembly of {:?} failed: {}", instr, e);
            }
        }

        let ltable = asm.label_table.clone();
        for (first_passed, (_, instr)) in asm.instructions.into_iter().zip(cases.into_iter()) {
            let assembled = match first_passed.compile(&ltable, false) {
                Ok(a) => a,
                Err(e) => panic!("second pass of {:?} failed: {}", instr, e),
            };
            assert_eq!(assembled, instr);
        }
    }

    /// Tests the `DB` and `DW` pseudo-operations, focusing on proper alignment
    /// of instructions.
    #[test]
    fn declare_alignment() {
        // A simple program that will check alignment details.
        let prog = "DW #1234
DB #56
DW #789A
DB #BC
DB #DE
EXIT";
        let asm = Assembler::new();
        let mut input = Cursor::new(prog);
        let mut output = Vec::new();
        let expected = [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0x00, 0x00, 0xFD];

        asm.assemble(&mut input, &mut output)
            .expect("failed to assemble test program");
        assert_eq!(output.as_slice(), &expected);
    }

    /// Tests labelled lines.
    #[test]
    fn labelled_lines() {
        // This is just a simple program that tests the basic possible label
        // configurations.
        let prog = "lbl: JP lbl2
lbl2:
        JP lbl
lbl3:   CALL lbl3";
        let asm = Assembler::new();
        let mut input = Cursor::new(prog);
        let mut output = Vec::new();
        let expected = [0x12, 0x02, 0x12, 0x00, 0x22, 0x04];

        asm.assemble(&mut input, &mut output)
            .expect("failed to assemble test program");
        assert_eq!(output.as_slice(), &expected);
    }

    /// Tests assignment statements.
    #[test]
    fn assignment() {
        // The test cases, in the format `(input line, label, value)`.
        let cases = [
            ("label = 5", "label", 5),
            ("     \tspacing\t=\t  70 ; comment", "spacing", 70),
            ("  expr =    5 + 8", "expr", 5 + 8),
            ("   a_test    =   expr + 7 ; wow", "a_test", 5 + 8 + 7),
        ];
        let mut asm = Assembler::new();

        for &(input, label, val) in &cases {
            if let Err(e) = asm.process_line(input) {
                panic!("assembly of {:?} failed: {}", input, e);
            }
            let assigned = match asm.label_table.get(label) {
                Some(&val) => val,
                None => panic!("label '{}' was not assigned", label),
            };
            assert_eq!(assigned, val, "incorrect processing of {:?}", input);
        }
    }

    /// Tests conditional assembly.
    #[test]
    fn conditional() {
        // A simple test program.
        let prog = "DEFINE COND
IFDEF COND
IFDEF NOTHING
DB 0
DEFINE BAD
ELSE
DB 1
ENDIF
ELSE
IFDEF NOTHING
DB 2
BAD2 = 1
ELSE
DB 3
ENDIF
ENDIF

IFDEF BAD
DB 4 + BAD2
ENDIF
IFNDEF BAD
DB 5
ENDIF";
        let asm = Assembler::new();
        let mut input = Cursor::new(prog);
        let mut output = Vec::new();
        let expected = [1, 5];

        asm.assemble(&mut input, &mut output)
            .expect("failed to assemble test program");
        assert_eq!(output.as_slice(), &expected);
    }

    /// Tests expected conditional assembly failure.
    #[test]
    fn conditional_failure() {
        // Some test programs, each of which should fail assembly.
        let progs = [
            "ELSE",
            "IFDEF",
            "ENDIF",
            "IFDEF UNDEFINED",
            "IFNDEF A
DW 0
ELSE
DW 1
ELSE
DW 2
ENDIF",
            "IFDEF A
IFDEF B
IFDEF C
ELSE
IFDEF D
ENDIF
ENDIF
ENDIF",
        ];

        for prog in &progs {
            let asm = Assembler::new();
            let mut input = Cursor::new(prog);
            let mut output = Vec::new();
            assert!(
                asm.assemble(&mut input, &mut output).is_err(),
                "assembly of program {:?} unexpectedly succeeded",
                prog
            );
        }
    }
}
