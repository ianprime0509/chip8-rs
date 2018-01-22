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

use failure::{Backtrace, Error, Fail};
use nom::IResult;

use PROG_SIZE;
use PROG_START;
use Address;
use AddressOutOfBoundsError;

/// An error resulting from an attempt to give a new value to a label.
#[derive(Debug, Fail)]
#[fail(display = "label '{}' already has a value", _0)]
pub struct LabelAlreadyDefinedError(String);

/// An error resulting from having more than one label associated with a single
/// statement.
#[derive(Debug, Fail)]
#[fail(display = "more than one label found for the same statement")]
pub struct TooManyLabelsError;

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
    operation: Vec<u8>,
    /// The operands.
    operands: Vec<Vec<u8>>,
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

    /// Performs the first pass on the given line.
    pub fn process_line(&mut self, line: &str) -> Result<(), ErrorWithLine> {
        self.process_line_inner(line).map_err(|e| ErrorWithLine {
            line: self.line,
            inner: e,
        })?;
        self.line += 1;
        println!("{:?}", self.instructions);
        println!("{:?}", self.label_table);
        Ok(())
    }

    /// The actual logic for `process_line` which returns a normal `Result<(),
    /// Error>`.
    fn process_line_inner(&mut self, line: &str) -> Result<(), Error> {
        let line = line.as_bytes();
        let parsed = match parse::line(line) {
            IResult::Done(_, out) => out,
            IResult::Error(e) => return Err(e.into()),
            IResult::Incomplete(_) => {
                unreachable!("the parser should never return an incomplete value")
            }
        };

        if let Some(lbl) = parsed.0 {
            if self.label.is_some() {
                return Err(TooManyLabelsError.into());
            } else {
                self.label = Some(String::from_utf8(lbl.to_vec())?);
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
        operation: &[u8],
        operands: Vec<&[u8]>,
    ) -> Result<(), Error> {
        let operation = operation.to_ascii_uppercase();
        let operands = operands.into_iter().map(|s| s.to_vec()).collect::<Vec<_>>();

        match operation.clone().as_slice() {
            b"DB" => {
                self.add_first_pass_instruction(operation, operands)?;
                self.index += 1;
            }
            b"DW" => {
                self.add_first_pass_instruction(operation, operands)?;
                self.index += 2;
            }
            _ => {
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
        operation: Vec<u8>,
        operands: Vec<Vec<u8>>,
    ) -> Result<(), Error> {
        self.instructions.push_back(FirstPassInstruction {
            line: self.line,
            index: self.index,
            operation,
            operands,
        });
        if let Some(lbl) = self.label.clone() {
            let addr = self.index.address()?.addr();
            self.define_label(&lbl, addr as u16)?;
            self.label = None;
        }

        Ok(())
    }
}

mod parse {
    //! Parsing functions for the assembler.

    use nom::{alpha, alphanumeric};

    /// Matches the first character in an identifier.
    named!(ident_start, alt!(alpha | tag!("_")));

    /// Matches any character but the first in an identifier.
    named!(ident_inner, alt!(alphanumeric | tag!("_")));

    /// Parses an identifier.
    named!(
        ident,
        recognize!(preceded!(ident_start, many0!(ident_inner)))
    );

    /// Parses a label.
    named!(
        label,
        complete!(do_parse!(name: ident >> tag!(":") >> (name)))
    );

    /// Parses a list of operands.
    named!(
        operands<Vec<&[u8]>>,
        map!(
            opt!(ws!(separated_list_complete!(
                tag!(","),
                take_while!(|b| b != b',' && b != b';')
            ))),
            |opt| opt.unwrap_or(Vec::new())
        )
    );

    /// Parses an instruction (operation and operands).
    named!(
        instruction<(&[u8], Vec<&[u8]>)>,
        do_parse!(operation: ident >> operands: operands >> (operation, operands))
    );

    /// Parses a line.
    ///
    /// The return tuple will contain an optional label name and an optional
    /// instruction, where the instruction consists of the operation name and a
    /// vector of operands.
    named!(
        pub line<(Option<&[u8]>, Option<(&[u8], Vec<&[u8]>)>)>,
        ws!(do_parse!(
            label: opt!(label) >> instruction: opt!(instruction) >> alt!(tag!(";") | eof!())
                >> (label, instruction)
        ))
    );
}
