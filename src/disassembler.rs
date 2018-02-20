/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! The Chip-8 disassembler.

use std::collections::HashSet;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::default::Default;
use std::io::{BufWriter, Read, Write};

use failure::{Error, ResultExt};

use PROG_START;
use assembler::ProgramIndex;
use instruction::{Address, Instruction, Opcode};

/// Options to be used with the disassembler.
pub struct Options {
    /// Whether to enable shift quirks mode.
    pub shift_quirks: bool,
}

impl Options {
    /// Returns the default set of options.
    pub fn new() -> Self {
        Options {
            shift_quirks: false,
        }
    }
}

impl Default for Options {
    fn default() -> Self {
        Options::new()
    }
}

/// A control point in the code, being either an unconditional jump instruction
/// (a jump point) or an address that is jumped to (a return point).
///
/// Keeping an ordered list of control points allows for easy control-flow
/// analysis: an instruction is reachable if and only if its address is
/// strictly between a jump point and a return point (either end of this
/// comparison could also be the start or end of the program data; an
/// instruction after the last control point is unreachable if that control
/// point is a jump point).
///
/// Keep in mind that jump points must be *unconditional jumps*, and not jumps
/// following a SKP instruction (or similar), since they indicate the end of a
/// reachable block.  For simplicity, we can also omit return points which
/// immediately follow a skip instruction, since they will add nothing to the
/// analysis.
///
/// Jump points are ordered after return points with the same program address
/// so that instructions like `lbl: JP lbl` are processed correctly:
///
/// ```
/// use chip8::assembler::ProgramIndex;
/// use chip8::disassembler::ControlPoint::*;
///
/// assert!(Jp(ProgramIndex::new(0)) > Ret(ProgramIndex::new(0)));
/// assert!(Jp(ProgramIndex::new(0)) < Ret(ProgramIndex::new(1)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlPoint {
    Jp(ProgramIndex),
    Ret(ProgramIndex),
}

impl Ord for ControlPoint {
    fn cmp(&self, other: &ControlPoint) -> Ordering {
        use self::ControlPoint::*;

        match (*self, *other) {
            (Jp(i), Jp(j)) | (Ret(i), Ret(j)) => i.cmp(&j),
            (Jp(i), Ret(j)) => if i == j {
                Ordering::Greater
            } else {
                i.cmp(&j)
            },
            (Ret(i), Jp(j)) => if i == j {
                Ordering::Less
            } else {
                i.cmp(&j)
            },
        }
    }
}

impl PartialOrd for ControlPoint {
    fn partial_cmp(&self, other: &ControlPoint) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Contains the state of the disassembler.
///
/// Once the disassembler is initialized with some program data, it can be used
/// repeatedly to get disassembly information from it.  This is intended to
/// support things like debuggers, which might want access to the disassembly
/// information to display sections of the disassembled code or to set
/// breakpoints based on disassembled label names.
pub struct Disassembler {
    /// The program being disassembled.
    prog: Vec<u8>,
    /// The list of control points.
    ///
    /// This must always be in ascending order.
    control_points: Vec<ControlPoint>,
    /// The list of labelled locations.
    ///
    /// Every address which is accessed or used by some instruction and which
    /// is also a valid program address should be in this list so that a nice
    /// label name can be used.
    labels: HashSet<Address>,
    /// Whether to use shift quirks mode.
    shift_quirks: bool,
}

impl Disassembler {
    /// Creates a new disassembler from the given program data using the
    /// default options.
    pub fn new<R: Read>(input: &mut R) -> Result<Self, Error> {
        Disassembler::with_options(input, Options::new())
    }

    /// Creates a new disassembler from the given program data using the given
    /// options.
    pub fn with_options<R: Read>(input: &mut R, options: Options) -> Result<Self, Error> {
        use Instruction::*;

        let mut prog = Vec::new();
        input.read_to_end(&mut prog);

        let mut control_points = Vec::new();
        let mut labels = HashSet::new();
        // A list of instructions that immediately follow skip instructions,
        // and therefore which should not be included as control points.
        let mut skipped = HashSet::new();
        // A list of execution starting points.
        let mut starts = vec![ProgramIndex::new(0)];

        while let Some(mut index) = starts.pop() {
            // If this instruction has been skipped, then we have already
            // analyzed the control paths that follow.
            if skipped.contains(&index) {
                continue;
            }
            // Skip this path if we've already gone down it; otherwise, add it
            // as a return point.
            match control_points.binary_search(&ControlPoint::Ret(index)) {
                Ok(_) => continue,
                Err(pos) => control_points.insert(pos, ControlPoint::Ret(index)),
            }

            loop {
                let pi = index.index()?;
                if pi + 1 >= prog.len() {
                    warn!("control path went out of program bounds");
                    break;
                }
                let opcode = Opcode::from_bytes(prog[pi], prog[pi + 1]);
                let instr =
                    Instruction::from_opcode(opcode, options.shift_quirks).with_context(|_| {
                        format!(
                            "encountered invalid opcode {} at address {}",
                            opcode,
                            index.address().unwrap()
                        )
                    })?;

                // If the instruction references an address, we need to add it
                // to our list.
                if let Some(addr) = instr.addr() {
                    if addr.addr() - PROG_START < prog.len() {
                        labels.insert(addr);
                    }
                }

                match instr {
                    Ret | Exit => {
                        if !skipped.contains(&index) {
                            let point = ControlPoint::Jp(index);
                            if let Err(pos) = control_points.binary_search(&point) {
                                control_points.insert(pos, point);
                            }
                            break;
                        }
                    }
                    Call(addr) => {
                        starts.push(ProgramIndex::from_address(*addr)?);
                    }
                    Jp(addr) => {
                        starts.push(ProgramIndex::from_address(*addr)?);
                        if !skipped.contains(&index) {
                            let point = ControlPoint::Jp(index);
                            if let Err(pos) = control_points.binary_search(&point) {
                                control_points.insert(pos, point);
                            }
                            break;
                        }
                    }
                    SeByte(_, _)
                    | SneByte(_, _)
                    | SeReg(_, _)
                    | SneReg(_, _)
                    | Skp(_)
                    | Sknp(_) => {
                        skipped.insert(index + 2);
                    }
                    JpV0(_) => {
                        warn!("the JP V0 instruction is not fully supported yet");
                        if !skipped.contains(&index) {
                            let point = ControlPoint::Jp(index);
                            if let Err(pos) = control_points.binary_search(&point) {
                                control_points.insert(pos, point);
                            }
                            break;
                        }
                    }
                    _ => {}
                }

                index += 2;
            }
        }

        // Just to make sure, we remove all control points corresponding to
        // skipped instructions; there are some rare cases in which the control
        // flow is so complicated that an instruction may not be identified as
        // skipped until it has already been processed and falsely identified
        // as a jump point.  For example (this is a test case in the
        // `control_points` test):
        //
        // JP next
        // previous: SKNP V0
        // next: JP previous
        // twist: JP twist2
        // SE V0, #23
        // twist2: JP twist
        let control_points = control_points
            .into_iter()
            .filter(|&point| match point {
                ControlPoint::Jp(ref index) | ControlPoint::Ret(ref index) => {
                    !skipped.contains(index)
                }
            })
            .collect();

        Ok(Disassembler {
            prog,
            control_points,
            labels,
            shift_quirks: options.shift_quirks,
        })
    }

    /// Dumps the entire disassembled content of the program to the given
    /// output.
    pub fn dump<W: Write>(&self, output: &mut W) -> Result<(), Error> {
        let mut output = BufWriter::new(output);

        for (n, chunk) in self.prog.chunks(2).enumerate() {
            let index = ProgramIndex::new(2 * n);

            if chunk.len() == 1 {
                write!(output, "DB #{:02X}\n", chunk[0])?;
                continue;
            }

            let opcode = Opcode::from_bytes(chunk[0], chunk[1]);
            // Make sure we precede the instruction with a label if the current
            // instruction is referenced somewhere in the code.
            if let Ok(addr) = index.address() {
                if self.labels.contains(&addr) {
                    write!(output, "L{:03X}: ", index.index()?)?;
                }
            }

            if self.is_reachable(index) {
                let instr = Instruction::from_opcode(opcode, self.shift_quirks)?;
                // We want to have a nice label operand for addresses that we
                // already know are referenced in the code.  The format for
                // these labels is currently `Lnnn`, where `nnn` is the program
                // index in hexadecimal.
                if let Some(addr) = instr.addr() {
                    if self.labels.contains(&addr) {
                        write!(
                            output,
                            "{}\n",
                            instr.to_string_with_address_label(Some(&format!(
                                "L{:03X}",
                                ProgramIndex::from_address(addr)?.index()?
                            )))
                        )?;
                        continue;
                    }
                }
                write!(output, "{}\n", instr)?;
            } else {
                write!(output, "DW {}\n", opcode)?;
            }
        }

        Ok(())
    }

    /// Returns whether the given program index is reachable (based on
    /// control-flow analysis).
    pub fn is_reachable(&self, index: ProgramIndex) -> bool {
        use self::ControlPoint::*;

        match self.control_points.binary_search(&Ret(index)) {
            Ok(_) => true,
            Err(pos) => if pos == self.control_points.len() {
                // We are guaranteed to have at least one control point (the
                // initial entry).
                match *self.control_points.last().unwrap() {
                    Ret(_) => true,
                    Jp(_) => false,
                }
            } else {
                // We are guaranteed to have pos > 0, since the first control
                // point is Ret(0) (the minimum value).
                assert!(pos > 0);
                match (self.control_points[pos - 1], self.control_points[pos]) {
                    (Jp(_), Ret(_)) => false,
                    _ => true,
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::Disassembler;
    use super::ControlPoint::*;
    use assembler::{Assembler, ProgramIndex};

    /// Tests whether control points are identified correctly.
    #[test]
    fn control_points() {
        // A list of cases, each one containing a program to be assembled and
        // the corresponding control points.
        let cases = [
            (
                "lbl: JP lbl",
                vec![Ret(ProgramIndex::new(0)), Jp(ProgramIndex::new(0))],
            ),
            (
                "lbl: JP lbl2
lbl2: JP lbl",
                vec![
                    Ret(ProgramIndex::new(0)),
                    Jp(ProgramIndex::new(0)),
                    Ret(ProgramIndex::new(2)),
                    Jp(ProgramIndex::new(2)),
                ],
            ),
            (
                "ADD V0, V1
JP later
DW 2
DB 3
later: JP later",
                vec![
                    Ret(ProgramIndex::new(0)),
                    Jp(ProgramIndex::new(2)),
                    Ret(ProgramIndex::new(8)),
                    Jp(ProgramIndex::new(8)),
                ],
            ),
            (
                "start: SKP V1
gotcha: JP gotcha
ADD V0, V1
JP start",
                vec![Ret(ProgramIndex::new(0)), Jp(ProgramIndex::new(6))],
            ),
            (
                "JP next
previous: SKNP V0
next: JP previous
twist: JP twist2
SE V0, #23
twist2: JP twist",
                vec![
                    Ret(ProgramIndex::new(0)),
                    Jp(ProgramIndex::new(0)),
                    Ret(ProgramIndex::new(2)),
                    Ret(ProgramIndex::new(6)),
                    Jp(ProgramIndex::new(6)),
                    Ret(ProgramIndex::new(10)),
                    Jp(ProgramIndex::new(10)),
                ],
            ),
        ];

        for (n, &(program, ref control_points)) in cases.into_iter().enumerate() {
            let asm = Assembler::new();
            let mut input = Cursor::new(program);
            let mut output = Vec::new();
            asm.assemble(&mut input, &mut output).unwrap();
            let mut output = Cursor::new(output);
            let disasm = Disassembler::new(&mut output).unwrap();

            assert_eq!(
                disasm.control_points,
                control_points.as_slice(),
                "test case {} failed",
                n + 1
            );
        }
    }

    /// Tests whether the `dump` method behaves as expected by assembling and
    /// then disassembling a sample program.
    #[test]
    fn dump() {
        let prog = "ADD V0, V1
LD I, #AB0
JP L00A
DW #1234
L008: DW #2F00
L00A: LD I, L008
L00C: JP L00C
DB #42
";
        let asm = Assembler::new();
        let mut input = Cursor::new(prog);
        let mut output = Vec::new();
        asm.assemble(&mut input, &mut output).unwrap();
        let mut output = Cursor::new(output);
        let disasm = Disassembler::new(&mut output).unwrap();

        let mut output = Vec::new();
        disasm.dump(&mut output).unwrap();
        assert_eq!(String::from_utf8(output).unwrap(), prog);
    }

    /// Tests whether the `is_reachable` method behaves as expected.
    #[test]
    fn is_reachable() {
        let prog = "JP start
DW #1234
start: ADD V0, V1
SKP V1
JP start
end: JP end";
        let asm = Assembler::new();
        let mut input = Cursor::new(prog);
        let mut output = Vec::new();
        asm.assemble(&mut input, &mut output).unwrap();
        let mut output = Cursor::new(output);
        let disasm = Disassembler::new(&mut output).unwrap();

        assert!(disasm.is_reachable(ProgramIndex::new(0)));
        assert!(!disasm.is_reachable(ProgramIndex::new(2)));
        assert!(disasm.is_reachable(ProgramIndex::new(4)));
        assert!(disasm.is_reachable(ProgramIndex::new(6)));
        assert!(disasm.is_reachable(ProgramIndex::new(8)));
        assert!(disasm.is_reachable(ProgramIndex::new(10)));
    }
}
