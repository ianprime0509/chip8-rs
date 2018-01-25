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

//! The Chip-8 interpreter.
//!
//! The main focus of this module is the `Interpreter` struct, which contains
//! the state of a Chip-8 interpreter and provides the main interface to be
//! used by the front-end.  Several options can be configured using the
//! `Options` struct, such as whether to use shift or load quirks mode.  More
//! details about what the interpreter is actually doing and what certain
//! options are (like the various "quirks" modes) can be found in the manual.

use std::default::Default;
use std::io::Read;
use std::num::Wrapping;
use std::u8;

use failure::{Error, ResultExt};
use rand;

use MEM_SIZE;
use PROG_START;
use PROG_SIZE;
use Register;
use display::{self, HEX_HIGH_HEIGHT, HEX_LOW_HEIGHT, HEX_SPRITES_HIGH, HEX_SPRITES_LOW};
use input::{self, Key};
use instruction::{Address, AddressOutOfBoundsError, AlignedAddress, Instruction, Opcode};
use timer::Timer;

/// The location at which to put the low-resolution hex sprites.
const HEX_LOW_START: usize = 0x0;
/// The location at which to put the high-resolution hex sprites.
const HEX_HIGH_START: usize = 0x100;

/// An error resulting from a bad `RET` instruction.
#[derive(Debug, Fail)]
#[fail(display = "no subroutine to return from")]
pub struct NotInSubroutineError;

/// An error resulting from an input program being too large.
#[derive(Debug, Fail)]
#[fail(display = "input program is too large")]
pub struct ProgramTooLargeError;

/// Options for the interpreter.
pub struct Options {
    /// Whether to delay draw instructions (default `true`).
    pub delay_draws: bool,
    /// Whether to enable the timer (default `true`).
    pub enable_timer: bool,
    /// Whether to enable load quirks mode (default `false`).
    pub load_quirks: bool,
    /// Whether to enable shift quirks mode (default `false`).
    pub shift_quirks: bool,
    /// The frequency at which to run the game, in Hz (default 60).
    pub timer_freq: u32,
}

impl Options {
    /// Returns the default set of options.
    pub fn new() -> Self {
        Options {
            delay_draws: true,
            enable_timer: true,
            load_quirks: false,
            shift_quirks: false,
            timer_freq: 60,
        }
    }

    /// Returns a set of options useful for testing (e.g. no timer).
    pub fn testing() -> Self {
        Options {
            delay_draws: false,
            enable_timer: false,
            load_quirks: false,
            shift_quirks: false,
            timer_freq: 60,
        }
    }
}

impl Default for Options {
    fn default() -> Self {
        Options::new()
    }
}

/// A Chip-8 interpreter.
///
/// This struct contains the entire state of a Chip-8 interpreter and provides
/// all the expected methods for interacting with an interpreter, such as
/// stepping through execution and inspecting the internal state.
pub struct Interpreter {
    /// The internal memory.
    mem: [u8; MEM_SIZE],
    /// The display buffer.
    display: display::Buffer,
    /// The input state.
    input: input::State,
    /// The general-purpose registers `V0`-`VF`.
    regs: [Wrapping<u8>; 16],
    /// The special register `I`.
    reg_i: Address,
    /// The internal timer that controls `DT` and `ST` as well as draw delays.
    timer: Timer,
    /// The delay timer.
    reg_dt: u8,
    /// The sound timer.
    reg_st: u8,
    /// The program counter.
    pc: AlignedAddress,
    /// Whether the interpreter has been halted.
    halted: bool,
    /// The call stack (for returning from subroutines).
    call_stack: Vec<AlignedAddress>,

    /// Whether to delay draw instructions.
    delay_draws: bool,
    /// Whether to use shift quirks mode.
    shift_quirks: bool,
    /// Whether to use load quirks mode.
    load_quirks: bool,
}

impl Interpreter {
    /// Returns a new interpreter with the default options.
    pub fn new() -> Self {
        Interpreter::with_options(Options::default())
    }

    /// Returns a new interpreter using the given options.
    pub fn with_options(options: Options) -> Self {
        let mut interpreter = Interpreter {
            mem: [0; MEM_SIZE],
            display: display::Buffer::new(),
            input: input::State::new(),
            regs: [Wrapping(0); 16],
            reg_i: Address::from_u16(0).unwrap(),
            timer: if options.enable_timer {
                Timer::new(options.timer_freq)
            } else {
                Timer::new_disabled(options.timer_freq)
            },
            reg_dt: 0,
            reg_st: 0,
            pc: Address::from_usize(PROG_START).unwrap().aligned().unwrap(),
            halted: false,
            call_stack: Vec::new(),

            delay_draws: options.delay_draws,
            shift_quirks: options.shift_quirks,
            load_quirks: options.load_quirks,
        };

        // Copy sprites into memory.
        for (i, sprite) in HEX_SPRITES_LOW.iter().enumerate() {
            let start = HEX_LOW_START + i * HEX_LOW_HEIGHT;
            let end = start + sprite.len();
            interpreter.mem[start..end].copy_from_slice(sprite);
        }
        for (i, sprite) in HEX_SPRITES_HIGH.iter().enumerate() {
            let start = HEX_HIGH_START + i * HEX_HIGH_HEIGHT;
            let end = start + sprite.len();
            interpreter.mem[start..end].copy_from_slice(sprite);
        }

        interpreter
    }

    /// Loads program data from the specified source.
    pub fn load_program<R: Read>(&mut self, input: &mut R) -> Result<(), Error> {
        let read = input.read(&mut self.mem[PROG_START..])?;
        if read == PROG_SIZE {
            // Try to see if we missed part of the file.
            let mut tmp = [0u8];
            if input.read(&mut tmp)? == 1 {
                return Err(ProgramTooLargeError.into());
            }
        }
        Ok(())
    }

    /// Returns a reference to the display buffer.
    pub fn display(&self) -> &display::Buffer {
        &self.display
    }

    /// Returns a mutable reference to the display buffer.
    pub fn display_mut(&mut self) -> &mut display::Buffer {
        &mut self.display
    }

    /// Returns whether the interpreter has been halted.
    pub fn halted(&self) -> bool {
        self.halted
    }

    /// Returns a reference to the input state.
    pub fn input(&self) -> &input::State {
        &self.input
    }

    /// Returns a mutable reference to the input state.
    pub fn input_mut(&mut self) -> &mut input::State {
        &mut self.input
    }

    /// Returns a reference to the internal memory.
    pub fn mem(&self) -> &[u8; MEM_SIZE] {
        &self.mem
    }

    /// Returns a mutable reference to the internal memory.
    pub fn mem_mut(&mut self) -> &mut [u8; MEM_SIZE] {
        &mut self.mem
    }

    /// Returns the value of register `I`.
    pub fn i(&self) -> Address {
        self.reg_i
    }

    /// Sets the value of register `I`.
    pub fn set_i(&mut self, val: Address) {
        self.reg_i = val;
    }

    /// Returns the value of the delay timer.
    pub fn dt(&self) -> u8 {
        self.reg_dt
    }

    /// Sets the value of the delay timer.
    pub fn set_dt(&mut self, val: u8) {
        self.reg_dt = val;
    }

    /// Returns the value of the sound timer.
    pub fn st(&self) -> u8 {
        self.reg_st
    }

    /// Sets the value of the sound timer.
    pub fn set_st(&mut self, val: u8) {
        self.reg_st = val;
    }

    /// Returns the value in the given register.
    pub fn register(&self, reg: Register) -> u8 {
        self.regs[reg as usize].0
    }

    /// Sets the given register to the given value.
    pub fn set_register(&mut self, reg: Register, val: u8) {
        self.regs[reg as usize].0 = val
    }

    /// Returns the value of the program counter.
    pub fn pc(&self) -> AlignedAddress {
        self.pc
    }

    /// Returns the instruction at the program counter.
    pub fn current_instruction(&self) -> Result<Instruction, Error> {
        Instruction::from_opcode(self.current_opcode(), self.shift_quirks)
    }

    /// Returns the opcode at the program counter.
    pub fn current_opcode(&self) -> Opcode {
        let high = self.mem[self.pc.addr()];
        let low = self.mem[self.pc.addr() + 1];
        Opcode::from_bytes(high, low)
    }

    /// Performs a single execution step.
    pub fn step(&mut self) -> Result<(), Error> {
        if !self.halted {
            self.update_timers();
            let instr = self.current_instruction()?;
            self.execute(instr)
        } else {
            Ok(())
        }
    }

    /// Executes the given instruction in the current interpreter context.
    ///
    /// The interpreter will behave as if the given instruction were executed
    /// at the current program location in memory.
    pub fn execute(&mut self, ins: Instruction) -> Result<(), Error> {
        use self::Instruction::*;

        match ins {
            Scd(n) => if self.ready_for_draw() {
                self.display.scroll_down(n as usize)
            } else {
                return Ok(());
            },
            Cls => self.display.clear(),
            Ret => {
                self.pc = self.call_stack
                    .pop()
                    .ok_or(NotInSubroutineError)
                    .with_context(|_| format!("error executing {}", ins))?;
            }
            Scr => if self.ready_for_draw() {
                self.display.scroll_right(4)
            } else {
                return Ok(());
            },
            Scl => if self.ready_for_draw() {
                self.display.scroll_left(4)
            } else {
                return Ok(());
            },
            Exit => {
                self.halted = true;
                return Ok(());
            }
            Low => self.display.set_high(false),
            High => self.display.set_high(true),
            Jp(addr) => {
                self.pc = addr;
                return Ok(());
            }
            Call(addr) => {
                self.call_stack.push(self.pc);
                self.pc = addr;
                return Ok(());
            }
            SeByte(reg, b) => if self.register(reg) == b {
                self.pc = (self.pc + 4).context("program counter overflowed")?;
                return Ok(());
            },
            SneByte(reg, b) => if self.register(reg) != b {
                self.pc = (self.pc + 4).context("program counter overflowed")?;
                return Ok(());
            },
            SeReg(reg1, reg2) => if self.register(reg1) == self.register(reg2) {
                self.pc = (self.pc + 4).context("program counter overflowed")?;
                return Ok(());
            },
            LdByte(reg, b) => self.set_register(reg, b),
            AddByte(reg, b) => self.add(reg, b),
            LdReg(reg1, reg2) => {
                let r2 = self.register(reg2);
                self.set_register(reg1, r2);
            }
            Or(reg1, reg2) => {
                let r1 = self.register(reg1);
                let r2 = self.register(reg2);
                self.set_register(reg1, r1 | r2);
            }
            And(reg1, reg2) => {
                let r1 = self.register(reg1);
                let r2 = self.register(reg2);
                self.set_register(reg1, r1 & r2);
            }
            Xor(reg1, reg2) => {
                let r1 = self.register(reg1);
                let r2 = self.register(reg2);
                self.set_register(reg1, r1 ^ r2);
            }
            AddReg(reg1, reg2) => {
                let r2 = self.register(reg2);
                self.add(reg1, r2);
            }
            Sub(reg1, reg2) => {
                let r2 = self.register(reg2);
                self.sub(reg1, r2);
            }
            Shr(reg) => self.shr(reg, reg),
            ShrQuirk(reg1, reg2) => self.shr(reg1, reg2),
            Subn(reg1, reg2) => {
                let r2 = self.register(reg2);
                self.subn(reg1, r2);
            }
            Shl(reg) => self.shl(reg, reg),
            ShlQuirk(reg1, reg2) => self.shl(reg1, reg2),
            SneReg(reg1, reg2) => if self.register(reg1) != self.register(reg2) {
                self.pc = (self.pc + 4)?;
                return Ok(());
            },
            LdI(addr) => self.reg_i = addr,
            JpV0(addr) => {
                self.pc = (addr + self.register(Register::V0) as usize)
                    .context("attempted to jump to out of bounds address")?
                    .aligned()
                    .context("attempted to jump to misaligned address")?;
                return Ok(());
            }
            Rnd(reg, b) => self.set_register(reg, rand::random::<u8>() & b),
            Drw(reg1, reg2, n) => if self.ready_for_draw() {
                self.drw(reg1, reg2, n);
            } else {
                return Ok(());
            },
            Skp(reg) => if self.input.is_pressed(Key::from_byte(self.register(reg))) {
                self.pc = (self.pc + 4).context("program counter overflowed")?;
                return Ok(());
            },
            Sknp(reg) => if !self.input.is_pressed(Key::from_byte(self.register(reg))) {
                self.pc = (self.pc + 4).context("program counter overflowed")?;
                return Ok(());
            },
            LdRegDt(reg) => {
                let dt = self.dt();
                self.set_register(reg, dt);
            }
            LdKey(reg) => match self.input.get_pressed() {
                Some(key) => self.set_register(reg, key as u8),
                None => return Ok(()),
            },
            LdDtReg(reg) => {
                let r = self.register(reg);
                self.set_dt(r);
            }
            LdSt(reg) => {
                let r = self.register(reg);
                self.set_st(r);
            }
            AddI(reg) => {
                let new_i =
                    (self.i() + self.register(reg) as usize).context("register 'I' overflowed")?;
                self.set_i(new_i);
            }
            LdF(reg) => {
                let r = self.register(reg) as usize;
                self.set_i(
                    Address::from_usize(
                        HEX_LOW_START + HEX_LOW_HEIGHT * (r % HEX_SPRITES_LOW.len()),
                    ).unwrap(),
                )
            }
            LdHf(reg) => {
                let r = self.register(reg) as usize;
                self.set_i(
                    Address::from_usize(
                        HEX_HIGH_START + HEX_HIGH_HEIGHT * (r % HEX_SPRITES_HIGH.len()),
                    ).unwrap(),
                )
            }
            LdB(reg) => self.ld_b(reg)
                .with_context(|_| format!("error executing {}", ins))?,
            LdDerefIReg(reg) => self.ld_deref_i_reg(reg)
                .with_context(|_| format!("error executing {}", ins))?,
            LdRegDerefI(reg) => self.ld_reg_deref_i(reg)
                .with_context(|_| format!("error executing {}", ins))?,
            LdRReg(_) => warn!("I don't know what 'LD R, Vx' does"),
            LdRegR(_) => warn!("I don't know what 'LD Vx, R' does"),
        }

        self.pc = (self.pc + 2).context("program counter overflowed")?;
        Ok(())
    }

    /// Adds the given byte to the given register, setting `VF` to 1 on carry
    /// or 0 otherwise.
    fn add(&mut self, reg: Register, val: u8) {
        let carry = val > u8::MAX - self.register(reg);
        self.regs[reg as usize] += Wrapping(val);
        self.set_register(Register::VF, carry as u8);
    }

    /// Implements the `DRW` operation.
    fn drw(&mut self, reg1: Register, reg2: Register, n: u8) {
        let start = self.reg_i.addr();
        let x = self.register(reg1) as usize;
        let y = self.register(reg2) as usize;

        if n == 0 {
            self.display
                .draw_sprite_high(&self.mem[start..start + 32], x, y);
        } else {
            self.display
                .draw_sprite_low(&self.mem[start..start + n as usize], x, y);
        }
    }

    /// Implements the `LD B, Vx` operation.
    fn ld_b(&mut self, reg: Register) -> Result<(), Error> {
        let val = self.register(reg);
        let hundreds = val / 100;
        let tens = val % 100 / 10;
        let ones = val % 10;
        let addr = self.i().addr();

        if addr + 2 >= MEM_SIZE {
            Err(AddressOutOfBoundsError(addr + 2))?
        } else {
            self.mem[addr] = hundreds;
            self.mem[addr + 1] = tens;
            self.mem[addr + 2] = ones;
            Ok(())
        }
    }

    /// Implements the `LD [I], Vx` operation.
    fn ld_deref_i_reg(&mut self, reg: Register) -> Result<(), Error> {
        let regno = reg as usize;
        let start = self.i().addr();

        if start + regno > MEM_SIZE {
            Err(AddressOutOfBoundsError(start + regno - 1))?
        } else {
            for (dest, src) in self.mem[start..start + regno]
                .iter_mut()
                .zip(self.regs[0..regno].iter_mut())
            {
                *dest = src.0;
            }
            if self.load_quirks {
                self.set_i(Address::from_usize(start + regno).unwrap());
            }

            Ok(())
        }
    }

    /// Implements to `LD Vx, [I]` operation.
    fn ld_reg_deref_i(&mut self, reg: Register) -> Result<(), Error> {
        let regno = reg as usize;
        let start = self.i().addr();

        if start + regno > MEM_SIZE {
            Err(AddressOutOfBoundsError(start + regno - 1))?
        } else {
            for (dest, src) in self.regs[0..regno]
                .iter_mut()
                .zip(self.mem[start..start + regno].iter_mut())
            {
                *dest = Wrapping(*src);
            }
            if self.load_quirks {
                self.set_i(Address::from_usize(start + regno).unwrap());
            }

            Ok(())
        }
    }

    /// Sets `reg1` to `reg2 << 1`, setting `VF` to the old highest bit.
    fn shl(&mut self, reg1: Register, reg2: Register) {
        let old = (self.register(reg2) & 1 << 7) >> 7;
        let r2 = self.register(reg2);
        self.set_register(reg1, r2 << 1);
        self.set_register(Register::VF, old);
    }

    /// Sets `reg1` to `reg2 >> 1`, setting `VF` to the old lowest bit.
    fn shr(&mut self, reg1: Register, reg2: Register) {
        let old = self.register(reg2) & 1;
        let r2 = self.register(reg2);
        self.set_register(reg1, r2 >> 1);
        self.set_register(Register::VF, old);
    }

    /// Subtracts the given byte from the given register, setting `VF` to 0 on
    /// borrow or 1 otherwise.
    fn sub(&mut self, reg: Register, val: u8) {
        let borrow = val > self.register(reg);
        self.regs[reg as usize] -= Wrapping(val);
        self.set_register(Register::VF, !borrow as u8);
    }

    /// Sets `reg` to `val - reg`, setting `VF` to 0 on borrow or 1 otherwise.
    fn subn(&mut self, reg: Register, val: u8) {
        let borrow = self.register(reg) > val;
        self.regs[reg as usize] = Wrapping(val) - self.regs[reg as usize];
        self.set_register(Register::VF, !borrow as u8);
    }

    /// Delays a draw instruction, returning `true` if the instruction should
    /// execute and `false` if more time is required.
    ///
    /// If the `delay_draws` interpreter option is `false`, then this always
    /// returns `true`.
    fn ready_for_draw(&mut self) -> bool {
        if self.delay_draws {
            self.timer.wait_for_latch()
        } else {
            true
        }
    }

    /// Updates the internal timer as well as the `DT` and `ST` registers.
    fn update_timers(&mut self) {
        let ticks = self.timer.lap() as u8;
        let dt = self.dt();
        let st = self.st();
        self.set_dt(if dt > ticks { dt - ticks } else { 0 });
        self.set_st(if st > ticks { st - ticks } else { 0 });
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter::new()
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
            let carry = b1 as u32 + b2 as u32 > u8::MAX as u32;

            // Test `ADD Vx, byte`.
            interpreter.set_register(vx, b1);
            interpreter.execute(Instruction::AddByte(vx, b2)).unwrap();
            assert_eq!(interpreter.register(vx), sum, "case {:?}", case);
            assert_eq!(interpreter.register(VF), carry as u8, "case {:?}", case);

            // Test `ADD Vx, Vy`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::AddReg(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), sum, "case {:?}", case);
            assert_eq!(interpreter.register(VF), carry as u8, "case {:?}", case);
        }
    }

    /// Tests the `AND`, `OR` and `XOR` operations.
    #[test]
    fn instruction_bitwise() {
        use Register::*;

        // Test cases, in the format (Vx, Vy, b1, b2).
        let cases = [
            (V7, V2, 0x75, 0xF2),
            (V3, V8, 0x01, 0xFF),
            (VA, VE, 0x6A, 0x32),
            (VF, VC, 0x78, 0xFD),
            (V0, V1, 0xF0, 0x0F),
        ];
        let mut interpreter = Interpreter::with_options(Options::testing());

        for &(vx, vy, b1, b2) in cases.into_iter() {
            let case = (vx, vy, b1, b2);
            let or = b1 | b2;
            let and = b1 & b2;
            let xor = b1 ^ b2;

            // Test `OR`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::Or(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), or, "case {:?}", case);

            // Test `AND`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::And(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), and, "case {:?}", case);

            // Test `XOR`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::Xor(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), xor, "case {:?}", case);
        }
    }

    /// Tests the `LD B, Vx` operation.
    #[test]
    fn instruction_ld_b() {
        use Register::*;

        // Test cases, in the format (Vx, n1, n2, n3), where the three digits
        // to be stored are n1, n2 and n3 (in that order).
        let cases = [
            (V5, 1, 2, 3),
            (VD, 0, 0, 1),
            (VE, 1, 0, 0),
            (V2, 2, 5, 5),
            (V6, 0, 0, 0),
            (V8, 0, 6, 4),
        ];
        let mut interpreter = Interpreter::with_options(Options::testing());

        for &(vx, n1, n2, n3) in cases.into_iter() {
            let case = (vx, n1, n2, n3);
            let n = 100 * n1 + 10 * n2 + n3;

            interpreter.set_register(vx, n);
            interpreter.execute(Instruction::LdB(vx)).unwrap();
            let i = interpreter.i().addr();
            assert_eq!(interpreter.mem()[i], n1, "case {:?}", case);
            assert_eq!(interpreter.mem()[i + 1], n2, "case {:?}", case);
            assert_eq!(interpreter.mem()[i + 2], n3, "case {:?}", case);
        }
    }

    /// Tests the `SUB` and `SUBN` operations.
    #[test]
    fn instruction_sub() {
        use Register::*;

        // Test cases, in the format (Vx, Vy, b1, b2).
        let cases = [
            (V9, V8, 70u8, 35u8),
            (V6, V2, 56u8, 2u8),
            (V0, V1, 0u8, 0u8),
            (VE, VA, 255u8, 255u8),
            (V3, V7, 1u8, 255u8),
        ];
        let mut interpreter = Interpreter::with_options(Options::testing());

        for &(vx, vy, b1, b2) in cases.into_iter() {
            let case = (vx, vy, b1, b2);
            let sub = b1.wrapping_sub(b2);
            let subn = b2.wrapping_sub(b1);
            let borrow = b2 > b1;
            let borrown = b1 > b2;

            // Test `SUB Vx, Vy`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::Sub(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), sub, "case {:?}", case);
            assert_eq!(interpreter.register(VF), !borrow as u8, "case {:?}", case);

            // Test `SUBN Vx, Vy`.
            interpreter.set_register(vx, b1);
            interpreter.set_register(vy, b2);
            interpreter.execute(Instruction::Subn(vx, vy)).unwrap();
            assert_eq!(interpreter.register(vx), subn, "case {:?}", case);
            assert_eq!(interpreter.register(VF), !borrown as u8, "case {:?}", case);
        }
    }
}
