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

use std::default::Default;
use std::num::Wrapping;
use std::u8;

use failure::Error;
use rand;

use MEM_SIZE;
use PROG_START;
use Register;
use display::{self, HEX_HIGH_HEIGHT, HEX_LOW_HEIGHT, HEX_SPRITES_HIGH, HEX_SPRITES_LOW};
use input::{self, Key};
use instruction::{Address, AddressOutOfBoundsError, AlignedAddress, Instruction, Opcode};
use timer::Timer;

/// The location at which to put the low-resolution hex sprites.
const HEX_LOW_START: usize = 0x0;
/// The location at which to put the high-resolution hex sprites.
const HEX_HIGH_START: usize = 0x100;

/// An error relating to the interpreter.
#[derive(Debug, Fail)]
pub enum InterpreterError {
    #[fail(display = "no subroutine to return from")] NotInSubroutine,
}

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
    pub fn new() -> Self {
        Options {
            delay_draws: true,
            enable_timer: true,
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

/// The interpreter.
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

    /// Returns the instruction at the program counter.
    pub fn current_instruction(&self) -> Result<Instruction, Error> {
        Instruction::from_opcode(self.current_opcode(), self.shift_quirks)
    }

    /// Returns the opcode at the program counter.
    pub fn current_opcode(&self) -> Opcode {
        let high = self.mem[self.pc.addr()] as u16;
        let low = self.mem[self.pc.addr() + 1] as u16;
        Opcode(high << 8 | low)
    }

    /// Performs a single execution step.
    pub fn step(&mut self) -> Result<(), Error> {
        self.update_timers();
        let instr = self.current_instruction()?;
        self.execute(instr)
    }

    /// Executes the given instruction in the current interpreter context.
    ///
    /// The interpreter will behave as if the given instruction were executed
    /// at the current program location in memory.
    fn execute(&mut self, ins: Instruction) -> Result<(), Error> {
        use self::Instruction::*;

        match ins {
            Scd(n) => if self.ready_for_draw() {
                self.display.scroll_down(n as usize)
            },
            Cls => self.display.clear(),
            Ret => {
                self.pc = self.call_stack
                    .pop()
                    .ok_or(InterpreterError::NotInSubroutine)?
            }
            Scr => if self.ready_for_draw() {
                self.display.scroll_right(4)
            },
            Scl => if self.ready_for_draw() {
                self.display.scroll_left(4)
            },
            Exit => {
                self.halted = true;
                return Ok(());
            }
            Low => self.display.set_low(),
            High => self.display.set_high(),
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
                self.pc = (self.pc + 4)?;
                return Ok(());
            },
            SneByte(reg, b) => if self.register(reg) != b {
                self.pc = (self.pc + 4)?;
                return Ok(());
            },
            SeReg(reg1, reg2) => if self.register(reg1) == self.register(reg2) {
                self.pc = (self.pc + 4)?;
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
                self.pc = (addr + self.register(Register::V0) as usize)?.aligned()?;
                return Ok(());
            }
            Rnd(reg, b) => self.set_register(reg, rand::random::<u8>() & b),
            Drw(reg1, reg2, n) => self.drw(reg1, reg2, n),
            Skp(reg) => if self.input.is_pressed(Key::from_byte(self.register(reg))) {
                self.pc = (self.pc + 4)?;
                return Ok(());
            },
            Sknp(reg) => if !self.input.is_pressed(Key::from_byte(self.register(reg))) {
                self.pc = (self.pc + 4)?;
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
                let new_i = (self.i() + self.register(reg) as usize)?;
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
            LdB(reg) => self.ld_b(reg)?,
            LdDerefIReg(reg) => self.ld_deref_i_reg(reg)?,
            LdRegDerefI(reg) => self.ld_reg_deref_i(reg)?,
            LdRReg(_) => warn!("I don't know what 'LD R, Vx' does"),
            LdRegR(_) => warn!("I don't know what 'LD Vx, R' does"),
        }

        self.pc = (self.pc + 2)?;
        Ok(())
    }

    /// Adds the given byte to the given register, setting `VF` to 1 on carry
    /// or 0 otherwise.
    fn add(&mut self, reg: Register, val: u8) {
        let carry = val > u8::MAX - 1 - self.register(reg);
        self.regs[reg as usize] += Wrapping(val);
        self.set_register(Register::VF, if carry { 1 } else { 0 });
    }

    /// Implements the `DRW` operation.
    fn drw(&mut self, reg1: Register, reg2: Register, n: u8) {
        if !self.ready_for_draw() {
            return;
        }
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
        self.set_register(Register::VF, if borrow { 0 } else { 1 });
    }

    /// Sets `reg` to `val - reg`, setting `VF` to 0 on borrow or 1 otherwise.
    fn subn(&mut self, reg: Register, val: u8) {
        let borrow = self.register(reg) > val;
        self.regs[reg as usize] = Wrapping(val) - self.regs[reg as usize];
        self.set_register(Register::VF, if borrow { 0 } else { 1 });
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
