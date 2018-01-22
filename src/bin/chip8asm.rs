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

//! The `chip8asm` binary program.

extern crate chip8;
extern crate failure;

use std::io;

use failure::Error;

fn main() {
    if let Err(e) = run() {
        println!("Error: {}", e);
    }
}

fn run() -> Result<(), Error> {
    let mut s = String::new();
    let mut assembler = chip8::assembler::Assembler::new();

    loop {
        s.clear();
        io::stdin().read_line(&mut s)?;

        if s.is_empty() {
            break;
        }
        assembler.process_line(&s)?;
    }

    Ok(())
}
