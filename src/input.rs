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

//! Input handling for the Chip-8 interpreter.

use std::default::Default;

use num::traits::FromPrimitive;

/// The number of keys on the Chip-8 controller.
const N_KEYS: usize = 16;

enum_from_primitive!{
/// The keys on the Chip-8 controller.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Key {
    K0 = 0,
    K1,
    K2,
    K3,
    K4,
    K5,
    K6,
    K7,
    K8,
    K9,
    KA,
    KB,
    KC,
    KD,
    KE,
    KF
}
}

impl Key {
    /// Returns the key corresponding to the lowest four bits of the given
    /// byte.
    pub fn from_byte(b: u8) -> Key {
        Key::from_u8(b % N_KEYS as u8).unwrap()
    }
}

/// Represents the state of the input device.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct State {
    /// The key states (`true` means "pressed").
    keys: [bool; N_KEYS],
}

impl State {
    /// Returns a new input state with all keys unpressed.
    pub fn new() -> Self {
        State::default()
    }

    /// Returns the lowest key that is pressed, and unpresses the key.
    pub fn get_pressed(&mut self) -> Option<Key> {
        for (i, key) in self.keys.iter_mut().enumerate() {
            if *key {
                *key = false;
                return Some(Key::from_usize(i).unwrap());
            }
        }
        None
    }

    /// Returns whether the given key is pressed.
    pub fn is_pressed(&self, key: Key) -> bool {
        self.keys[key as usize]
    }
}
