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

//! Chip-8 display traits and implementations.

use std::default::Default;

use failure::Fail;

/// The width of the display.
pub const WIDTH: usize = 128;
/// The height of the display.
pub const HEIGHT: usize = 64;

/// The height of a low-resolution sprite.
pub const HEX_LOW_HEIGHT: usize = 5;
/// The height of a high-resolution sprite.
pub const HEX_HIGH_HEIGHT: usize = 10;

/// The low-resolution hex digit sprites.
pub const HEX_SPRITES_LOW: [[u8; HEX_LOW_HEIGHT]; 16] = [
    [0xF0, 0x90, 0x90, 0x90, 0xF0],
    [0x20, 0x60, 0x20, 0x20, 0x70],
    [0xF0, 0x10, 0xF0, 0x80, 0xF0],
    [0xF0, 0x10, 0xF0, 0x10, 0xF0],
    [0x90, 0x90, 0xF0, 0x10, 0x10],
    [0xF0, 0x80, 0xF0, 0x10, 0xF0],
    [0xF0, 0x80, 0xF0, 0x90, 0xF0],
    [0xF0, 0x10, 0x20, 0x40, 0x40],
    [0xF0, 0x90, 0xF0, 0x90, 0xF0],
    [0xF0, 0x90, 0xF0, 0x10, 0xF0],
    [0xF0, 0x90, 0xF0, 0x90, 0x90],
    [0xE0, 0x90, 0xE0, 0x90, 0xE0],
    [0xF0, 0x80, 0x80, 0x80, 0xF0],
    [0xE0, 0x90, 0x90, 0x90, 0xE0],
    [0xF0, 0x80, 0xF0, 0x80, 0xF0],
    [0xF0, 0x80, 0xF0, 0x80, 0x80],
];

/// The high-resolution hex digit sprites.
pub const HEX_SPRITES_HIGH: [[u8; HEX_HIGH_HEIGHT]; 16] = [
    [0x3C, 0x42, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x42, 0x3C],
    [0x18, 0x28, 0x48, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x7F],
    [0x3C, 0x42, 0x81, 0x81, 0x02, 0x0C, 0x30, 0x40, 0x80, 0xFF],
    [0x7C, 0x82, 0x01, 0x01, 0x1E, 0x01, 0x01, 0x01, 0x82, 0x7C],
    [0x81, 0x81, 0x81, 0x81, 0xFF, 0x01, 0x01, 0x01, 0x01, 0x01],
    [0xFF, 0x80, 0x80, 0x80, 0xFC, 0x02, 0x01, 0x01, 0x02, 0xFC],
    [0x3E, 0x40, 0x80, 0x80, 0x80, 0xFE, 0x81, 0x81, 0x81, 0x7E],
    [0xFF, 0x01, 0x02, 0x04, 0x08, 0x08, 0x10, 0x10, 0x20, 0x20],
    [0x3C, 0x42, 0x81, 0x42, 0x3C, 0x42, 0x81, 0x81, 0x42, 0x3C],
    [0x7E, 0x81, 0x81, 0x81, 0x7F, 0x01, 0x01, 0x01, 0x02, 0x7C],
    [0x18, 0x24, 0x24, 0x24, 0x42, 0x7E, 0x42, 0x81, 0x81, 0x81],
    [0xFC, 0x82, 0x82, 0x84, 0xF8, 0x84, 0x82, 0x82, 0x82, 0xFC],
    [0x3C, 0x42, 0x81, 0x80, 0x80, 0x80, 0x80, 0x81, 0x42, 0x3C],
    [0xFC, 0x82, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x82, 0xFC],
    [0xFF, 0x80, 0x80, 0x80, 0xFC, 0x80, 0x80, 0x80, 0x80, 0xFF],
    [0xFF, 0x80, 0x80, 0x80, 0xFC, 0x80, 0x80, 0x80, 0x80, 0x80],
];

/// A Chip-8 display buffer.
pub struct Buffer {
    /// The underlying display buffer data.
    data: [[bool; HEIGHT]; WIDTH],
    /// Whether the display is in high-resolution mode.
    high_resolution: bool,
    /// Whether the display needs to be refreshed.
    needs_refresh: bool,
}

impl Buffer {
    /// Returns a new display buffer with all pixels clear.
    pub fn new() -> Self {
        Buffer {
            data: [[false; HEIGHT]; WIDTH],
            high_resolution: false,
            needs_refresh: true,
        }
    }

    /// Clears the display.
    pub fn clear(&mut self) {
        for col in self.data.iter_mut() {
            for elem in col.iter_mut() {
                *elem = false;
            }
        }
        self.needs_refresh = true;
    }

    /// Returns a reference to the underlying pixel data.
    pub fn data(&self) -> &[[bool; HEIGHT]; WIDTH] {
        &self.data
    }

    /// Draws the given low-resolution sprite at the given position.
    ///
    /// Returns whether there was a collision.
    pub fn draw_sprite_low(&mut self, sprite: &[u8], x: usize, y: usize) -> bool {
        let mut collision = false;

        for (j, row) in sprite.iter().enumerate() {
            for i in 0..8 {
                if row & (1 << (7 - i)) != 0 {
                    if self.toggle(x + i, y + j) {
                        collision = true;
                    }
                }
            }
        }

        collision
    }

    /// Draws the given high-resolution sprite at the given position.
    ///
    /// Returns whether there was a collision.
    pub fn draw_sprite_high(&mut self, sprite: &[u8], x: usize, y: usize) -> bool {
        let mut collision = false;

        for (j, row) in sprite.chunks(2).enumerate() {
            for (k, chunk) in row.iter().enumerate() {
                for i in 0..8 {
                    if chunk & (1 << (7 - i)) != 0 {
                        if self.toggle(x + 8 * k + i, y + j) {
                            collision = true;
                        }
                    }
                }
            }
        }

        collision
    }

    /// Forces a refresh on the next call to `refresh`, even if no draw
    /// operation has been performed.
    pub fn force_refresh(&mut self) {
        self.needs_refresh = true;
    }

    /// Returns whether the display is in high-resolution mode.
    pub fn high(&self) -> bool {
        self.high_resolution
    }

    /// Sets whether the display is in high-resolution mode.
    pub fn set_high(&mut self, high: bool) {
        self.high_resolution = high;
    }

    /// Refreshes the display using the given refresh function.
    ///
    /// If a refresh is unnecessary, nothing will be done.  The refresh
    /// function receives a "snapshot" of the display, and should draw that to
    /// whatever user-facing display buffer is currently being used.
    pub fn refresh<F, E>(&mut self, f: F) -> Result<(), E>
    where
        F: FnOnce(&Self) -> Result<(), E>,
        E: Fail,
    {
        if self.needs_refresh {
            f(self)?;
            self.needs_refresh = false;
        }
        Ok(())
    }

    /// Scrolls the display down the given number of pixels.
    pub fn scroll_down(&mut self, amt: usize) {
        for col in self.data.iter_mut() {
            for i in 0..col.len() - amt {
                col[i] = col[i + amt];
            }
            for i in col.len() - amt..col.len() {
                col[i] = false;
            }
        }
        self.needs_refresh = true;
    }

    /// Scrolls the display left the given number of pixels.
    pub fn scroll_left(&mut self, amt: usize) {
        for i in (amt..self.data.len()).rev() {
            for j in 0..self.data[i].len() {
                self.data[i][j] = self.data[i - amt][j];
            }
        }
        for i in 0..amt {
            for elem in self.data[i].iter_mut() {
                *elem = false;
            }
        }
        self.needs_refresh = true;
    }

    /// Scrolls the display right the given number of pixels.
    pub fn scroll_right(&mut self, amt: usize) {
        for i in 0..self.data.len() - amt {
            for j in 0..self.data[i].len() {
                self.data[i][j] = self.data[i + amt][j];
            }
        }
        for i in self.data.len() - amt..self.data.len() {
            for elem in self.data[i].iter_mut() {
                *elem = false;
            }
        }
        self.needs_refresh = true;
    }

    /// Flips the on/off state of the given pixel, returning whether it was
    /// flipped off from the on state.
    fn toggle(&mut self, x: usize, y: usize) -> bool {
        if x < WIDTH && y < HEIGHT {
            let old = self.data[x][y];
            self.data[x][y] = !self.data[x][y];
            self.needs_refresh = true;

            old
        } else {
            false
        }
    }
}

impl Default for Buffer {
    fn default() -> Self {
        Buffer::new()
    }
}
