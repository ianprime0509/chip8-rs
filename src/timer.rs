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

//! A basic timer.

use std::num::Wrapping;

/// A basic timer.
#[derive(Debug)]
pub struct Timer {
    /// Whether the timer is enabled.
    enabled: bool,
    /// The frequency at which to run the timer.
    frequency: u32,
    /// A latch that is released on every clock cycle.
    latch: bool,
    /// Whether we are waiting for a latch release.
    latch_waiting: bool,
    /// An internal number of ticks.
    ///
    /// The absolute number of ticks is meaningless; it is only relative values
    /// (differences between two values) that are significant.
    ticks: Wrapping<u32>,
}

impl Timer {
    /// Returns a new timer running at the given frequency.
    pub fn new(frequency: u32) -> Self {
        let mut timer = Timer::new_disabled(frequency);
        timer.enabled = true;
        timer
    }

    /// Returns a new timer at the given frequency which is disabled.
    pub fn new_disabled(frequency: u32) -> Self {
        Timer {
            enabled: false,
            frequency,
            latch: false,
            latch_waiting: false,
            ticks: Wrapping(0),
        }
    }
}
