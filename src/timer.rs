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

use time;

/// A basic timer.
#[derive(Debug)]
pub struct Timer {
    /// Whether the timer is enabled.
    enabled: bool,
    /// The frequency at which to run the timer.
    frequency: u32,
    /// A latch that is released (set to `false`) on every clock cycle.
    latch: bool,
    /// Whether we are waiting for a latch release.
    latch_waiting: bool,
    /// An internal number of ticks.
    ticks: Wrapping<u32>,
}

impl Timer {
    /// Returns a new timer running at the given frequency.
    pub fn new(frequency: u32) -> Self {
        let mut timer = Timer::new_disabled(frequency);
        timer.enabled = true;
        timer.update();
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

    /// Returns the number of ticks which have elapsed since the last call to
    /// this method (or the creation of the timer).
    ///
    /// This will also release the latch if at least one tick has elapsed.
    ///
    /// If the timer is disabled, this always returns 0 and doesn't actually do
    /// anything else.
    pub fn lap(&mut self) -> u32 {
        if self.enabled {
            let old = self.ticks;
            self.update();
            let ticks = (self.ticks - old).0;
            if ticks > 0 {
                self.latch = false;
            }
            ticks
        } else {
            0
        }
    }

    /// Sets the latch or waits for it to be released.
    ///
    /// If we are not already waiting for the latch, it is set and `false` is
    /// returned; if we are, then this will return `false` until the latch is
    /// released.  When the latch is finally released, we return `true` and
    /// stop waiting for the latch.
    pub fn wait_for_latch(&mut self) -> bool {
        if self.latch_waiting {
            if self.latch {
                false
            } else {
                self.latch_waiting = false;
                true
            }
        } else {
            self.latch_waiting = true;
            false
        }
    }

    /// Updates the internal `ns` value.
    fn update(&mut self) {
        self.ticks =
            Wrapping((time::precise_time_ns() as f64 * self.frequency as f64 / 1e9) as u32);
    }
}
