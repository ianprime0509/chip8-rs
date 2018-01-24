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

//! Various utility functions.

use std::fmt::Display;

use combine::{ParseError, Stream};

/// Formats a parse error into a nice string.
///
/// This is just here because I don't like the default formatting, and would
/// rather have something more compact.
pub fn format_parse_error<S>(e: &ParseError<S>) -> String
where
    S: Stream,
    S::Range: Display,
    S::Item: Display,
{
    use combine::primitives::Error::*;
    use combine::primitives::Info;

    fn info_string<T, R>(i: &Info<T, R>) -> String
    where
        T: Display,
        R: Display,
    {
        use combine::primitives::Info::*;
        match *i {
            Token(ref t) => format!("'{}'", t),
            Range(ref t) => format!("'{}'", t),
            Owned(ref t) => t.clone(),
            Borrowed(t) => t.to_owned(),
        }
    }

    e.errors
        .iter()
        .map(|e| match *e {
            Unexpected(ref info) => format!("unexpected {}", info_string(info)),
            Expected(ref info) => format!("expected {}", info_string(info)),
            Message(ref info) => info_string(info),
            Other(ref err) => err.to_string(),
        })
        .collect::<Vec<_>>()
        .join("; ")
}
