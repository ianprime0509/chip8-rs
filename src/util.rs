/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

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
