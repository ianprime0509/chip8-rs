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

//! Parsing functions for the assembler.

use combine::{many, optional, satisfy, sep_by, token, try};
use combine::char::spaces;
use combine::{Parser, Stream};

/// Returns whether the given character could be the first character in an
/// identifier.
fn is_ident_start(c: char) -> bool {
    'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '_'
}

/// Returns whether the given character could be inside an identifier, but not
/// necessarily as the first character.
fn is_ident_inner(c: char) -> bool {
    is_ident_start(c) || '0' <= c && c <= '9'
}

/// Parses an identifier.
parser!{
    fn ident[I]()(I) -> String
    where [I: Stream<Item = char>]
    {
        satisfy(is_ident_start)
            .and(many(satisfy(is_ident_inner)))
            .map(|(c, s): (char, String)| {
                let mut ident = String::with_capacity(s.len() + 1);
                ident.push(c);
                ident.push_str(&s);
                ident
            })
            .expected("identifier")
    }
}

/// Parses a line containing an (optional) label and an (optional) instruction.
parser!{
    pub fn line[I]()(I) -> (Option<String>, Option<(String, Vec<String>)>)
    where [I: Stream<Item = char>]
    {
        let label = ident().skip(token(':'));
        let operation = ident();
        let operand = many(satisfy(|c| c != ',' && c != ';'));
        let operands = sep_by(operand, token(','));
        let instruction = operation
            .skip(spaces())
            .and(operands);

        optional(try(label))
            .skip(spaces())
            .and(optional(try(instruction)))
    }
}
