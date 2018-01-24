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
//!
//! For the sake of consistency, we follow the convention that all parsers in
//! the "expression" class (that is, parsers that parse different operator
//! precedence levels, like `term`) should consume whitespace *after* the
//! actual content of the expression, but don't need to worry about consuming
//! it before the expression starts.  This implies that all parsers will start
//! parsing right at the beginning of their desired content.

use std::collections::HashMap;

use combine::{between, eof, many, one_of, optional, satisfy, sep_by, token, try, chainl1, many1};
use combine::char::{digit, hex_digit, spaces};
use combine::{Parser, Stream};
// For some reason, the compiler complains about `Fail` being unused even
// though it's clearly used in one of the macros; this probably has something
// to do with https://github.com/rust-lang/rust/issues/43970
#[allow(unused_imports)]
use failure::Fail;
use failure::Error;

use util;

/// An error resulting from a nonexistent label.
#[derive(Debug, Fail)]
#[fail(display = "label '{}' does not exist", _0)]
pub struct NonexistentLabelError(String);

/// An error encountered while evaluating an expression.
#[derive(Debug, Fail)]
#[fail(display = "could not evaluate expression: {}", _0)]
pub struct ExpressionEvalError(String);

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
            .map(|(c, mut s): (char, String)| {
                s.insert(0, c);
                s
            })
            .expected("identifier")
    }
}

/// Parses a line containing an (optional) label and an (optional) instruction.
parser!{
    pub fn line[I]()(I) -> (Option<String>, Option<(String, Vec<String>)>)
    where [I: Stream<Item = char>]
    {
        let label = ident().skip(token(':')).skip(spaces());
        let operation = ident().skip(spaces());
        let operand = many1(satisfy(|c| c != ',' && c != ';'))
            .skip(spaces())
            .map(|s: String| s.trim().to_owned());
        let operands = sep_by(operand, token(',').skip(spaces())).skip(spaces());
        let instruction = operation.and(operands);

        spaces().with(optional(try(label)))
            .and(optional(try(instruction)))
    }
}

/// Parses a numeric literal (binary, decimal or hexadecimal).
parser!{
    fn number[I]()(I) -> u16
    where [I: Stream<Item = char>]
    {
        let binary = token('$')
            .with(many1(satisfy(|c| c == '0' || c == '1'))
                 .and_then(|s: String| u16::from_str_radix(&s, 2)))
            .expected("binary literal");
        let hex = token('#')
            .with(many1(hex_digit())
                 .and_then(|s: String| u16::from_str_radix(&s, 16)))
            .expected("hexadecimal literal");
        let decimal = many1(digit())
            .and_then(|s: String| u16::from_str_radix(&s, 10))
            .expected("decimal literal");

        choice!(binary, hex, decimal)
            .skip(spaces())
    }
}

/// Parses an identifer, returning the value looked up using the given
/// label table.
parser!{
    fn variable['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        ident()
            .and_then(|s| ltable
                      .get(&s)
                      .map(|v| *v)
                      .ok_or(NonexistentLabelError(s).compat()))
            .skip(spaces())
    }
}

/// Parses a number or an identifier, or an expression in parentheses.
parser!{
    fn parens['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        choice!(choice!(number(), variable(ltable)),
                between(token('(').skip(spaces()),
                        token(')'),
                        expr(ltable)))
        .skip(spaces())
        .expected("number, label name or '('")
    }
}

/// Parses an expression starting with a unary operator.
parser!{
    fn factor['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        let unary = one_of("-~".chars())
            .skip(spaces())
            .and(parens(ltable))
            .map(|(op, num)| match op {
                '-' => num.wrapping_neg(),
                '~' => !num,
                _ => unreachable!(),
            })
            .skip(spaces());

        choice!(unary, parens(ltable))
            .expected("unary operator, number, label name or '('")
    }
}

/// Parses a term (expression containing `*`, `/` or `%`).
parser!{
    fn term['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        factor(ltable)
            .and(many::<Vec<_>, _>(one_of("*/%".chars())
                                   .skip(spaces())
                                   .and(factor(ltable))))
            .map(|(f, ops)| ops.iter().fold(f, |acc, &(op, other)| match op {
                '*' => acc.wrapping_mul(other),
                '/' => acc.wrapping_div(other),
                '%' => acc.wrapping_rem(other),
                _ => unreachable!(),
            }))
            .skip(spaces())
            .expected("term")
    }
}

/// Parses a shift operand (expression containing `+` or `-`).
parser!{
    fn shift_op['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        term(ltable)
            .and(many::<Vec<_>, _>(one_of("+-".chars())
                                   .skip(spaces())
                                   .and(term(ltable))))
            .map(|(f, ops)| ops.iter().fold(f, |acc, &(op, other)| match op {
                '+' => acc.wrapping_add(other),
                '-' => acc.wrapping_sub(other),
                _ => unreachable!(),
            }))
            .skip(spaces())
            .expected("shift operand")
    }
}

/// Parses a bitwise AND operand (expression containing `>` or `<`).
parser!{
    fn and_op['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        shift_op(ltable)
            .and(many::<Vec<_>, _>(one_of("><".chars())
                                   .skip(spaces())
                                   .and(shift_op(ltable))))
            .map(|(f, ops)| ops.iter().fold(f, |acc, &(op, other)| match op {
                '>' => acc.wrapping_shr(other as u32),
                '<' => acc.wrapping_shl(other as u32),
                _ => unreachable!()
            }))
            .skip(spaces())
            .expected("AND operand")
    }
}

/// Parses a bitwise XOR operand (expression containing '&').
parser!{
    fn xor_op['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        chainl1(and_op(ltable), token('&').skip(spaces())
                .map(|_| |l: u16, r: u16| l & r))
            .skip(spaces())
            .expected("XOR operand")
    }
}

/// Parses a bitwise OR operand (expression containing '^').
parser!{
    fn or_op['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        chainl1(xor_op(ltable), token('^').skip(spaces())
                .map(|_| |l: u16, r: u16| l ^ r))
            .skip(spaces())
            .expected("OR operand")
    }
}

/// Parses an expression.
parser!{
    fn expr['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        spaces().with(chainl1(or_op(ltable), token('|').skip(spaces())
                              .map(|_| |l: u16, r: u16| l | r)))
            .skip(spaces())
            .skip(eof().expected("end of expression"))
    }
}

/// Evaluates the given expression, returning its value.
pub fn eval(expression: &str, ltable: &HashMap<String, u16>) -> Result<u16, Error> {
    expr(ltable)
        .parse(expression)
        .map(|x| x.0)
        .map_err(|e| ExpressionEvalError(util::format_parse_error(&e)).into())
}
