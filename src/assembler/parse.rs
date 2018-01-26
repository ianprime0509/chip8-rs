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

use combine::{any, between, eof, many, one_of, optional, satisfy, sep_by, token, try, chainl1,
              many1};
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
pub struct NonexistentLabelError(pub String);

/// An error encountered while evaluating an expression.
#[derive(Debug, Fail)]
#[fail(display = "could not evaluate expression: {}", _0)]
pub struct ExpressionEvalError(pub String);

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

/// A line of a certain type (assignment or instruction).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Line {
    /// An assignment statement, with the label name and operand (to be
    /// evaluated).
    Assignment(String, String),
    /// An instruction, with an optional label and the instruction (with
    /// operands).
    Instruction(Option<String>, Option<(String, Vec<String>)>),
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

/// Parses an operand which should be only an identifier and nothing else.
pub fn ident_only(operand: &str) -> Result<String, ExpressionEvalError> {
    spaces()
        .with(ident())
        .skip(spaces())
        .skip(eof().expected("end of operand"))
        .parse(operand)
        .map(|(got, _)| got)
        .map_err(|e| ExpressionEvalError(util::format_parse_error(&e)))
}

/// Parses an operand to an instruction (or the body of an assignment).
parser!{
    fn operand[I]()(I) -> String
    where [I: Stream<Item = char>]
    {
        many1(satisfy(|c| c != ',' && c != ';'))
            .skip(spaces())
            .map(|s: String| s.trim().to_owned())
    }
}

/// Parses a line containing an (optional) label and an (optional) instruction.
parser!{
    pub fn line[I]()(I) -> Line
    where [I: Stream<Item = char>]
    {
        let label = ident().skip(token(':')).skip(spaces());
        let operation = ident().skip(spaces());
        let operands = sep_by(operand(), token(',').skip(spaces())).skip(spaces());
        let instruction = operation.and(operands);
        // A comment will just consume everything else on the line.
        let comment = token(';').and(many::<Vec<_>, _>(any()));

        let assignment = ident().skip(spaces())
            .skip(token('=').skip(spaces()))
            .and(operand())
            .map(|(label, operand)| Line::Assignment(label, operand));
        let line = optional(try(label))
            .and(optional(try(instruction)))
            .map(|(label, instruction)| Line::Instruction(label, instruction));

        spaces().with(try(assignment).or(line))
            .skip(optional(comment))
            .skip(eof())
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
                        token(')').skip(spaces()),
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
            .and(factor(ltable))
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
        chainl1(or_op(ltable), token('|').skip(spaces())
                .map(|_| |l: u16, r: u16| l | r))
            .skip(spaces())
            .expected("expression")
    }
}

/// Parses a top-level expression (a complete operand).
parser!{
    fn expr_top['a, I](ltable: &'a HashMap<String, u16>)(I) -> u16
    where [I: Stream<Item = char>]
    {
        spaces().with(expr(ltable))
            .skip(spaces())
            .skip(eof().expected("end of expression"))
    }
}

/// Evaluates the given expression, returning its value.
pub fn eval(expression: &str, ltable: &HashMap<String, u16>) -> Result<u16, Error> {
    expr_top(ltable)
        .parse(expression)
        .map(|x| x.0)
        .map_err(|e| ExpressionEvalError(util::format_parse_error(&e)).into())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use combine::Parser;

    use super::{eval, line, Line};
    use util::format_parse_error;

    /// Tests line parsing.
    #[test]
    fn parse_line() {
        use self::Line::*;

        let cases = [
            (
                "label_only:\t   \t ; a comment",
                Instruction(Some("label_only".into()), None),
            ),
            (
                "operation op1 , op2, op3 ; trick, ",
                Instruction(
                    None,
                    Some((
                        "operation".into(),
                        vec!["op1".into(), "op2".into(), "op3".into()],
                    )),
                ),
            ),
            (
                "label:  AND  op,op + 2   ,    op3  \t\t",
                Instruction(
                    Some("label".into()),
                    Some((
                        "AND".into(),
                        vec!["op".into(), "op + 2".into(), "op3".into()],
                    )),
                ),
            ),
            ("     ;  nothing to see here!", Instruction(None, None)),
            ("", Instruction(None, None)),
            ("label = 2 + 2", Assignment("label".into(), "2 + 2".into())),
            (
                "    \thi_there = 2 * 6 - 2  ; with a comment",
                Assignment("hi_there".into(), "2 * 6 - 2".into()),
            ),
        ];

        for &(input, ref expected) in cases.iter() {
            let parsed = match line().parse(input) {
                Ok(p) => p.0,
                Err(e) => panic!(
                    "failed to parse line {:?}: {}",
                    input,
                    format_parse_error(&e)
                ),
            };
            assert_eq!(&parsed, expected);
        }
    }

    /// Tests parse failures on bad lines.
    #[test]
    fn fail_line() {
        let cases = [
            "bad:  000 ; not an operation",
            "ADD 2,",
            ",",
            ":",
            "label: operation op,",
        ];

        for &case in cases.iter() {
            assert!(
                line().parse(case).is_err(),
                "successfully parsed {:?}",
                case
            );
        }
    }

    /// Tests expression evaluation.
    #[test]
    fn expr_eval() {
        let ltable = hashmap![
            "label1".into() => 10,
            "TEST_ident".into() => 50,
            "weird00D".into() => 100,
        ];

        let cases = [
            ("1 + 1", 1 + 1),
            ("4 - 3", 4 - 3),
            ("#20 * $101", 0x20 * 0b101),
            ("78 / 5", 78 / 5),
            ("24 % 7", 24 % 7),
            ("8 < 2", 8 << 2),
            ("5 > 2", 5 >> 2),
            ("$10101 & $11001", 0b10101 & 0b11001),
            ("$11001 ^ $11100", 0b11001 ^ 0b11100),
            ("$10001 | $01001", 0b10001 | 0b01001),
            ("2 + 6 * 5", 2 + 6 * 5),
            ("2 * 5 + 6", 2 * 5 + 6),
            ("(2 + 6) * 5", (2 + 6) * 5),
            ("-1", 1u16.wrapping_neg()),
            ("-(1 + 2)", (1u16 + 2).wrapping_neg()),
            ("~$1100110", !0b1100110),
            ("1 < 2 + 2", 1 << 2 + 2),
            ("1 | 1 ^ 1 & 1", 1 | 1 ^ 1 & 1),
            ("((((6 + 6))) + ((2)))", 6 + 6 + 2),
            ("~~--1", 1),
            ("1+1+1", 1 + 1 + 1),
            ("2\t-1\t+1            ", 2 - 1 + 1),
            ("label1 + TEST_ident+weird00D", 10 + 50 + 100),
            ("-label1", 10u16.wrapping_neg()),
            ("~weird00D", !100),
        ];

        for &(ref expression, result) in cases.iter() {
            let evaluated = match eval(expression, &ltable) {
                Ok(n) => n,
                Err(e) => panic!("could not evaluate {:?}: {}", expression, e),
            };
            assert_eq!(evaluated, result, "improper evaluation of {:?}", expression);
        }
    }

    /// Tests failure on malformed expression evaluation.
    ///
    /// All of the cases in this test should *fail* when they are evaluated,
    /// since they are malformed.  We don't use the `#[should_panic]` attribute
    /// since we want to have multiple cases and not just check the first one.
    #[test]
    fn expr_fail() {
        let ltable = HashMap::new();
        let cases = [
            "1 +",
            "2 + -",
            "5 + + 4",
            "&",
            "",
            "(((4))",
            "5)",
            "4 << 2",
            "undefined + 2",
            "also_undefined",
        ];

        for case in cases.iter() {
            assert!(
                eval(case, &ltable).is_err(),
                "evaluation of {:?} succeeded",
                case
            );
        }
    }
}
