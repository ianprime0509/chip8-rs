/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! The `chip8disasm` binary program.

extern crate chip8;
extern crate clap;
extern crate env_logger;
extern crate failure;
#[macro_use]
extern crate log;

use std::fs::File;
use std::io::{self, Read, Write};
use std::process;

use clap::{App, Arg, ArgMatches};
use failure::{Error, ResultExt};
use log::LevelFilter;

use chip8::Disassembler;
use chip8::disassembler::Options;

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    let matches = App::new("chip8disasm")
        .version(VERSION)
        .author("Ian Johnson <ianprime0509@gmail.com>")
        .about("A Chip-8/Super-Chip disassembler")
        .help_message("show this help message and exit")
        .version_message("show this version information and exit")
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .value_name("OUTPUT")
                .help("set output file name")
                .takes_value(true)
                .default_value("-"),
        )
        .arg(
            Arg::with_name("shift-quirks")
                .short("q")
                .long("shift-quirks")
                .help("enable shift quirks mode"),
        )
        .arg(
            Arg::with_name("verbose")
                .short("v")
                .long("verbose")
                .multiple(true)
                .help("increase verbosity"),
        )
        .arg(
            Arg::with_name("FILE")
                .help("set the disassembler source file")
                .default_value("-")
                .index(1),
        )
        .get_matches();

    let verbosity = matches.occurrences_of("verbose");
    let filter = match verbosity {
        0 => LevelFilter::Warn,
        1 => LevelFilter::Info,
        2 => LevelFilter::Debug,
        _ => LevelFilter::Trace,
    };

    env_logger::Builder::new()
        .filter(None, filter)
        .format(|buf, record| writeln!(buf, "{}: {}", record.level(), record.args()))
        .init();

    if let Err(e) = run(&matches) {
        error!("{}", e);
        for cause in e.causes().skip(1) {
            info!("caused by: {}", cause);
        }
        trace!("backtrace: {}", e.backtrace());
        process::exit(1);
    }
}

fn run(matches: &ArgMatches) -> Result<(), Error> {
    let input_file = matches.value_of("FILE").unwrap();
    let stdin = io::stdin();
    let mut input: Box<Read> = if input_file == "-" {
        Box::new(stdin.lock())
    } else {
        Box::new(File::open(input_file)
            .with_context(|_| format!("could not open input file '{}'", input_file))?)
    };

    let output_file = matches.value_of("output").unwrap();
    let stdout = io::stdout();
    let mut output: Box<Write> = if output_file == "-" {
        Box::new(stdout.lock())
    } else {
        Box::new(File::open(output_file)
            .with_context(|_| format!("could not open output file '{}'", output_file))?)
    };

    let mut opts = Options::new();
    opts.shift_quirks = matches.is_present("shift-quirks");
    let disasm = Disassembler::with_options(&mut input, opts)?;
    disasm.dump(&mut output)?;

    Ok(())
}
