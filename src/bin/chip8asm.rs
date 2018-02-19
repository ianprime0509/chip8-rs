/*
 * Copyright 2018 Ian Johnson
 *
 * This is free software, distributed under the MIT license.  A copy of the
 * license can be found in the LICENSE file in the project root, or at
 * https://opensource.org/licenses/MIT.
 */

//! The `chip8asm` binary program.

extern crate chip8;
extern crate clap;
extern crate env_logger;
extern crate failure;
#[macro_use]
extern crate log;

use std::fs::File;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process;

use clap::{App, Arg, ArgMatches};
use failure::{Error, ResultExt};
use log::LevelFilter;

use chip8::Assembler;
use chip8::assembler::Options;

const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The default output file extension.
const DEFAULT_OUTPUT_EXT: &str = "bin";
/// The default output file when the input is stdin.
const DEFAULT_OUTPUT_FILE: &str = "output.bin";

fn main() {
    let matches = App::new("chip8asm")
        .version(VERSION)
        .author("Ian Johnson <ianprime0509@gmail.com>")
        .about("A Chip-8/Super-Chip interpreter")
        .help_message("show this help message and exit")
        .version_message("show version information and exit")
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .value_name("OUTPUT")
                .help("set output file name")
                .takes_value(true),
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
                .help("set the assembler source file")
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
    let input_file = matches.value_of("FILE").unwrap_or("-");
    let stdin = io::stdin();
    let mut input: Box<Read> = if input_file == "-" {
        Box::new(stdin.lock())
    } else {
        Box::new(File::open(input_file)
            .with_context(|_| format!("could not open input file '{}'", input_file))?)
    };

    let output_file = match matches.value_of("output") {
        Some(out) => Path::new(out).to_owned(),
        None => output_filepath(input_file),
    };
    let mut output = File::create(&output_file).with_context(|_| {
        format!(
            "could not open output file '{}'",
            output_file.to_string_lossy()
        )
    })?;

    let mut opts = Options::new();
    opts.shift_quirks = matches.is_present("shift-quirks");
    let asm = Assembler::with_options(opts);
    asm.assemble(&mut input, &mut output)?;

    Ok(())
}

/// Returns a reasonable output filepath from the given input filename.
///
/// Basically, this changes the extension (or adds it if not present) to
/// `.bin`, but does not do this if the given filename is `-` (the default will
/// be as specified in the `DEFAULT_OUTPUT_FILE` constant).
fn output_filepath(input_filename: &str) -> PathBuf {
    if input_filename == "-" {
        let mut p = PathBuf::new();
        p.push(DEFAULT_OUTPUT_FILE);
        p
    } else {
        let mut p = Path::new(input_filename).to_owned();
        p.set_extension(DEFAULT_OUTPUT_EXT);
        p
    }
}
