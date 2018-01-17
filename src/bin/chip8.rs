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

//! The `chip8` binary program.

extern crate chip8;
extern crate clap;
extern crate env_logger;
extern crate failure;
#[macro_use]
extern crate log;

use std::io::Write;
use std::process;

use clap::{App, Arg, ArgMatches};
use env_logger::Builder;
use failure::{Error, ResultExt};
use log::LevelFilter;

use chip8::interpreter::{Interpreter, Options};

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    let matches = App::new("Chip-8")
        .version(VERSION)
        .author("Ian Johnson <ianprime0509@gmail.com>")
        .about("A Chip-8/Super-Chip interpreter")
        .arg(
            Arg::with_name("frequency")
                .long("frequency")
                .value_name("FREQ")
                .help("set game timer frequency (in Hz)")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("load-quirks")
                .short("l")
                .long("load-quirks")
                .help("enable load quirks mode"),
        )
        .arg(
            Arg::with_name("shift-quirks")
                .short("q")
                .long("shift-quirks")
                .help("enable shift quirks mode"),
        )
        .arg(
            Arg::with_name("scale")
                .short("s")
                .long("scale")
                .value_name("SCALE")
                .help("set game display scale")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("tone")
                .short("t")
                .long("tone")
                .value_name("FREQ")
                .help("set game buzzer tone (in Hz)")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("verbose")
                .short("v")
                .long("verbose")
                .multiple(true)
                .help("increase verbosity"),
        )
        .arg(
            Arg::with_name("volume")
                .long("volume")
                .value_name("VOL")
                .help("set game buzzer volume (0-100)")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("FILE")
                .help("set the program file to run")
                .required(true)
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

    Builder::new()
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
    let mut opts = Options::new();
    process_opts(&mut opts, matches)?;
    let scale = matches
        .value_of("scale")
        .map(|n| n.parse::<u32>())
        .unwrap_or(Ok(6))
        .context("invalid scale argument")?;
    let tone = matches
        .value_of("tone")
        .map(|n| n.parse::<u32>())
        .unwrap_or(Ok(440))
        .context("invalid tone argument")?;
    let volume = matches
        .value_of("volume")
        .map(|n| n.parse::<u32>())
        .unwrap_or(Ok(10))
        .context("invalid volume argument")?;

    println!("scale is {}; tone is {}; volume is {}", scale, tone, volume);
    let mut _interpreter = Interpreter::with_options(opts);
    Ok(())
}

/// Processes the command-line arguments and changes the necessary fields of
/// the given interpreter options.
fn process_opts(opts: &mut Options, matches: &ArgMatches) -> Result<(), Error> {
    if let Some(freq) = matches.value_of("frequency") {
        opts.timer_freq = freq.parse::<u32>().context("invalid frequency argument")?;
    }
    if matches.is_present("load-quirks") {
        opts.load_quirks = true;
    }
    if matches.is_present("shift-quirks") {
        opts.shift_quirks = true;
    }

    Ok(())
}
