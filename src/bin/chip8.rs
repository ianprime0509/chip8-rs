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
#[macro_use]
extern crate failure;
#[macro_use]
extern crate log;
extern crate sdl2;

use std::fs::File;
use std::io::Write;
use std::process;

use clap::{App, Arg, ArgMatches};
use env_logger::Builder;
use failure::{Error, Fail, ResultExt};
use log::LevelFilter;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use sdl2::render::Canvas;
use sdl2::video::Window;

use chip8::display;
use chip8::interpreter::{Interpreter, Options};

const VERSION: &str = env!("CARGO_PKG_VERSION");

/// An SDL error.
#[derive(Debug, Fail)]
#[fail(display = "SDL error: {}", _0)]
struct SdlError(String);

/// The display buffer for the interpreter.
struct Display {
    /// The underlying SDL canvas.
    canvas: Canvas<Window>,
    /// The background color to use.
    bg: Color,
    /// The foreground color to use.
    fg: Color,
}

impl Display {
    /// Initializes the display and returns the resulting object.
    fn new(
        video_subsystem: sdl2::VideoSubsystem,
        width: u32,
        height: u32,
        bg: Color,
        fg: Color,
    ) -> Result<Self, Error> {
        let window = video_subsystem.window("Chip-8", width, height).build()?;
        let mut canvas = window.into_canvas().present_vsync().build()?;

        canvas.set_draw_color(bg);
        canvas.clear();
        canvas.present();

        Ok(Display { canvas, bg, fg })
    }

    /// Draws the given Chip-8 display buffer to the window.
    fn draw(&mut self, buffer: &display::Buffer) -> Result<(), SdlError> {
        let (width, height) = self.canvas.window().size();
        let scalex = width / display::WIDTH as u32;
        let scaley = height / display::HEIGHT as u32;

        self.canvas.set_draw_color(self.bg);
        self.canvas.clear();
        self.canvas.set_draw_color(self.fg);
        if buffer.high() {
            for (x, col) in buffer.data().iter().enumerate() {
                for (y, &pixel) in col.iter().enumerate() {
                    if pixel {
                        let x = x as i32 * scalex as i32;
                        let y = y as i32 * scaley as i32;

                        self.canvas
                            .fill_rect(Rect::new(x, y, scalex, scaley))
                            .map_err(SdlError)?;
                    }
                }
            }
        } else {
            for (x, col) in buffer.data().iter().take(display::WIDTH / 2).enumerate() {
                for (y, &pixel) in col.iter().take(display::HEIGHT / 2).enumerate() {
                    if pixel {
                        let scalex = 2 * scalex;
                        let scaley = 2 * scaley;
                        let x = x as i32 * scalex as i32;
                        let y = y as i32 * scaley as i32;

                        self.canvas
                            .fill_rect(Rect::new(x, y, scalex, scaley))
                            .map_err(SdlError)?;
                    }
                }
            }
        }
        self.canvas.present();
        Ok(())
    }
}

fn main() {
    let matches = App::new("Chip-8")
        .version(VERSION)
        .author("Ian Johnson <ianprime0509@gmail.com>")
        .about("A Chip-8/Super-Chip interpreter")
        .help_message("show this help message and exit")
        .version_message("show version information and exit")
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
    let filename = matches.value_of("FILE").unwrap();
    let mut input =
        File::open(filename).with_context(|_| format!("could not open file '{}'", filename))?;
    let mut interpreter = Interpreter::with_options(opts);
    interpreter
        .load_program(&mut input)
        .with_context(|_| format!("could not load program from file '{}'", filename))?;

    let sdl_context = sdl2::init().map_err(SdlError)?;
    let video_subsystem = sdl_context.video().map_err(SdlError)?;
    let mut event_pump = sdl_context.event_pump().map_err(SdlError)?;
    let mut display = Display::new(
        video_subsystem,
        display::WIDTH as u32 * scale,
        display::HEIGHT as u32 * scale,
        Color::RGB(0, 0, 0),
        Color::RGB(255, 255, 255),
    )?;

    'main: loop {
        for event in event_pump.poll_iter() {
            match event {
                Event::Quit { .. } => break 'main,
                _ => {}
            }
        }

        interpreter.display_mut().refresh(|buf| display.draw(buf))?;
        interpreter.step()?;
    }

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
