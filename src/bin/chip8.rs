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
#[macro_use]
extern crate maplit;
extern crate sdl2;

use std::collections::HashMap;
use std::default::Default;
use std::fs::File;
use std::io::Write;
use std::process;
use std::thread;

use clap::{App, Arg, ArgMatches};
use failure::{Error, ResultExt};
use log::LevelFilter;
use sdl2::audio::{AudioCallback, AudioSpecDesired};
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::Rect;
use sdl2::render::Canvas;
use sdl2::video::Window;

use chip8::display;
use chip8::interpreter::{Interpreter, Options};
use chip8::input::Key;

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
        let mut canvas = window.into_canvas().build()?;

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

/// A utility to process SDL key events and press/release the corresponding
/// buttons in the interpreter's input buffer.
struct Controller {
    /// The map from scancodes to Chip-8 keys.
    ///
    /// The alternative would be to use scancodes instead of keycodes, which
    /// would have the advantage of working even on alternative keyboard
    /// layouts with the keys in the same position, but it would also make
    /// documentation more difficult (unless we refer to the keys in the QWERTY
    /// layout, which might not be intuitive to people).  I think it's better
    /// long-term if we just have the layout configurable, and people using
    /// other layouts can change the default as they see fit.
    ///
    /// In any case, this is an easy decision to change later, so there's no
    /// need to worry too much about it now.
    keymap: HashMap<Keycode, Key>,
}

impl Controller {
    /// Returns a controller with the default keymap.
    fn new() -> Self {
        use Keycode::*;
        use Key::*;

        Controller::with_keymap(hashmap![
            Num1 => K1,
            Num2 => K2,
            Num3 => K3,
            Num4 => KC,
            Q => K4,
            W => K5,
            E => K6,
            R => KD,
            A => K7,
            S => K8,
            D => K9,
            F => KE,
            Z => KA,
            X => K0,
            C => KB,
            V => KF,
        ])
    }

    /// Returns a controller with the given keymap.
    fn with_keymap(keymap: HashMap<Keycode, Key>) -> Self {
        Controller { keymap }
    }

    /// Processes the given SDL event, applying the corresponding action to the
    /// given interpreter.
    fn process(&self, event: Event, interpreter: &mut Interpreter) {
        match event {
            Event::KeyDown {
                keycode: Some(key), ..
            } => if let Some(&key) = self.keymap.get(&key) {
                interpreter.input_mut().press(key);
            },
            Event::KeyUp {
                keycode: Some(key), ..
            } => if let Some(&key) = self.keymap.get(&key) {
                interpreter.input_mut().release(key);
            },
            _ => {}
        }
    }
}

impl Default for Controller {
    fn default() -> Self {
        Controller::new()
    }
}

/// A simple square wave generator.
///
/// Thanks to the SDL2 crate's documentation for basically giving me this code
/// :)
struct SquareWave {
    volume: f32,
    phase: f32,
    phase_inc: f32,
}

impl SquareWave {
    /// Returns a square wave generator with the given volume and frequency (in
    /// Hz).  The device's sample rate must be provided to calculate the actual
    /// frequency of samples.
    fn new(volume: f32, frequency: f32, sample_rate: i32) -> Self {
        SquareWave {
            volume,
            phase: 0.0,
            phase_inc: frequency / sample_rate as f32,
        }
    }
}

impl AudioCallback for SquareWave {
    type Channel = f32;

    fn callback(&mut self, out: &mut [f32]) {
        for x in out.iter_mut() {
            *x = if self.phase <= 0.5 {
                self.volume
            } else {
                -self.volume
            };
            self.phase = (self.phase + self.phase_inc) % 1.0;
        }
    }
}

fn main() {
    let matches = App::new("chip8")
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

    let filename = matches.value_of("FILE").unwrap();
    let mut input =
        File::open(filename).with_context(|_| format!("could not open file '{}'", filename))?;
    let mut interpreter = Interpreter::with_options(opts);
    interpreter
        .load_program(&mut input)
        .with_context(|_| format!("could not load program from file '{}'", filename))?;

    let sdl_context = sdl2::init()
        .map_err(SdlError)
        .context("could not initialize SDL")?;
    let video_subsystem = sdl_context
        .video()
        .map_err(SdlError)
        .context("could not initialize SDL video subsystem")?;
    let audio_subsystem = sdl_context
        .audio()
        .map_err(SdlError)
        .context("could not initialize SDL audio subsystem")?;
    let mut event_pump = sdl_context
        .event_pump()
        .map_err(SdlError)
        .context("could not initialize SDL event loop")?;
    let mut display = Display::new(
        video_subsystem,
        display::WIDTH as u32 * scale,
        display::HEIGHT as u32 * scale,
        Color::RGB(0, 0, 0),
        Color::RGB(255, 255, 255),
    )?;
    let controller = Controller::new();
    let device = audio_subsystem
        .open_playback(
            None,
            &AudioSpecDesired {
                freq: Some(44100),
                channels: Some(1),
                samples: None,
            },
            |spec| SquareWave::new(volume as f32 / 100.0, tone as f32, spec.freq),
        )
        .map_err(SdlError)
        .context("could not initialize SDL audio playback")?;

    'main: loop {
        for event in event_pump.poll_iter() {
            match event {
                Event::Quit { .. } => break 'main,
                Event::Window { .. } => interpreter.display_mut().force_refresh(),
                e => controller.process(e, &mut interpreter),
            }
        }

        interpreter
            .display_mut()
            .refresh(|buf| display.draw(buf))
            .context("could not refresh display window")?;
        // The necessary context for any error in 'step' should be provided
        // from the method itself; providing more context here would shadow the
        // more useful errors defined there.
        interpreter.step()?;
        if interpreter.halted() {
            info!("interpreter was halted");
            break;
        }
        if interpreter.st() != 0 {
            device.resume();
        } else {
            device.pause();
        }
        thread::yield_now();
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
