
extern crate log;

use {
    log::{Log, Record, Level, LevelFilter, Metadata},
    colored::*,
};

/// Initialize the logging infrastructure.
pub fn init() {
    if let Ok(s) = std::env::var("RUST_LOG") {
        let lvl = match s.as_str() {
            "none" => {
                return; // disabled
            },
            "info" => LevelFilter::Info,
            "error" => LevelFilter::Error,
            "warn" => LevelFilter::Warn,
            "trace" => LevelFilter::Trace,
            "debug" => LevelFilter::Debug,
            s => {
                eprintln!("unknown logging level {:?}", s);
                return;
            },
        };
        let logger = Logger(lvl, PPLevels::new());
        log::set_max_level(lvl);
        log::set_boxed_logger(Box::new(logger)).unwrap();
    };
}

struct PPLevels {
    info: ColoredString,
    debug: ColoredString,
    error: ColoredString,
    trace: ColoredString,
    warn: ColoredString,
}

impl PPLevels {
    fn new() -> Self {
        PPLevels{
            info: "INFO ".purple().bold(),
            debug: "DEBUG".green().dimmed(),
            error: "ERROR".white().on_red().bold(),
            trace: "TRACE".blue().dimmed(),
            warn: "WARN ".yellow().bold(),
        }
    }

    /// Get constant string for this level
    fn get(&self, lvl: Level) -> &ColoredString {
        match lvl {
            Level::Trace => &self.trace,
            Level::Info => &self.info,
            Level::Debug => &self.debug,
            Level::Warn => &self.warn,
            Level::Error => &self.error,
        }
    }
}

/// Logger implementation.
struct Logger(LevelFilter, PPLevels);

impl Log for Logger {
    #[inline(always)]
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.0
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            // TODO: colorize path as "dimmed", but without allocating a string
            let path = record.module_path().unwrap_or("<>");
            let lvl = self.1.get(record.level());
            eprintln!("[{} {}] {}", lvl, path, record.args());
        }
    }

    fn flush(&self) {}
}


