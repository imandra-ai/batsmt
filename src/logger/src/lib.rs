
extern crate log;

use {
    log::{Log, Record, LevelFilter, Metadata},
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
            s => {
                eprintln!("unknown logging level {:?}", s);
                return;
            },
        };
        let logger = Logger(lvl);
        log::set_max_level(lvl);
        log::set_boxed_logger(Box::new(logger)).unwrap();
    };
}

/// Logger implementation.
struct Logger(LevelFilter);

impl Log for Logger {
    #[inline(always)]
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.0
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let path = record.module_path().unwrap_or("<>");
            eprintln!("[{} {}] {}", record.level(), path, record.args());
        }
    }

    fn flush(&self) {}
}


