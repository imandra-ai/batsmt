
//! Time indicator.

use {
    std::time::Instant,
};

/// A chronometer, to measure time.
pub struct Chrono(Instant);

impl Chrono {
    /// New chronometer.
    pub fn new() -> Self { Chrono(Instant::now()) }

    /// Duration, in seconds (rounded at the millisecond)
    pub fn as_f64(&self) -> f64 {
        let d = self.0.elapsed();
        d.as_secs() as f64 + (d.subsec_millis() as f64 * 1e-3)
    }
}

