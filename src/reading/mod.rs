//! Interactive textbook reading subsystem.
//!
//! See README.md and DESIGN.md for scope and implementation order.

mod capture;
#[rustfmt::skip]
mod capture_generated;
mod build_reading;
mod export_reading;
mod helper;
mod parse_reading_command;
mod partition_reading;
mod reading_command;
mod serve_reading;
mod upload_cache;

pub use build_reading::{build_reading, ReadingBuildResult};
pub use export_reading::{export_reading, reading_html, APP_JS, READER_CSS, READER_JS};
pub use parse_reading_command::parse_reading_command;
pub use reading_command::{ReadingAction, ReadingCommand, ReadingInput};
pub use serve_reading::serve_reading;
