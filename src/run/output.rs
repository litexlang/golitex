//! CLI stdout writes with explicit I/O handling.

use crate::runtime::{RuntimeError, RuntimeResult};
use std::fmt::Arguments;
use std::io::{self, Write};
use std::path::PathBuf;

/// A closed downstream reader discards output without changing verification's
/// exit status. Other output errors remain ordinary runtime I/O errors.
pub fn write_stdout(text: Arguments<'_>) -> RuntimeResult<()> {
    let mut stdout = io::stdout().lock();
    match stdout.write_fmt(text).and_then(|_| stdout.flush()) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(()),
        Err(error) => Err(RuntimeError::Io {
            path: PathBuf::from("<stdout>"),
            message: error.to_string(),
        }),
    }
}
