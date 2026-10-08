//! Turn verified Litex computational fragments into Python / C.

mod c;
mod program;
mod python;
mod source_extraction;

pub use crate::launch_command::CodeExtractionTarget;
pub use c::{to_c, to_c_from_file, to_c_from_repository, to_c_from_source};
pub use python::{
    to_python, to_python_from_file, to_python_from_repository, to_python_from_source,
};
pub use source_extraction::{
    extract_code_from_file, extract_code_from_repository, extract_code_from_source,
};
