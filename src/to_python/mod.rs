// Frozen experiment: preserve the documented v1 subset and compatibility, but
// do not expand the extractor without an explicit decision to resume it.
mod to_python_pipeline;

pub use to_python_pipeline::{
    to_python, to_python_from_file, to_python_from_repository, to_python_from_source,
};
