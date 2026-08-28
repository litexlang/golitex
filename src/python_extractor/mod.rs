// Frozen experiment: preserve the documented v1 subset and compatibility, but
// do not expand the extractor without an explicit decision to resume it.
mod extraction;

pub use extraction::{
    to_python, to_python_from_file, to_python_from_repository, to_python_from_source,
};
