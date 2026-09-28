use super::super::source_extraction::{
    extract_code, extract_code_from_file, extract_code_from_repository, extract_code_from_source,
    CodeExtractionTarget,
};
use crate::prelude::*;

pub fn to_python(source_code: &str, runtime: &mut Runtime) -> Result<String, RuntimeError> {
    extract_code(source_code, runtime, CodeExtractionTarget::Python)
}

pub fn to_python_from_source(
    source_code: &str,
    source_label: &str,
) -> Result<String, RuntimeError> {
    extract_code_from_source(source_code, source_label, CodeExtractionTarget::Python)
}

pub fn to_python_from_file(file_path: &str) -> Result<String, RuntimeError> {
    extract_code_from_file(file_path, CodeExtractionTarget::Python)
}

pub fn to_python_from_repository(repository_path: &str) -> Result<String, RuntimeError> {
    extract_code_from_repository(repository_path, CodeExtractionTarget::Python)
}
