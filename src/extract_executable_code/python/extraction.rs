use super::super::source_extraction::{
    extract_code, extract_code_from_file, extract_code_from_repository, extract_code_from_source,
};
use crate::launch_command::CodeExtractionTarget;
use crate::runtime::{Runtime, RuntimeResult};

pub fn to_python(source_code: &str, runtime: &mut Runtime) -> RuntimeResult<String> {
    extract_code(source_code, runtime, CodeExtractionTarget::Python)
}

pub fn to_python_from_source(source_code: &str) -> RuntimeResult<String> {
    extract_code_from_source(source_code, CodeExtractionTarget::Python)
}

pub fn to_python_from_file(file_path: &str) -> RuntimeResult<String> {
    extract_code_from_file(file_path, CodeExtractionTarget::Python)
}

pub fn to_python_from_repository(repository_path: &str) -> RuntimeResult<String> {
    extract_code_from_repository(repository_path, CodeExtractionTarget::Python)
}
