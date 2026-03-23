mod pipeline;

pub use pipeline::{
    run_repl_loop, run_repl_loop_json, run_source_code, run_source_code_from_string,
    run_source_code_from_string_json, run_source_code_in_file, run_source_code_in_file_json,
    run_source_code_json,
};
