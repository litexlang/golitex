#[cfg(test)]
mod run_examples_lit {
    use std::fs;
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::pipeline::run_source_code_in_file_and_return_string;

    #[test]
    fn run_all_lit_files_under_examples_directory() {
        let examples_directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
        assert!(
            examples_directory.is_dir(),
            "examples directory must exist at {:?}",
            examples_directory
        );

        let read_directory = match fs::read_dir(&examples_directory) {
            Ok(entries) => entries,
            Err(read_error) => panic!(
                "failed to read examples directory {:?}: {}",
                examples_directory, read_error
            ),
        };

        let mut lit_file_paths: Vec<PathBuf> = Vec::new();
        for directory_entry_result in read_directory {
            let directory_entry = match directory_entry_result {
                Ok(entry) => entry,
                Err(read_error) => panic!(
                    "failed to read directory entry under {:?}: {}",
                    examples_directory, read_error
                ),
            };
            let entry_path = directory_entry.path();
            if !entry_path.is_file() {
                continue;
            }
            let extension_is_lit = match entry_path.extension() {
                Some(ext) => ext == "lit",
                None => false,
            };
            if extension_is_lit {
                lit_file_paths.push(entry_path);
            }
        }

        lit_file_paths.sort();

        if lit_file_paths.is_empty() {
            println!(
                "no .lit files under examples; skip run_all_lit_files_under_examples_directory"
            );
            return;
        }

        let start_of_whole_time = Instant::now();

        for lit_file_path in lit_file_paths.iter() {
            let lit_file_content = match fs::read_to_string(lit_file_path) {
                Ok(content) => content,
                Err(read_error) => panic!("failed to read {:?}: {}", lit_file_path, read_error),
            };
            if lit_file_content.trim().is_empty() {
                println!("{:?} is empty; skip", lit_file_path);
                continue;
            }

            let lit_file_path_str = match lit_file_path.to_str() {
                Some(path_string) => path_string,
                None => panic!("{:?} must be valid UTF-8", lit_file_path),
            };

            let start_time = Instant::now();
            let run_result_string = run_source_code_in_file_and_return_string(lit_file_path_str);
            let duration = start_time.elapsed();

            println!("\n=== {:?} ===\n{}\n", lit_file_path, run_result_string);
            println!(
                "Time {:?}: {:?} ({:.2} ms)",
                lit_file_path.file_name(),
                duration,
                duration.as_secs_f64() * 1000.0
            );
        }

        let duration = start_of_whole_time.elapsed();
        println!(
            "Total time: {:?} ({:.2} ms)",
            duration,
            duration.as_secs_f64() * 1000.0
        );
    }

    #[test]
    fn run_examples_tmp_lit() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        assert!(path.is_file(), "examples/tmp.lit must exist at {:?}", path);

        let path_str = match path.to_str() {
            Some(path_string) => path_string,
            None => panic!("examples/tmp.lit path must be valid UTF-8"),
        };

        let tmp_lit_content = match fs::read_to_string(&path) {
            Ok(content) => content,
            Err(read_error) => panic!("examples/tmp.lit must be readable: {}", read_error),
        };
        if tmp_lit_content.trim().is_empty() {
            println!("examples/tmp.lit is empty; skip run_examples_tmp_lit");
            return;
        }

        let start_time = Instant::now();
        let result_from_string = run_source_code_in_file_and_return_string(path_str);
        let duration_string = start_time.elapsed();

        println!("\n{}\n", result_from_string);
        println!(
            "Time (from_string): {:?} ({:.2} ms)",
            duration_string,
            duration_string.as_secs_f64() * 1000.0
        );
    }
}
