#[cfg(test)]
mod lit_file_runner_tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::Instant;

    use crate::pipeline::run_source_code_in_file_with_ok;

    #[test]
    fn run_tmp() {
        let tmp_lit_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("tmp.lit");

        assert!(
            tmp_lit_path.is_file(),
            "examples/tmp.lit must exist at {:?}",
            tmp_lit_path
        );

        let tmp_lit_content = match fs::read_to_string(&tmp_lit_path) {
            Ok(content) => content,
            Err(read_error) => panic!("failed to read {:?}: {}", tmp_lit_path, read_error),
        };
        if tmp_lit_content.trim().is_empty() {
            println!("examples/tmp.lit is empty; skip run_tmp");
            return;
        }

        let path_str = match tmp_lit_path.to_str() {
            Some(path_string) => path_string,
            None => panic!("{:?} must be valid UTF-8", tmp_lit_path),
        };

        let start_time = Instant::now();
        let (run_succeeded, run_output) = run_source_code_in_file_with_ok(path_str);
        let duration_ms = start_time.elapsed().as_secs_f64() * 1000.0;

        let status_label = if run_succeeded { "OK" } else { "FAILED" };
        println!(
            "\n=== [{}] {:?} ({:.2} ms) ===\n{}\n",
            status_label, tmp_lit_path, duration_ms, run_output
        );
    }

    #[test]
    fn run_examples() {
        let examples_directory_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/test_codes");

        let read_directory = match fs::read_dir(&examples_directory_path) {
            Ok(entries) => entries,
            Err(read_error) => panic!(
                "failed to read {:?}: {}",
                examples_directory_path, read_error
            ),
        };

        let mut lit_file_paths: Vec<PathBuf> = Vec::new();
        for directory_entry_result in read_directory {
            let directory_entry = match directory_entry_result {
                Ok(entry) => entry,
                Err(read_error) => panic!("failed to read directory entry: {}", read_error),
            };
            let lit_file_path = directory_entry.path();
            if !lit_file_path.is_file() {
                continue;
            }
            let extension_is_lit = match lit_file_path.extension() {
                Some(ext) => ext == "lit",
                None => false,
            };
            if extension_is_lit {
                lit_file_paths.push(lit_file_path);
            }
        }
        lit_file_paths.sort();

        let mut file_name_and_duration_ms_list: Vec<(String, f64)> = Vec::new();
        let mut every_file_run_ok = true;

        for lit_file_path in lit_file_paths.iter() {
            let lit_file_path_str = match lit_file_path.to_str() {
                Some(path_string) => path_string,
                None => panic!("{:?} must be valid UTF-8", lit_file_path),
            };

            let file_label_for_report = match lit_file_path.file_name() {
                Some(os_file_name) => match os_file_name.to_str() {
                    Some(name_string) => String::from(name_string),
                    None => format!("{:?}", lit_file_path),
                },
                None => format!("{:?}", lit_file_path),
            };

            let start_time_for_one_file = Instant::now();
            let (run_succeeded, run_output) = run_source_code_in_file_with_ok(lit_file_path_str);
            let duration_for_one_file = start_time_for_one_file.elapsed();
            let duration_ms_for_one_file = duration_for_one_file.as_secs_f64() * 1000.0;

            if !run_succeeded {
                every_file_run_ok = false;
                println!(
                    "=== [{}] {:?} ===\n{}\n",
                    "FAILED", lit_file_path, run_output
                );
                break;
            }

            file_name_and_duration_ms_list.push((file_label_for_report, duration_ms_for_one_file));
        }

        if !every_file_run_ok {
            return;
        }

        let number_of_lit_files = file_name_and_duration_ms_list.len();

        println!(
            "--- examples folder: {} .lit files, all OK, timing ---",
            number_of_lit_files
        );
        let mut sum_of_per_file_duration_ms: f64 = 0.0;
        for (file_name, duration_ms) in file_name_and_duration_ms_list.iter() {
            println!("  {}  {:.2} ms", file_name, duration_ms);
            sum_of_per_file_duration_ms += duration_ms;
        }
        println!(
            "  sum of per-file runs: {:.2} ms",
            sum_of_per_file_duration_ms
        );
    }
}
