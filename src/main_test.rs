// cargo test run_examples -- --nocapture
// cargo test run_docs_markdown_files -- --nocapture
// cargo test run_mechanics_textbook_chapters -- --nocapture
// cargo test run_analysis_one_chapters -- --nocapture
// cargo test run_linear_algebra_done_right -- --nocapture
// cargo test run_number_theory_for_beginners -- --nocapture
// cargo test run_minif2f_litex_finished -- --nocapture
// cargo test run_math500_litex_finished -- --nocapture
// Fast aggregate (examples + docs only): cargo test run_all -- --nocapture
// Full aggregate (examples + docs + runtime contracts + textbooks):
// cargo test run_all_docs_examples_textbooks -- --ignored --nocapture

#[cfg(test)]
mod lit_file_runner_tests;
