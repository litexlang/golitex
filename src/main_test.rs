// cargo test run_examples -- --nocapture
// cargo test run_examples_only -- --nocapture
// cargo test run_docs_markdown_files -- --nocapture
// Explicit dataset gates (ignored by default):
// cargo test --release run_gsm8k_solutions -- --ignored --nocapture
// cargo test --release run_metamathqa_litex_solutions -- --ignored --nocapture
// cargo test --release run_minif2f_litex_finished -- --ignored --nocapture
// cargo test --release run_math500_tmp -- --ignored --nocapture
// cargo test --release run_math500_litex_simple -- --ignored --nocapture
// cargo test --release run_math500_litex_all -- --ignored --nocapture
// Full repository aggregate (examples + docs + runtime contracts):
// cargo test run_all_docs_examples_runtime_contracts -- --ignored --nocapture
// Workspace-owned textbooks: python3 scripts/textbook_gate.py
// Parallel pre-deploy docs/examples gate: python3 .github/scripts/predeploy_gate.py

#[cfg(test)]
mod lit_file_runner_tests;
