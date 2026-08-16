// cargo test run_examples -- --nocapture
// cargo test run_examples_only -- --nocapture
// cargo test run_docs_markdown_files -- --nocapture
// cargo test run_minif2f_litex_finished -- --nocapture
// cargo test run_math500_litex_all -- --nocapture
// Full repository aggregate (examples + docs + runtime contracts):
// cargo test run_all_docs_examples_runtime_contracts -- --ignored --nocapture
// Workspace-owned textbooks: python3 scripts/textbook_gate.py
// Parallel pre-deploy docs/examples gate: python3 tools/predeploy_gate.py

#[cfg(test)]
mod lit_file_runner_tests;
