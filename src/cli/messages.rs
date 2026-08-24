pub(super) fn print_help_message() {
    println!("{}", help_message());
}

/// Print instructions instead of running a package manager.
/// Litex can be installed by Homebrew, release packages, or source builds, so
/// startup should not perform network or system changes on the user's machine.
pub(super) fn upgrade_message(version: &str) -> String {
    let mut result = format!("Litex version {}\n\nUpgrade Litex:\n", version);

    if cfg!(target_os = "macos") {
        result.push_str("macOS with Homebrew:\n");
        result.push_str("  brew update\n");
        result.push_str("  brew upgrade litexlang/tap/litex\n\n");
    } else if cfg!(target_os = "linux") {
        result.push_str("Linux with the .deb release package:\n");
        result.push_str(
            "  Download the latest litex_<tag>_amd64.deb from GitHub Releases and run:\n",
        );
        result.push_str("  sudo dpkg -i litex_<tag>_amd64.deb\n\n");
    } else if cfg!(target_os = "windows") {
        result.push_str("Windows release zip install:\n");
        result.push_str("  Rerun the PowerShell install command from docs/Setup.md.\n\n");
    } else {
        result.push_str("Open the latest GitHub Release and install the package for your OS.\n\n");
    }

    result.push_str("Release page: https://github.com/litexlang/golitex/releases/latest\n");
    result.push_str("Full setup notes: https://litexlang.com/doc/Setup");
    result
}

pub(super) fn help_message() -> String {
    let result = r#"litex : start an isolated persistent REPL; terminal import is available
litex -f <file> : require a direct-parent litex.config and run the module prefix through this file
litex -isolated -f <file> : run any standalone file and continue in an isolated REPL
litex -f <file> -trust-before-line <X> : trust top-level statements before the exact header line X, then verify from X
litex -r <folder> : run a module's recursive [export] tree, or the root prefix through a selected submodule
litex -e <code> : execute the given code
litex -runner -f <file> : run a file and return one wrapper JSON object
litex -runner -e <code> : run source code and return one wrapper JSON object
litex -runner -r <project> : run a project and return one wrapper JSON object
litex -session : run a machine-readable project REPL for framed code blocks
litex -session -f <file> : load the project prefix through a registered file, then keep the same Runtime in session mode
litex -session -before <file> : load the registered project prefix before a file, then edit in that file's Runtime context
litex -f <input.lit> -isolated -lean <output.lean> : verify every statement in one standalone file, then compile the complete result to Lean
litex -lean-ledger <markdown> <output.lean> : freshly compile every H2 Litex fence into one namespaced Lean file
litex -graph -f <file> <json> : run a file and save a recursive result/proof/FactId graph JSON object
litex -graph -e <code> <json> : run source code and save a recursive result/proof/FactId graph JSON object
litex -graph -r <project> <json> : run a project and save a recursive result/proof/FactId graph JSON object
litex -factgraph -f <file> <json> : run a file and save a fact-only verification dependency graph JSON object
litex -factgraph -e <code> <json> : run source code and save a fact-only verification dependency graph JSON object
litex -factgraph -r <project> <json> : run a project and save a fact-only verification dependency graph JSON object
litex -defgraph -f <file> <json> : run a file and save an environment-backed definition dependency graph JSON object
litex -defgraph -e <code> <json> : run source code and save an environment-backed definition dependency graph JSON object
litex -defgraph -r <project> <json> : run a project and save an environment-backed definition dependency graph JSON object
litex -latex : run Litex interactively and print LaTeX output in your terminal
litex -latex -f <file> : compile the given file to LaTeX
litex -latex -e <code> : compile the given code to LaTeX
litex -latex -r <project> : compile the given project to LaTeX
litex -python -f <file> : run the frozen experimental Python extractor on a file
litex -python -e <code> : run the frozen experimental Python extractor on source code
litex -python -r <project> : run the frozen experimental Python extractor on a recursive project
litex -help : show the help message
litex -version : show the version
litex -upgrade : show upgrade instructions for this platform
litex -compact : show minimal success output; RuntimeError output always uses full detailed diagnostics
litex : show normal success output with internal statements and direct verification reasons; RuntimeError output is detailed
litex -detail : include full audit trace details and raw source paths for both success and RuntimeError JSON output
litex -strict : verify configured imports and -f prefix entries, and reject user trust, trust have, and axiom statements
litex -trust-before-line <X> : preview development tool for direct -f runs; X must name an exact top-level statement header line, cannot be used with -strict, and an isolated cutoff run exits after its summary
litex -summarize : append one run summary JSON object after ordinary verifier command output
litex -lang <en|zh|zh-Hans|zh-Hant|ja|ko|es|fr|de|pt|ru|ar|hi|vi|id> : choose output language
"#;
    result.to_string()
}
