pub(super) fn print_help_message() {
    println!("{}", help_message());
}

pub(super) fn help_message() -> String {
    let result = r#"litex : start an isolated persistent REPL; terminal import is available
litex -f <file> : require a direct-parent litex.config and run the module prefix through this file
litex -isolated -f <file> : run any standalone file and continue in an isolated REPL
litex -r <folder> : run a module's recursive [export] tree, or the root prefix through a selected submodule
litex -e <code> : execute the given code
litex -session : run a machine-readable project REPL for framed code blocks
litex -session -f <file> : load the project prefix through a registered file, then keep the same Runtime in session mode
litex -isolated -session -f <file> : load one standalone file, then keep the same Runtime in session mode
litex -f <input.lit> -isolated -lean <output.lean> : verify every statement in one standalone file, then compile the complete result to Lean
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
litex -extractpython <code> : verify inline Litex and extract the supported program subset as Python
litex -extractpython -f <file> : verify a file and extract the supported program subset as Python
litex -extractpython -r <project> : verify a recursive project and extract the supported program subset as Python
litex -extractc <code> : verify inline Litex and extract the supported program subset as C99
litex -extractc -f <file> : verify a file and extract the supported program subset as C99
litex -extractc -r <project> : verify a recursive project and extract the supported program subset as C99
litex -help : show the help message
litex -version : show the version
litex -compact : show minimal success output; RuntimeError output always uses full detailed diagnostics
litex : show normal success output with internal statements and direct verification reasons; RuntimeError output is detailed
litex -detail : include full audit trace details and raw source paths for both success and RuntimeError JSON output
litex -strict : verify configured imports and -f prefix entries, and reject user trust, trust have, and axiom statements
litex -summarize : append one run summary JSON object after ordinary verifier command output
litex -lang <en|zh|zh-Hans|zh-Hant|ja|ko|es|fr|de|pt|ru|ar|hi|vi|id> : choose output language
"#;
    result.to_string()
}
