use litex::litex_to_lean_compiler2::compile_source;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
    if let Err(message) = run() {
        eprintln!("compiler2: {message}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [command, input] if command == "compile" => {
            let input = Path::new(input);
            let output = paired_output_path(input)?;
            compile_file(input, &output)?;
            println!("generated {} from {}", output.display(), input.display());
            Ok(())
        }
        [command, input, output] if command == "compile" => {
            compile_file(Path::new(input), Path::new(output))?;
            println!("generated {output} from {input}");
            Ok(())
        }
        [command, directory] if command == "generate" => {
            let count = generate_directory(Path::new(directory))?;
            println!("generated {count} compiler2 example pair(s)");
            Ok(())
        }
        [command, directory] if command == "check" => {
            let count = check_directory(Path::new(directory))?;
            println!(
                "checked {count} compiler2 example pair(s): no drift and Lean kernel accepted"
            );
            Ok(())
        }
        _ => Err(
            "usage: compiler2 compile <input.lit> [output.lean] | generate <examples-dir> | check <examples-dir>"
                .to_string(),
        ),
    }
}

fn paired_output_path(input: &Path) -> Result<PathBuf, String> {
    if input.extension().is_none_or(|extension| extension != "lit") {
        return Err(format!(
            "single-file compilation expects a .lit input: {}",
            input.display()
        ));
    }
    Ok(input.with_extension("lean"))
}

fn compile_file(input: &Path, output: &Path) -> Result<(), String> {
    if input == output {
        return Err("input and output paths must differ".to_string());
    }
    let source = fs::read_to_string(input)
        .map_err(|error| format!("failed to read {}: {error}", input.display()))?;
    let label = input
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("source path has no UTF-8 file name: {}", input.display()))?;
    let generated = compile_source(&source, label)?;
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create {}: {error}", parent.display()))?;
    }
    fs::write(output, generated)
        .map_err(|error| format!("failed to write {}: {error}", output.display()))
}

fn generate_directory(directory: &Path) -> Result<usize, String> {
    let sources = example_sources(directory)?;
    for source in &sources {
        compile_file(source, &source.with_extension("lean"))?;
    }
    Ok(sources.len())
}

fn check_directory(directory: &Path) -> Result<usize, String> {
    let sources = example_sources(directory)?;
    let mut outputs = Vec::new();
    for source_path in &sources {
        let output_path = source_path.with_extension("lean");
        let source = fs::read_to_string(source_path)
            .map_err(|error| format!("failed to read {}: {error}", source_path.display()))?;
        let label = source_path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid source name: {}", source_path.display()))?;
        let generated = compile_source(&source, label)?;
        let checked_in = fs::read_to_string(&output_path).map_err(|error| {
            format!(
                "missing generated pair {} for {}: {error}",
                output_path.display(),
                source_path.display()
            )
        })?;
        if generated != checked_in {
            return Err(format!(
                "generated Lean drifted for {}; run `./compiler2.sh generate examples`",
                source_path.display()
            ));
        }
        outputs.push(output_path);
    }
    for output in &outputs {
        check_with_lean(output)?;
    }
    Ok(sources.len())
}

fn check_with_lean(output: &Path) -> Result<(), String> {
    let lean_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("lean");
    let output = output
        .canonicalize()
        .map_err(|error| format!("failed to resolve {}: {error}", output.display()))?;
    let result = Command::new("lake")
        .current_dir(&lean_root)
        .args(["env", "lean"])
        .arg(&output)
        .output()
        .map_err(|error| format!("failed to start Lean for {}: {error}", output.display()))?;
    if result.status.success() {
        return Ok(());
    }
    Err(format!(
        "Lean rejected {}:\n{}{}",
        output.display(),
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    ))
}

fn example_sources(directory: &Path) -> Result<Vec<PathBuf>, String> {
    let mut sources = fs::read_dir(directory)
        .map_err(|error| format!("failed to read {}: {error}", directory.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "lit"))
        .collect::<Vec<_>>();
    sources.sort();
    if sources.is_empty() {
        return Err(format!("no .lit examples found in {}", directory.display()));
    }
    Ok(sources)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paired_output_replaces_lit_extension() {
        assert_eq!(
            paired_output_path(Path::new("examples/1_SetSystem.lit")).unwrap(),
            PathBuf::from("examples/1_SetSystem.lean")
        );
    }

    #[test]
    fn paired_output_rejects_non_lit_input() {
        let error = paired_output_path(Path::new("examples/1_SetSystem.lean")).unwrap_err();
        assert!(error.contains("expects a .lit input"));
    }
}
