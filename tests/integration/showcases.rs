use std::collections::VecDeque;
use std::ffi::OsStr;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::time::Instant;

const SHOWCASES_SUBDIR: &str = "showcases/math_concepts_in_litex";
const SHOWCASE_WORKERS: usize = 4;

struct ShowcaseResult {
    label: String,
    duration_ms: f64,
    succeeded: bool,
    output: String,
}

#[test]
fn run_showcases() {
    let repository_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut showcase_files = collect_showcase_files(&repository_root);
    assert!(
        !showcase_files.is_empty(),
        "no published showcase .lit files found under {}",
        SHOWCASES_SUBDIR
    );

    showcase_files.sort_by_key(|path| {
        std::cmp::Reverse(path.metadata().map(|metadata| metadata.len()).unwrap_or(0))
    });
    let worker_count = SHOWCASE_WORKERS.min(showcase_files.len());
    println!(
        "--- showcases: verifying {} published .lit file(s) with {} worker(s) ---",
        showcase_files.len(),
        worker_count
    );

    let wall_start = Instant::now();
    let pending = Arc::new(Mutex::new(VecDeque::from(showcase_files)));
    let mut handles = Vec::new();
    for worker_index in 0..worker_count {
        let worker_pending = Arc::clone(&pending);
        let worker_repository_root = repository_root.clone();
        handles.push(
            std::thread::Builder::new()
                .name(format!("run_showcases_worker_{worker_index}"))
                .spawn(move || run_showcase_worker(worker_repository_root, worker_pending))
                .expect("spawn showcase worker"),
        );
    }

    let mut results = Vec::new();
    for handle in handles {
        results.extend(handle.join().expect("showcase worker panicked"));
    }
    results.sort_by(|left, right| left.label.cmp(&right.label));

    let mut durations_ms = Vec::new();
    let mut failed_files = Vec::new();
    for result in results {
        durations_ms.push((result.label.clone(), result.duration_ms));
        if result.succeeded {
            println!("  OK  {:.2} ms  {}", result.duration_ms, result.label);
        } else {
            println!(
                "=== [FAILED] {} ({:.2} ms) ===\n{}\n>>> FAILED showcase file: {}\n",
                result.label,
                result.duration_ms,
                concise_failure_output(result.output.as_str()),
                result.label
            );
            failed_files.push(result.label);
        }
    }

    print_slowest_runs(durations_ms.as_slice());
    println!(
        "--- showcases: {} run(s), {} failure(s), wall {:.2} ms ---",
        durations_ms.len(),
        failed_files.len(),
        wall_start.elapsed().as_secs_f64() * 1000.0
    );
    assert!(
        failed_files.is_empty(),
        "showcase verification failed: {}",
        failed_files.join(", ")
    );
}

#[test]
fn run_showcases_excludes_draft_paths() {
    assert!(is_draft_path(Path::new(
        "showcases/math_concepts_in_litex/topic/.draft/work.lit"
    )));
    assert!(is_draft_path(Path::new(
        "showcases/math_concepts_in_litex/topic/.drafts/work.lit"
    )));
    assert!(!is_draft_path(Path::new(
        "showcases/math_concepts_in_litex/topic/main.lit"
    )));
}

fn collect_showcase_files(repository_root: &Path) -> Vec<PathBuf> {
    let showcase_root = repository_root.join(SHOWCASES_SUBDIR);
    let mut pending = vec![showcase_root];
    let mut files = Vec::new();
    while let Some(directory) = pending.pop() {
        let entries = fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", directory.display()));
        for entry in entries {
            let entry = entry.expect("read showcase directory entry");
            let path = entry.path();
            if path.is_dir() {
                if !is_draft_path(&path) {
                    pending.push(path);
                }
            } else if path.extension().is_some_and(|extension| extension == "lit") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

fn run_showcase_worker(
    repository_root: PathBuf,
    pending: Arc<Mutex<VecDeque<PathBuf>>>,
) -> Vec<ShowcaseResult> {
    let mut results = Vec::new();
    loop {
        let showcase_file = pending.lock().unwrap().pop_front();
        let Some(showcase_file) = showcase_file else {
            break;
        };
        let label = showcase_file
            .strip_prefix(&repository_root)
            .unwrap_or(&showcase_file)
            .display()
            .to_string();
        let start = Instant::now();
        let output = Command::new(litex_binary())
            .args([
                "-compact",
                "-runner",
                "-f",
                showcase_file
                    .to_str()
                    .unwrap_or_else(|| panic!("showcase path must be UTF-8: {showcase_file:?}")),
            ])
            .current_dir(&repository_root)
            .output()
            .unwrap_or_else(|error| panic!("failed to run showcase {label}: {error}"));
        let stdout = String::from_utf8_lossy(&output.stdout);
        let succeeded = output.status.success()
            && stdout.contains("\"runner\": \"litex-runner\"")
            && stdout.contains("\"result\": \"success\"")
            && stdout.contains("\"ok\": true");
        let combined_output = if succeeded {
            String::new()
        } else {
            format!(
                "exit: {:?}\nstdout:\n{}\nstderr:\n{}",
                output.status.code(),
                stdout,
                String::from_utf8_lossy(&output.stderr)
            )
        };
        results.push(ShowcaseResult {
            label,
            duration_ms: start.elapsed().as_secs_f64() * 1000.0,
            succeeded,
            output: combined_output,
        });
    }
    results
}

fn is_draft_path(path: &Path) -> bool {
    path.components().any(|component| {
        matches!(
            component,
            Component::Normal(name)
                if name == OsStr::new(".draft") || name == OsStr::new(".drafts")
        )
    })
}

fn litex_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_litex") {
        return PathBuf::from(path);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/litex")
}

fn concise_failure_output(output: &str) -> String {
    const HEAD_CHARS: usize = 16_000;
    const TAIL_CHARS: usize = 4_000;

    if output.chars().count() <= HEAD_CHARS + TAIL_CHARS {
        return output.to_string();
    }
    let head = output.chars().take(HEAD_CHARS).collect::<String>();
    let tail = output
        .chars()
        .rev()
        .take(TAIL_CHARS)
        .collect::<String>()
        .chars()
        .rev()
        .collect::<String>();
    format!("{}\n... failure output truncated ...\n{}", head, tail)
}

fn print_slowest_runs(durations_ms: &[(String, f64)]) {
    let mut sorted = durations_ms.to_vec();
    sorted.sort_by(|left, right| {
        right
            .1
            .partial_cmp(&left.1)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    println!("--- slowest showcase runs: top 10 of {} ---", sorted.len());
    for (index, (label, duration_ms)) in sorted.iter().take(10).enumerate() {
        println!("  {:>2}. {:.2} ms  {}", index + 1, duration_ms, label);
    }
}
