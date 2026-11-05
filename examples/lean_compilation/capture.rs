//! Capture the inspected result and generated proof from one completed run.
use litex::compile_to_lean::LitexToLeanCompiler;
use litex::launch_command::parse_launch_command;
use litex::result_detail::OutputDetail;
use litex::runtime::Runtime;
use std::{env, fs, path::Path};

fn main() {
    let args: Vec<String> = env::args().collect();
    let source = fs::read_to_string(&args[1]).expect("read source");
    let command = parse_launch_command(&[
        "-strict".into(),
        "-lean".into(),
        "-f".into(),
        args[1].clone(),
    ])
    .expect("parse capture command");
    let mut runtime = Runtime::new_with_result_detail(command, OutputDetail::Detailed);
    let result = runtime.run_litex_code(&source).expect("run source");
    assert!(result.success, "source verification failed");
    let detailed =
        litex::json_output::emit_run_detailed(&result, &runtime, "file", Some(Path::new(&args[1])));
    let compiler = LitexToLeanCompiler::new(runtime);
    let generated = compiler
        .compile_run(&result, &args[2])
        .expect("compile same result");
    let output = Path::new(&args[3]);
    fs::write(output.join("detailed.json"), detailed).expect("write detail");
    fs::write(output.join("generated.lean"), generated).expect("write generated proof");
}
