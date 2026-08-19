use super::CompilationReport;
use crate::litex_to_lean_ir::capture_litex_to_lean_ir_from_source;

pub fn compile_source(source: &str, source_label: &str) -> Result<String, String> {
    let ir = capture_litex_to_lean_ir_from_source(source, source_label)
        .map_err(|error| format!("Litex verification/IR capture failed: {error:?}"))?;
    super::emitter::emit_file(&ir, source_label)
}

pub fn compile_source_with_report(
    source: &str,
    source_label: &str,
) -> Result<CompilationReport, String> {
    let ir = capture_litex_to_lean_ir_from_source(source, source_label)
        .map_err(|error| format!("Litex verification/IR capture failed: {error:?}"))?;
    Ok(match super::emitter::emit_file(&ir, source_label) {
        Ok(lean_code) => CompilationReport::complete(lean_code),
        Err(reason) => CompilationReport::incomplete_emission(source_label, reason),
    })
}
