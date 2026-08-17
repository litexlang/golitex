use crate::compile_to_lean::capture_litex_to_lean_ir_from_source;

pub fn compile_source(source: &str, source_label: &str) -> Result<String, String> {
    let ir = capture_litex_to_lean_ir_from_source(source, source_label)
        .map_err(|error| format!("Litex verification/IR capture failed: {error:?}"))?;
    super::emitter::emit_file(&ir, source_label)
}
