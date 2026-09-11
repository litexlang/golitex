use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult, Runtime};

impl Runtime {
    pub fn store_fact_and_well_definedness_then_infer(
        &mut self,
        _verify_result: (),
    ) -> RuntimeResult<()> {
        let _ = self;
        Err(RuntimeError::Unsupported(
            "store_fact_and_well_definedness_then_infer is not wired yet".to_string(),
        ))
    }
}
