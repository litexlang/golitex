use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};

impl Runtime {
    pub fn store_fact_and_well_definedness_then_infer(
        &mut self,
        _verify_result: (),
    ) -> PipelineResult<()> {
        let _ = self;
        Err(PipelineError::Unsupported(
            "store_fact_and_well_definedness_then_infer is not wired yet".to_string(),
        ))
    }
}
