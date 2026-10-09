use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn cited_fact_reference<'p>(
        &'p self,
        id: FactId,
        position: &SourcePosition<'p>,
    ) -> Result<(&'p Fact, String), LeanCompileError> {
        position.visible_fact(id, &self.runtime)
    }

    pub(in crate::compile_to_lean) fn resolve_fact(
        &self,
        id: FactId,
        position: &SourcePosition<'_>,
    ) -> Result<Fact, LeanCompileError> {
        position.source_fact(id, &self.runtime).cloned()
    }

    pub(in crate::compile_to_lean) fn resolve_wd(
        &self,
        id: WellDefinednessId,
        position: &SourcePosition<'_>,
    ) -> Result<Obj, LeanCompileError> {
        position.source_wd(id, &self.runtime).cloned()
    }
}
