//! Project a prefix only from a completed, fully checked original call node.
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_checked_call_prefix(
        &self,
        requested: &Obj,
        original: &ObjWellDefinedProof,
        producer: &SourcePosition<'_>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::FnObj(prefix),
            DetailedObjWellDefinedProof::ByDef {
                obj: Obj::FnObj(whole),
                proof: ObjWellDefinedProofByDef::FnObj(evidence),
            },
        ) = (requested, original.detailed_ref())
        else {
            return Err(LeanCompileError::unsupported(
                "CallPrefix/OriginalConstructor",
            ));
        };
        if prefix.body.is_empty() || prefix.body.len() >= whole.body.len() {
            return Err(LeanCompileError::unsupported("CallPrefix/ProperPrefix"));
        }
        let mut retained = whole.clone();
        retained.body.truncate(prefix.body.len());
        if retained.ir() != prefix.ir() {
            return Err(LeanCompileError::unsupported("CallPrefix/OriginalSubject"));
        }
        let scope = SourcePosition::new(Some(producer), SourceOwner::WD(original), 0);
        let mut call = match position
            .bound_wd_child(original)
            .or_else(|| producer.bound_wd_child(original))
        {
            Some(call) => call,
            None => self.compile_fn_obj_wd(whole, evidence, &scope)?,
        };
        for _ in prefix.body.len()..whole.body.len() {
            // The original constructor may itself be a tactic term. Give it
            // its checked call shape before projecting, so Lean can infer the
            // original host types without a new prefix WD result.
            call = format!("((fun (_litex_prefix_whole : Litex.Obj (M := M) (Litex.CallOnObj (M := M) _ _)) => _litex_prefix_whole.val.function) {call})");
        }
        Ok(call)
    }
}
