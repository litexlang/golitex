use crate::compile_to_lean::helper::{ensure_object, source_subject};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    ExecReleaseRegularityAxiomStmtResult, ExecReleaseRegularityAxiomStmtSuccess,
};
use crate::prelude::*;

pub(super) fn regularity_statement(
    statement: &ExecStmtResult,
) -> Option<&ExecReleaseRegularityAxiomStmtSuccess> {
    match statement {
        ExecStmtResult::ReleaseAndExpand(
            crate::execute::ExecReleaseAndExpandStmtResult::RegularityAxiom(
                ExecReleaseRegularityAxiomStmtResult::Success(p),
            ),
        ) => Some(p),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_regularity(
        &self,
        result: &ExecReleaseRegularityAxiomStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseRegularityAxiomStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("Regularity/Failed"));
        };
        let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) =
            source_subject(&p.nonempty)?
        else {
            return Err(LeanCompileError::unsupported("Regularity/NonemptySubject"));
        };
        let VerifyObjWellDefinedResult::Success(wd) = &p.set_wd else {
            return Err(LeanCompileError::unsupported("Regularity/SetWD"));
        };
        ensure_object(&nonempty.set, wd)?;
        let set = self.compile_wd(wd, position)?;
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let nonempty_proof = self.compile_verify(&p.nonempty, &formed)?;
        let source = match &p.stored.store {
            StoreFactResult::ExistShapedFact(s) => match &s.fact {
                ExistShapedFact::Exist(fact) => Fact::ExistFact(fact.clone()),
                _ => return Err(LeanCompileError::unsupported("Regularity/Conclusion")),
            },
            _ => return Err(LeanCompileError::unsupported("Regularity/Conclusion")),
        };
        let Fact::ExistFact(fact) = &source else {
            unreachable!()
        };
        let [group] = fact.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Regularity/Binder"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Regularity/Binder"));
        };
        let [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq))] = fact.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Regularity/Conclusion"));
        };
        let element = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        if !matches!(&group.param_type, ParamType::Obj(a) if a.ir() == nonempty.set.ir())
            || !matches!(&eq.left, Obj::SetOperator(SetOperator::Intersect(p))
                if p.left.ir() == element.ir() && p.right.ir() == nonempty.set.ir())
            || !matches!(&eq.right, Obj::SetFormer(SetFormer::ListSet(p)) if p.list.is_empty())
        {
            return Err(LeanCompileError::unsupported(
                "Regularity/ConclusionSubject",
            ));
        }
        self.validate_store(&p.stored.store, &source)?;
        let before_store = SourcePosition {
            before: 2,
            ..*position
        };
        let proposition =
            self.compile_formed_fact_proposition(&p.stored_wd, &source, &before_store)?;
        let compiled = (
            proposition,
            format!("(Litex.regularity {set} {})", nonempty_proof.1),
        );
        let mut declarations =
            vec![self.emit_fact(&source, compiled.clone(), index, local, &before_store)?];
        let published = SourcePosition {
            before: 4,
            ..*position
        };
        let name = format!("h_{}", source.fact_id().value());
        let reference = if local {
            name
        } else {
            self.context_application(&name, &published)
        };
        declarations.extend(self.compile_stored_inferences(
            &p.stored,
            &source,
            &(compiled.0, reference),
            &published,
        )?);
        Ok(declarations.join("\n\n"))
    }
}
