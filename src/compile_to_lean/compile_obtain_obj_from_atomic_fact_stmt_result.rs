use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecObtainObjFromAtomicFactStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_obtain_atomic_statement(
        &self,
        result: &ExecObtainObjFromAtomicFactStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecObtainObjFromAtomicFactStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ObtainAtomic/Failed"));
        };
        let expected = Fact::AtomicFact(AtomicFact::NormalAtomicFact(proof.statement.fact.clone()));
        if verified_subject(&proof.verify_atomic).as_ref() != Some(&expected) {
            return Err(LeanCompileError::unsupported("ObtainAtomic/SourceSubject"));
        }
        let (declaration, parent, _) = position.visible_prop(&proof.statement.fact.predicate)?;
        let (source, formation) = match (
            declaration.statement.iff_facts.as_slice(),
            declaration.assumed_iff_facts.as_slice(),
        ) {
            ([Fact::ExistFact(source)], [captured]) => match &captured.well_defined {
                FactWellDefinedProof::ExistFact(formation) => (source, formation),
                _ => return Err(LeanCompileError::unsupported("ObtainAtomic/Formation")),
            },
            _ => return Err(LeanCompileError::unsupported("ObtainAtomic/Definition")),
        };
        let substitution = self.prop_argument_substitution(declaration, &proof.statement.fact)?;
        if !matches!(&proof.projected_exist, ExistShapedFact::Exist(projected) if instantiated_fact_matches(
            &Fact::ExistFact(source.clone()), &Fact::ExistFact(projected.clone()), &substitution))
        {
            return Err(LeanCompileError::unsupported(
                "ObtainAtomic/ProjectionSubject",
            ));
        }
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let (_, mut tail) = self.compile_verify(&proof.verify_atomic, &prior)?;
        for _ in declaration.statement.typed_parameters.ordered_param_ids() {
            tail = format!("(Classical.choose_spec ({tail}))");
        }
        let original = SourcePosition::new(
            Some(&parent),
            SourceOwner::PropDefinition(declaration),
            declaration
                .statement
                .typed_parameters
                .ordered_param_ids()
                .len(),
        );
        self.compile_obtain_elimination(
            source,
            formation,
            &proof.statement.equal_tos,
            &proof.store_and_infer_result,
            &substitution,
            tail,
            &original,
            position,
            local,
        )
    }
}
