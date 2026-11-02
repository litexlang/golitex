use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_finite_subset_theorem(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        if builtin.theorem != BuiltinTheoremId::SubsetOfFiniteSetIsFinite
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(LeanCompileError::unsupported(
                "FiniteSubset/TheoremContract",
            ));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(LeanCompileError::unsupported("FiniteSubset/Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != 2
            || builtin.requirements.len() != 3
            || dom_proofs.len() != 3
            || dom_stores.len() != 3
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(LeanCompileError::unsupported("FiniteSubset/Stages"));
        }
        let (a, b) = (&arguments[0], &arguments[1]);
        if !matches!(&builtin.requirements[0],Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==a.ir())
            || !matches!(&builtin.requirements[1],Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir()==b.ir())
            || !matches!(&builtin.requirements[2],Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir()==a.ir() && f.right.ir()==b.ir())
            || !matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir()==a.ir())
        {
            return Err(LeanCompileError::unsupported("FiniteSubset/Subjects"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(LeanCompileError::unsupported("FiniteSubset/PremiseCapture"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: 3,
            ..*position
        };
        let fact = &builtin.conclusions[0];
        self.compile_fact_wd(&conclusions_wd[0], fact, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], fact, &formed)?;
        let a = self.compile_object_reference(a, &scope)?;
        let b = self.compile_object_reference(b, &scope)?;
        let application = format!(
            "(show {statement} from Litex.finiteSubsetOfFinite {a} {b} h_{} h_{})",
            builtin.requirements[1].fact_id().value(),
            builtin.requirements[2].fact_id().value()
        );
        Ok((definitions, application, builtin.conclusions.clone()))
    }
}
