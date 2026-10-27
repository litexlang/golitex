//! Replay completeness and selection with the exact ordered theorem premises.
use super::compile_real_extrema::{
    certificate_matches, is_real_subset, validate_extremum_existence,
};
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
    pub(super) fn compile_builtin_extremum_theorem(
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
        use BuiltinTheoremId::*;
        let (name, title, exists) = match builtin.theorem {
            RealSupremumExists => ("supremum", "Supremum", true),
            RealInfimumExists => ("infimum", "Infimum", true),
            RealSupremumSelected => ("supremum", "Supremum", false),
            RealInfimumSelected => ("infimum", "Infimum", false),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if exists { 3 } else { 2 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || arguments != &builtin.arguments
            || arguments.len() != 1
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let set = &arguments[0];
        if !is_real_subset(&builtin.requirements[0], set) {
            return Err(invalid("RealCarrier"));
        }
        if exists {
            if !matches!(&builtin.requirements[1],Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==set.ir())
                || !matches!(&builtin.requirements[2],Fact::AtomicFact(AtomicFact::RealSetBoundedFact(f)) if f.set.ir()==set.ir() && f.boundedness == if name=="supremum" { RealBoundedness::Above } else { RealBoundedness::Below })
            {
                return Err(invalid("ExistencePremises"));
            }
            validate_extremum_existence(&builtin.conclusions[0], name, set)?;
        } else {
            validate_extremum_existence(&builtin.requirements[1], name, set)?;
            let Fact::AtomicFact(AtomicFact::NormalAtomicFact(c)) = &builtin.conclusions[0] else {
                return Err(invalid("SelectedConclusion"));
            };
            if !certificate_matches(c, name, set)
                || !match &c.body[1] {
                    Obj::BoundOperator(BoundOperator::Supremum(a)) => {
                        name == "supremum" && a.set.ir() == set.ir()
                    }
                    Obj::BoundOperator(BoundOperator::Infimum(a)) => {
                        name == "infimum" && a.set.ir() == set.ir()
                    }
                    _ => false,
                }
            {
                return Err(invalid("SelectedObject"));
            }
        }
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((requirement, proof), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(proof)? != *requirement {
                return Err(invalid("PremiseSubject"));
            }
            self.validate_store(&store.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(proof, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let fact = &builtin.conclusions[0];
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, fact, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
        let term = if exists {
            format!(
                "(Litex.real{title}Exists {} {})",
                self.compile_object_reference(set, &scope)?,
                references.join(" ")
            )
        } else {
            format!(
                "(Litex.{name}Selected (Litex.{name} {} {} {}))",
                self.compile_object_reference(set, &scope)?,
                references[0],
                references[1]
            )
        };
        Ok((
            definitions,
            format!("(show {statement} from {term})"),
            builtin.conclusions.clone(),
        ))
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(
        &format!("RealExtremum/Theorem{stage}"),
        "Extremum theorem evidence differs in its ID, ordered premises or conclusion.",
    )
}
