//! Borrow the two original predicate formations, without a new domain lookup.
use super::compile_antiderivative::{invalid, parts, validate_context};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::multivariable::helper::actual_domain;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use std::collections::HashMap;

fn scoped(term: String, bindings: &[String]) -> String {
    if bindings.is_empty() {
        return term;
    }
    format!(
        "(by\n  {}\n  exact {}\n)",
        bindings.join("\n").replace('\n', "\n  "),
        term.replace('\n', "\n  ")
    )
}
impl LitexToLeanCompiler {
    pub(super) fn antiderivative_context_function_terms(
        &self,
        args: &[Obj],
        requirements: &[&Fact],
        references: &[String],
        which: usize,
        prefix: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        validate_context(args, requirements)?;
        if which > 1 || references.len() != requirements.len() {
            return Err(invalid("FunctionContextArity"));
        }
        let offset = requirements.len() - 8 + 4 * which;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = requirements[offset] else {
            return Err(invalid("FunctionMembership"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(invalid("FunctionSignature"));
        };
        let domain = actual_domain(signature).ok_or_else(|| invalid("ActualDomain"))?;
        let signature_term = format!(
            "({}).val",
            self.compile_object_reference(&member.set, position)?
        );
        let reference = |i: usize| references[i].replace('\n', "\n  ");
        let (view, equal) = self.compile_named_limit_domain_view(
            &args[which],
            &domain,
            signature,
            &signature_term,
            &reference(offset),
            prefix,
            position,
        )?;
        let real=format!("(by\n{view}\n  have _{prefix}input_real : ∀ x, M.mem x _{prefix}source_domain → M.mem x (M.standard .real) := {}\n  have _{prefix}output_real : ∀ y, M.mem y _{prefix}signature.target → M.mem y (M.standard .real) := {}\n  refine ⟨_{prefix}signature,_{prefix}member,?_,_{prefix}output_real⟩\n  intro x hx\n  exact _{prefix}input_real x ((congrArg (fun D => M.mem x D) _{prefix}domain_match).mpr hx)\n)",reference(offset+1),reference(offset+2));
        let region =
            self.compile_function_raw_expression_bound(&args[2], position, &HashMap::new())?;
        let cover = format!(
            "(by\n{view}\n  have _{prefix}region_cover : ∀ x, M.mem x {region} → M.mem x _{prefix}source_domain := {}\n  intro x hx\n  exact (congrArg (fun D => M.mem x D) {equal}).mp (_{prefix}region_cover x hx)\n)",
            reference(offset + 3)
        );
        Ok((real, cover))
    }

    pub(super) fn antiderivative_function_from_formation(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        which: usize,
        prefix: &str,
        prior: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let Some((args, _)) = parts(fact) else {
            return Err(invalid("FormationPredicate"));
        };
        if args.len() != 3 || which > 1 {
            return Err(invalid("FormationArguments"));
        }
        let formed =
            SourcePosition::new(Some(prior), SourceOwner::AtomicWDLocals(wd, 3), usize::MAX);
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::ByRequirements(requirements) => {
                validate_context(
                    args,
                    &requirements
                        .iter()
                        .map(|r| &r.requirement)
                        .collect::<Vec<_>>(),
                )?;
                let bindings = self.compile_atomic_wd_locals(wd, fact, prior)?;
                let arguments = args.iter().collect::<Vec<_>>();
                let mut references = Vec::new();
                for (i, requirement) in requirements.iter().enumerate() {
                    let position = SourcePosition {
                        before: 3 + i,
                        ..formed
                    };
                    let term = match &requirement.result {
                        PredicateDomainRequirementProof::Verified(proof) => {
                            if source_subject(proof)? != requirement.requirement {
                                return Err(invalid("FormationProofSubject"));
                            }
                            self.compile_verify(proof, &position)?.1
                        }
                        PredicateDomainRequirementProof::CheckedArgument(checked) => self
                            .compile_checked_domain_argument(
                                &requirement.requirement,
                                checked,
                                &arguments,
                                i,
                                &position,
                            )?,
                    };
                    references.push(term);
                }
                let (real, cover) = self.antiderivative_context_function_terms(
                    args,
                    &requirements
                        .iter()
                        .map(|r| &r.requirement)
                        .collect::<Vec<_>>(),
                    &references,
                    which,
                    prefix,
                    &formed,
                )?;
                Ok((scoped(real, &bindings), scoped(cover, &bindings)))
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                self.compile_known_atomic(cite, fact, &formed)?;
                self.with_cited_atomic_formation(cite.cite_fact_id,&formed,&mut|old,old_wd,old_prior|{
                    let Some((old_args,_))=parts(old) else {return Err(invalid("CitedFormationPredicate"));};
                    let same=|a:&Obj,b:&Obj|a.ir()==b.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a,b);
                    if old_args.len()!=3 || !same(&args[which],&old_args[which]) || !same(&args[2],&old_args[2]) {return Err(invalid("CitedFormationFunctionOrRegion"));}
                    self.antiderivative_function_from_formation(old,old_wd,which,prefix,old_prior)
                })
            }
            _ => Err(invalid("OriginalFormationDomain")),
        }
    }
}
