//! Replay point membership from its original continuity formation, including exact WD citations.
use super::compile_function_continuity::continuity_parts;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;

pub(super) struct ContinuityPointFormation {
    pub bindings: Vec<String>,
    pub domain: Obj,
    pub function: String,
    pub point: String,
    pub membership: String,
    pub domain_equality: String,
    pub real_function: String,
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuityPointFormation/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_continuity_point_formation(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<ContinuityPointFormation, LeanCompileError> {
        let (function, point, _, negative) =
            continuity_parts(fact).ok_or_else(|| invalid("Family"))?;
        if negative {
            return Err(invalid("PositiveProperty"));
        }
        let bindings = self.compile_atomic_wd_locals(wd, fact, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::AtomicWDLocals(wd, 2),
            usize::MAX,
        );
        let f = self.compile_object_reference(function, &formed)?;
        let p = self.compile_object_reference(point, &formed)?;
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::FunctionAnalysis(formation) => {
                let [member] = formation.requirements.as_slice() else {
                    return Err(invalid("PointRequirement"));
                };
                // The ordinary WD consumer above validates the exact function,
                // complete domain, point subject and captured membership route.
                let (view, equality) = self.compile_function_limit_domain_view(
                    function,
                    &formation.function_domain,
                    &formed,
                )?;
                let mut bindings = bindings;
                bindings.extend(
                    view.lines()
                        .map(|line| line.strip_prefix("  ").unwrap_or(line).to_owned()),
                );
                bindings.push(format!("have _continuity_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := {equality} ▸ h_{}",member.requirement.fact_id().value()));
                Ok(ContinuityPointFormation {
                    bindings,
                    domain: formation.function_domain.domain.clone(),
                    function: f,
                    point: p,
                    membership: "_continuity_point_domain".into(),
                    domain_equality: equality,
                    real_function: "_continuity_domain".into(),
                })
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                self.compile_known_atomic(cite, fact, &formed)?;
                let mut callback = |source: &AtomicFact,
                                    source_wd: &AtomicFactWellDefinedProof,
                                    prior: &SourcePosition<'_>| {
                    let (old_function, old_point, _, negative) =
                        continuity_parts(source).ok_or_else(|| invalid("CitedFamily"))?;
                    if negative {
                        return Err(invalid("CitedPositive"));
                    }
                    let mut original =
                        self.compile_continuity_point_formation(source, source_wd, prior)?;
                    original.bindings.push(format!(
                        "have _continuity_previous_domain := {}",
                        original.domain_equality
                    ));
                    original.bindings.push(format!(
                        "have _continuity_previous_real := {}",
                        original.real_function
                    ));
                    let [function_equal, point_equal] = cite
                        .why_parameters_of_known_fact_are_equal_to_givens
                        .as_slice()
                    else {
                        return Err(invalid("Equalities"));
                    };
                    for (old, current, proof, name, old_term, new_term) in [
                        (
                            old_function,
                            function,
                            function_equal,
                            "_continuity_function_eq",
                            &original.function,
                            &f,
                        ),
                        (
                            old_point,
                            point,
                            point_equal,
                            "_continuity_point_eq",
                            &original.point,
                            &p,
                        ),
                    ] {
                        let obligation = EqualFact {
                            fact_id: fact.fact_id(),
                            left: old.clone(),
                            right: current.clone(),
                            line_file: None,
                        };
                        let equality = self.compile_equality_search(&obligation, proof, &formed)?;
                        original.bindings.push(format!("have {name} : Litex.denote {old_term} = Litex.denote {new_term} := {equality}"));
                    }
                    original.bindings.push(format!("have _continuity_point_domain : M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) := by\n  rw [← _continuity_function_eq, ← _continuity_point_eq]\n  exact {}",original.membership));
                    original.bindings.push("have _continuity_complete_domain := _continuity_previous_domain.trans (congrArg (Litex.FunctionSemantics.domainValue (M := M)) _continuity_function_eq)".into());
                    original.bindings.push(format!("have _continuity_real_function : Litex.RealFunctionValue M (Litex.denote {f}) := _continuity_function_eq ▸ _continuity_previous_real"));
                    original.domain_equality = "_continuity_complete_domain".into();
                    original.real_function = "_continuity_real_function".into();
                    Ok(original)
                };
                let original =
                    self.with_cited_atomic_formation(cite.cite_fact_id, &formed, &mut callback)?;
                let mut bindings = bindings;
                bindings.extend(original.bindings);
                Ok(ContinuityPointFormation {
                    bindings,
                    domain: original.domain,
                    function: f,
                    point: p,
                    membership: "_continuity_point_domain".into(),
                    domain_equality: original.domain_equality,
                    real_function: original.real_function,
                })
            }
            _ => Err(invalid("DomainEvidence")),
        }
    }
}
