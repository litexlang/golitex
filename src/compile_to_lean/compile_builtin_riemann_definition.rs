//! Replay the original integral definition clauses and zero-width NativeSchema.
use super::compile_riemann_definition::validate_clauses;
use super::compile_riemann_integral::{endpoint_rewrites, validate_domain_requirement};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;
use std::collections::HashMap;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannDefinition/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_riemann_definition(
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
        let (arity, count, outputs) = match builtin.theorem {
            RiemannIntegralFromDefinition => (4, 10, 1),
            RiemannIntegralToDefinition => (4, 5, 6),
            RiemannIntegralZero => (2, 3, 1),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain {name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != outputs
            || conclusions_wd.len() != outputs
        {
            return Err(invalid("OriginalStages"));
        }
        let to = builtin.theorem == RiemannIntegralToDefinition;
        let zero = builtin.theorem == RiemannIntegralZero;
        let candidate = if to {
            &builtin.requirements[4]
        } else {
            &builtin.conclusions[0]
        };
        let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(source)) = candidate else {
            return Err(invalid("Candidate"));
        };
        if source.function.ir() != args[0].ir()
            || source.lower.ir() != args[1].ir()
            || source.upper.ir() != args[if zero { 1 } else { 2 }].ir()
            || if zero {
                !is_zero(&source.value)
            } else {
                source.value.ir() != args[3].ir()
            }
        {
            return Err(invalid("CandidateArguments"));
        }
        let req = &builtin.requirements;
        if !zero
            && !matches!(&req[3], Fact::AtomicFact(AtomicFact::InFact(m))
                if m.element.ir()==source.value.ir() && m.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("ValueCarrier"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        for (fact, wd) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(wd, fact, &formed)?;
        }
        let (domain, real, (view, equal)) = if to {
            let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[4] else {
                return Err(invalid("OriginalCandidateProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
                return Err(invalid("OriginalCandidateSuccess"));
            };
            self.riemann_certificate_domain(
                &p.fact,
                &p.well_defined_proof,
                &SourcePosition {
                    before: 4,
                    ..*position
                },
            )?
        } else {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("OriginalCandidateFormation"));
            };
            self.riemann_certificate_domain(
                &AtomicFact::HasRiemannIntegralFact(source.clone()),
                wd,
                &formed,
            )?
        };
        for (i, r) in req[..3].iter().enumerate() {
            validate_domain_requirement(r, i, &source.lower, &source.upper, &domain)?;
        }
        if !zero {
            validate_clauses(
                source,
                &domain,
                if to { &builtin.conclusions } else { &req[4..] },
            )?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = [
            &source.function,
            &source.lower,
            &source.upper,
            &source.value,
        ]
        .into_iter()
        .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
        .collect::<Result<Vec<_>, _>>()?;
        let all = raw.join(" ");
        let statements = builtin
            .conclusions
            .iter()
            .zip(conclusions_wd)
            .map(|(f, w)| self.compile_formed_fact_proposition(w, f, &formed))
            .collect::<Result<Vec<_>, _>>()?;
        let reductions =
            self.compile_riemann_endpoint_reductions(&source.lower, &source.upper, &scope)?;
        let proof = if zero {
            let mut cover = vec![
                format!("have _integral_domain_eq := {equal}"),
                "rw [← _integral_domain_eq]".into(),
            ];
            if let Some((proofs, names)) = &reductions {
                cover.push(proofs.clone());
                cover.push("unfold Litex.riemannIntervalValue".into());
                cover.push(endpoint_rewrites(names, "").replace("\n  ", "\n"));
            }
            cover.push(format!("exact {}", refs[2]));
            format!("(by\n{view}\n  have _riemann_original_real := {real}\n  apply Litex.riemannIntegralZeroCandidate {} {} _riemann_original_real {}\n  {}\n)",
                raw[0], raw[1], refs[0], cover.join("\n").replace('\n',"\n  "))
        } else if !to {
            let mut clauses = refs[4..].to_vec();
            for i in [2, 3, 5] {
                let mut steps = Vec::new();
                if i == 2 {
                    steps.push(format!("have _integral_domain_eq := {equal}"));
                    steps.push("rw [← _integral_domain_eq]".into());
                }
                if let Some((proofs, names)) = &reductions {
                    steps.push(proofs.clone());
                    if i == 2 {
                        steps.push("unfold Litex.riemannIntervalValue".into());
                    } else if i == 3 {
                        steps.push(
                            "unfold Litex.riemannRestrictedRangeValue Litex.riemannIntervalValue"
                                .into(),
                        );
                    }
                    steps.push(endpoint_rewrites(names, "").replace("\n  ", "\n"));
                }
                if i == 5 {
                    steps.push("intro _epsilon _epsilon_member _interval_order".into());
                    steps.push(format!("exact {} (Litex.semanticObject (M := M) _epsilon (M.member_isSet _epsilon_member)) _epsilon_member _interval_order",refs[i+4]));
                } else {
                    steps.push(format!("exact {}", refs[i + 4]));
                }
                clauses[i] = format!("(by\n  {}\n)", steps.join("\n").replace('\n', "\n  "));
            }
            format!("(by\n{view}\n  have _riemann_original_real := {real}\n  exact Litex.riemannIntegralFromDefiningClauses {all} {} ⟨{}⟩\n)",refs[3],clauses.join(", "))
        } else {
            let mut terms = Vec::new();
            for i in 0..6 {
                let projection = conjunction_projection("_integral_clauses", i, 6);
                let mut steps = vec![format!("have _integral_clause := {projection}")];
                if i == 2 {
                    steps.push(format!("have _integral_domain_eq := {equal}"));
                    steps.push("rw [← _integral_domain_eq] at _integral_clause".into());
                }
                if [2, 3, 5].contains(&i) {
                    if let Some((proofs, names)) = &reductions {
                        steps.push(proofs.clone());
                        if i == 2 {
                            steps.push(
                                "unfold Litex.riemannIntervalValue at _integral_clause".into(),
                            );
                        } else if i == 3 {
                            steps.push("unfold Litex.riemannRestrictedRangeValue Litex.riemannIntervalValue at _integral_clause".into());
                        }
                        steps.push(
                            endpoint_rewrites(names, " at _integral_clause").replace("\n  ", "\n"),
                        );
                    }
                }
                if i == 5 {
                    steps.push("intro _Host _rep epsilon h_epsilon h_order".into());
                    steps.push(
                        "exact _integral_clause (Litex.denote epsilon) h_epsilon h_order".into(),
                    );
                } else {
                    steps.push("exact _integral_clause".into());
                }
                terms.push(format!(
                    "(show {} from (by\n  {}\n))",
                    statements[i],
                    steps.join("\n").replace('\n', "\n  ")
                ));
            }
            format!("(by\n{view}\n  have _riemann_original_real := {real}\n  have _integral_clauses := Litex.riemannIntegralDefiningClauses {all} {}\n  exact ⟨{}⟩\n)",refs[4],terms.join(", "))
        };
        let statement = conjunction_proposition(statements)?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
