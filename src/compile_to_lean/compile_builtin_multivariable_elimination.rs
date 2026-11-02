use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

impl LitexToLeanCompiler {
    // Native inference clauses retain the same semantic-object calling
    // convention as source forall citations. Only their body uses raw values.
    pub(super) fn compile_multivariable_clause_value_proposition(
        &self,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::ForallFact(fact) = fact else {
            return Err(invalid("InferenceClause"));
        };
        let param = parameter(&fact.typed_parameters, &Obj::StandardSet(StandardSet::RPos))?;
        let [clause] = fact.then_facts.as_slice() else {
            return Err(invalid("InferenceClause"));
        };
        if !fact.dom_facts.is_empty() {
            return Err(invalid("InferenceClauseGuard"));
        }
        let name = format!("_value_i{}", param.id.value());
        let bound = HashMap::from([(param.id, format!("(Litex.denote {name})"))]);
        let body = self.compile_function_raw_predicate(&clause.clone().into(), position, &bound)?;
        Ok(format!(
            "∀ ({name} : Litex.Obj (M := M) M.Value), Litex.In {name} Litex.RPos → ({body})"
        ))
    }

    pub(super) fn compile_builtin_multivariable_elimination(
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
            MultiLimitAtToDefinition => (4, 5, 2),
            MultiLimitAtExists => (4, 5, 1),
            MultiLimitAtUnique => (5, 6, 1),
            MultiLimitAtSelected => (3, 5, 1),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != outputs
            || conclusions_wd.len() != outputs
        {
            return Err(invalid("Stages"));
        }
        let (f, p, n) = (&args[0], &args[1], &args[2]);
        let source = if builtin.theorem == MultiLimitAtSelected {
            validate_existence(&builtin.requirements[4], f, p, n)?;
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
                return Err(invalid("SelectedFormation"));
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) = &wd
                .as_detailed()
                .map_err(|_| invalid("SelectedDetailedFormation"))?
                .predicate_domain
            else {
                return Err(invalid("SelectedOriginalDomain"));
            };
            if capture.requirements.len()!=5 || !builtin.requirements[..4].iter().zip(&capture.requirements[..4]).all(|(a,b)|
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)) {
                return Err(invalid("SelectedOriginalContext"));
            }
            &capture.function_domain
        } else {
            validate_candidate(&builtin.requirements[4], f, p, n, &args[3])?;
            if builtin.theorem == MultiLimitAtUnique {
                validate_candidate(&builtin.requirements[5], f, p, n, &args[4])?;
            }
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &dom_stores[4].infer
            else {
                return Err(invalid("OriginalInferenceCapture"));
            };
            let [InferMultivariableAnalysisFactResult::Definition(inference)] = rules.as_slice()
            else {
                return Err(invalid("OriginalInferenceCapture"));
            };
            if inference.source_fact_id != builtin.requirements[4].fact_id()
                || inference.derived.len() != 3
            {
                return Err(invalid("OriginalInferenceIdentity"));
            }
            inference
                .function_domain
                .as_ref()
                .ok_or_else(|| invalid("OriginalFunctionDomain"))?
        };
        super::compile_multivariable_limit_context::validate_limit_context(
            args,
            &builtin.requirements[..4],
            source,
            None,
        )?;
        let actual = crate::execute::execute_fact_stmt::multivariable::helper::actual_domain(
            &source.signature,
        )
        .ok_or_else(|| invalid("ActualDomain"))?;
        match builtin.theorem {
            MultiLimitAtToDefinition => {
                super::compile_multivariable_scalar_limit::validate_clauses(
                    f,
                    p,
                    n,
                    None,
                    &args[3],
                    &actual,
                    &builtin.conclusions,
                )?
            }
            MultiLimitAtExists => validate_existence(&builtin.conclusions[0], f, p, n)?,
            MultiLimitAtUnique => {
                if !matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==args[3].ir() && eq.right.ir()==args[4].ir())
                {
                    return Err(invalid("UniqueConclusion"));
                }
            }
            MultiLimitAtSelected => {
                let Fact::AtomicFact(goal) = &builtin.conclusions[0] else {
                    return Err(invalid("SelectedConclusion"));
                };
                let (r, false) = super::compile_multivariable_scalar_limit::parts(goal)
                    .ok_or_else(|| invalid("SelectedConclusion"))?
                else {
                    return Err(invalid("SelectedNegative"));
                };
                let Obj::LimitOperator(LimitOperator::MultivariableScalar(selector)) = &r.value
                else {
                    return Err(invalid("SelectedObject"));
                };
                if r.function.ir() != f.ir()
                    || r.point.ir() != p.ir()
                    || r.dimension.ir() != n.ir()
                    || selector.function.ir() != f.ir()
                    || selector.point.ir() != p.ir()
                    || selector.dimension.ir() != n.ir()
                {
                    return Err(invalid("SelectedArguments"));
                }
            }
            _ => unreachable!(),
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
                return Err(invalid("OriginalProofSubject"));
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
            before: count,
            ..*position
        };
        for (fact, wd) in builtin.conclusions.iter().zip(conclusions_wd) {
            self.compile_fact_wd(wd, fact, &formed)?;
        }
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let candidate = format!("h_{}", builtin.requirements[4].fact_id().value());
        let statements = builtin
            .conclusions
            .iter()
            .zip(conclusions_wd)
            .map(|(f, w)| self.compile_formed_fact_proposition(w, f, &formed))
            .collect::<Result<Vec<_>, _>>()?;
        let proof=match builtin.theorem {
            MultiLimitAtSelected=>format!("(by\n  apply Litex.multivariableScalarLimitValueSelected {}\n  obtain ⟨value,hv,hc⟩ := {candidate}\n  exact ⟨Litex.denote value,hc⟩\n)",raw.join(" ")),
            MultiLimitAtExists=>format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.multivariableScalarExistsOfCandidate {} {candidate}\n  exact ⟨value,hv,hc⟩\n)",raw.join(" ")),
            MultiLimitAtUnique=>{
                let (view,_)=self.compile_multivariable_limit_view(f,source,&scope)?;
                let real=self.compile_euclidean_limit_function_context(args,&builtin.requirements[..4],source,None,&scope)?;
                format!("(by\n{view}\n{real}\n  exact Litex.multivariableScalarLimitUnique (M := M) {} _multivariable_real {candidate} h_{}\n)",raw.join(" "),builtin.requirements[5].fact_id().value())
            }
            MultiLimitAtToDefinition=>{
                let mut proofs=Vec::new();
                for (index,(statement,wd)) in statements.iter().zip(conclusions_wd).enumerate(){
                    let scope=SourcePosition::new(Some(&formed),SourceOwner::FactWD(wd),usize::MAX);
                    let (view,equal)=self.compile_multivariable_limit_view(f,source,&scope)?;
                    let begin=format!("(by\n{view}\n  have _clauses := Litex.multivariableScalarLimitClauses (M := M) {} {candidate}\n",raw.join(" "));
                    let body=if index==0 {
                        format!("  intro _Host _rep radius h_radius\n  obtain ⟨input,hi,hpos,hclose⟩ := _clauses.1 (Litex.denote radius) h_radius\n  have hi : M.mem (Litex.denote input) _multivariable_source_domain := (congrArg (fun D => M.mem (Litex.denote input) D) {equal}).mpr hi\n  exact ⟨input,hi,hpos,hclose⟩\n)")
                    } else {
                        format!("  intro _Host _rep epsilon h_epsilon\n  obtain ⟨delta,hd,hcontrol⟩ := _clauses.2 (Litex.denote epsilon) h_epsilon\n  refine ⟨delta,hd,?_⟩\n  change ∀ input : M.Value, M.mem input _ → M.mem input _\n  intro input h_input\n  obtain ⟨hi,_,hpos,hclose⟩ := (Litex.SetSemantics.sep_members _ _ _).mp h_input\n  apply (Litex.SetSemantics.sep_members _ _ _).mpr\n  exact ⟨hi,hi,hcontrol input ((congrArg (fun D => M.mem input D) {equal}).mp hi) hpos hclose⟩\n)")
                    };
                    proofs.push(format!("(show {statement} from {begin}{body})"));
                }
                format!("(And.intro {} {})",proofs[0],proofs[1])
            }
            _=>unreachable!(),
        };
        let statement = conjunction_proposition(statements)?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn validate_candidate(
    fact: &Fact,
    f: &Obj,
    p: &Obj,
    n: &Obj,
    v: &Obj,
) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(a) if super::compile_multivariable_scalar_limit::parts(a).is_some_and(|(r,negative)|!negative&&r.function.ir()==f.ir()&&r.point.ir()==p.ir()&&r.dimension.ir()==n.ir()&&r.value.ir()==v.ir()))
    {
        Ok(())
    } else {
        Err(invalid("OriginalCandidate"))
    }
}
fn validate_existence(fact: &Fact, f: &Obj, p: &Obj, n: &Obj) -> Result<(), LeanCompileError> {
    let Fact::ExistFact(e) = fact else {
        return Err(invalid("Existence"));
    };
    let v = parameter(&e.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
    if [f, p, n].iter().any(|a| contains_parameter(a, v.id)) {
        return Err(invalid("ExistenceCapture"));
    }
    let [QuantifierFreeFact::AtomicFact(candidate)] = e.facts.as_slice() else {
        return Err(invalid("ExistenceClause"));
    };
    validate_candidate(
        &Fact::AtomicFact(candidate.clone()),
        f,
        p,
        n,
        &Obj::Identifier(IdentifierObj::from_bound_name(v)),
    )
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("MultivariableElimination/{stage}"),"Scalar Euclidean elimination theorems retain the original complete-domain inference capture, exact context/candidates/clauses and ordered stages.")
}
