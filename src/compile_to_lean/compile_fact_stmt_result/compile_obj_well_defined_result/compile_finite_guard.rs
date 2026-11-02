//! Original finite-index guard certificates, shared by folds and scalar aggregates.
use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(super) fn validate_finite_guards(
    signature: &FnSet,
    set: &Obj,
    guards: &[VerifyFactResult],
) -> Result<(), LeanCompileError> {
    if signature.dom_facts.is_empty() {
        return if guards.is_empty() {
            Ok(())
        } else {
            Err(LeanCompileError::unsupported(
                "FiniteGuard/ExtraRequirements",
            ))
        };
    }
    if let Obj::SetFormer(SetFormer::ListSet(list)) = set {
        if list.list.len().checked_mul(signature.dom_facts.len()) != Some(guards.len()) {
            return Err(LeanCompileError::unsupported("FiniteGuard/GuardCount"));
        }
        let original = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .next()
            .unwrap();
        for (argument, row) in list
            .list
            .iter()
            .zip(guards.chunks(signature.dom_facts.len()))
        {
            let substitution =
                std::collections::HashMap::from([(original.id, argument.as_ref().clone())]);
            for (condition, proof) in signature.dom_facts.iter().zip(row) {
                if !instantiated_fact_matches(
                    &function_guard_fact(condition)?,
                    &source_subject(proof)?,
                    &substitution,
                ) {
                    return Err(LeanCompileError::unsupported("FiniteGuard/GuardSubject"));
                }
            }
        }
        Ok(())
    } else {
        let [proof] = guards else {
            return Err(LeanCompileError::unsupported(
                "FiniteGuard/UniversalGuardCount",
            ));
        };
        validate_finite_universal_guard(signature, set, &source_subject(proof)?)
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_finite_guard(
        &self,
        signature: &FnSet,
        set: &Obj,
        set_term: &str,
        proofs: &[String],
        position: &SourcePosition<'_>,
        bindings: &mut String,
    ) -> Result<String, LeanCompileError> {
        if signature.dom_facts.is_empty() {
            return Ok("True.intro".into());
        }
        let guard = self.compile_function_explicit_guard_template(signature, position)?;
        if let Obj::SetFormer(SetFormer::ListSet(list)) = set {
            bindings.push_str(&format!("let _fold_tail_0 := {set_term};\n"));
            for i in 0..list.list.len() {
                bindings.push_str(&format!(
                    "let _fold_tail_{} := _fold_tail_{i}.val.tail;\n",
                    i + 1
                ));
            }
            let mut term = format!("Litex.finiteGuardEmpty {guard}");
            for i in (0..list.list.len()).rev() {
                let row =
                    &proofs[i * signature.dom_facts.len()..(i + 1) * signature.dom_facts.len()];
                let head = row
                    .iter()
                    .cloned()
                    .rev()
                    .reduce(|tail, head| format!("⟨{head}, {tail}⟩"))
                    .unwrap();
                term = format!("Litex.finiteGuardInsert _fold_tail_{i} {guard} ({head}) ({term})");
            }
            bindings.push_str(&format!(
                "let _fold_guard : ∀ i, M.mem i (Litex.denote {set_term}) → {guard} i := {term};\n"
            ));
        } else {
            bindings.push_str(&format!("let _fold_guard : ∀ i, M.mem i (Litex.denote {set_term}) → {guard} i := Litex.forallMembersOfRepresentations.{{u, _, 0}} {set_term} (fun _fold_index _fold_member => {} _fold_index _fold_member);\n", proofs[0]));
        }
        Ok("_fold_guard i hi".into())
    }
}

fn validate_finite_universal_guard(
    signature: &FnSet,
    set: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardCoverage"));
    };
    let parameters = all
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    let [(parameter, ParamType::Obj(domain))] = parameters.as_slice() else {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardParameter"));
    };
    if domain.ir() != set.ir()
        || !all.dom_facts.is_empty()
        || all.then_facts.len() != signature.dom_facts.len()
    {
        return Err(LeanCompileError::unsupported("FiniteFold/GuardDomain"));
    }
    let original = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .next()
        .unwrap();
    let substitution = std::collections::HashMap::from([(
        original.id,
        Obj::Identifier(IdentifierObj::from_bound_name(parameter)),
    )]);
    for (expected, actual) in signature.dom_facts.iter().zip(&all.then_facts) {
        if !instantiated_fact_matches(
            &function_guard_fact(expected)?,
            &actual.clone().into(),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported("FiniteFold/GuardSubject"));
        }
    }
    Ok(())
}
