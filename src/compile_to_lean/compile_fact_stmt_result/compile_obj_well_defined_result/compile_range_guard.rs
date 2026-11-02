//! Replay the same range coverage certificates for folds and scalar aggregates.
use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::LeanCompileError;
use crate::prelude::*;

pub(super) fn validate_range_guard(
    signature: &FnSet,
    start: &Obj,
    end: &Obj,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(LeanCompileError::unsupported("RangeGuard/UniversalGuard"));
    };
    let parameters = all
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    let [(parameter, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] = parameters.as_slice()
    else {
        return Err(LeanCompileError::unsupported("RangeGuard/GuardParameter"));
    };
    let argument = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
    if all.dom_facts.len() != 2
        || all.then_facts.len() != signature.dom_facts.len()
        || !matches!(&all.dom_facts[0], Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==start.ir() && f.right.ir()==argument.ir())
        || !matches!(&all.dom_facts[1], Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==argument.ir() && f.right.ir()==end.ir())
    {
        return Err(LeanCompileError::unsupported("RangeGuard/GuardInterval"));
    }
    let original = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .next()
        .unwrap();
    let substitution = std::collections::HashMap::from([(original.id, argument)]);
    for (expected, actual) in signature.dom_facts.iter().zip(&all.then_facts) {
        if !instantiated_fact_matches(
            &function_guard_fact(expected)?,
            &actual.clone().into(),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported("RangeGuard/GuardSubject"));
        }
    }
    Ok(())
}

pub(super) fn validate_explicit_range_guards(
    signature: &FnSet,
    start: &Obj,
    end: &Obj,
    guards: &[VerifyFactResult],
) -> Result<(i128, i128), LeanCompileError> {
    if guards.len() < 2 {
        return Err(LeanCompileError::unsupported("RangeGuard/GuardBounds"));
    }
    let mut bounds = Vec::new();
    for (source, endpoint) in guards[..2].iter().zip([start, end]) {
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = source_subject(source)? else {
            return Err(LeanCompileError::unsupported("RangeGuard/GuardEndpoint"));
        };
        if eq.left.ir() != endpoint.ir() {
            return Err(LeanCompileError::unsupported(
                "RangeGuard/GuardEndpointSubject",
            ));
        }
        bounds.push(
            EvalRational::from_obj(&eq.right)
                .and_then(|n| n.to_i128_if_integer())
                .ok_or_else(|| LeanCompileError::unsupported("RangeGuard/GuardEndpointValue"))?,
        );
    }
    let count = bounds[1]
        .checked_sub(bounds[0])
        .and_then(|n| n.checked_add(1))
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| LeanCompileError::unsupported("RangeGuard/GuardInterval"))?;
    if count == 0 || count.checked_mul(signature.dom_facts.len()) != Some(guards.len() - 2) {
        return Err(LeanCompileError::unsupported("RangeGuard/GuardCount"));
    }
    let original = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .next()
        .unwrap();
    for (index, row) in guards[2..].chunks(signature.dom_facts.len()).enumerate() {
        let argument = Obj::Literal(Literal::Number(Number::new(
            (bounds[0] + index as i128).to_string(),
        )));
        let substitution = std::collections::HashMap::from([(original.id, argument)]);
        for (condition, proof) in signature.dom_facts.iter().zip(row) {
            if !instantiated_fact_matches(
                &function_guard_fact(condition)?,
                &source_subject(proof)?,
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported("RangeGuard/GuardSubject"));
            }
        }
    }
    Ok((bounds[0], bounds[1]))
}
pub(super) fn explicit_range_guard_term(
    first: i128,
    last: i128,
    guard_count: usize,
    guard: &str,
    endpoints: [&str; 2],
    references: &[String],
) -> (String, String) {
    let items = (first..=last)
        .map(|n| format!("({n} : ℤ)"))
        .collect::<Vec<_>>()
        .join(", ");
    let rows = &references[2..];
    let cases = rows.chunks(guard_count).enumerate().map(|(index, row)| {
                    let term = row.iter().cloned().rev().reduce(|tail, head| format!("⟨{head}, {tail}⟩")).unwrap();
                    let integer = first + index as i128;
                    format!("  · have _recorded : {guard} (M.number ({integer} : ℂ)) := {term}\n    simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded")
                }).collect::<Vec<_>>().join("\n");
    let branches = std::iter::repeat_n("rfl", rows.len() / guard_count)
        .collect::<Vec<_>>()
        .join(" | ");
    let bindings = format!("let _fold_guards : ∀ k ∈ Litex.integerFoldIndices ({first} : ℤ) ({last} : ℤ), {guard} (M.number (k : ℂ)) := (by\n  intro k hk\n  rw [show Litex.integerFoldIndices ({first} : ℤ) ({last} : ℤ) = [{items}] from by decide] at hk\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk\n  rcases hk with {branches}\n{cases}\n);\n");
    let proof = format!("Litex.integerRangeGuards {} {} ({first} : ℤ) ({last} : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) {guard} _fold_guards k hlow hhigh", endpoints[0], endpoints[1], references[0], references[1]);
    (bindings, proof)
}
