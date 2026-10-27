use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ReduceObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_range_fold_wd(
        &self,
        value: &Reduce,
        proof: &ReduceObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let operation = proof
            .operation_signature_selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Reduce/OperationSignatureCapture"))?;
        let iterand = proof
            .iterand_signature_selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Reduce/IterandSignatureCapture"))?;
        let op_signature = operation.signature();
        let signature = iterand.signature();
        let op_parameters = op_signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let [input] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported("Reduce/IterandArity"));
        };
        if op_parameters.len() != 2
            || !op_signature.dom_facts.is_empty()
            || op_parameters
                .iter()
                .any(|p| p.ir() != signature.ret_set.ir())
            || op_signature.ret_set.ir() != signature.ret_set.ir()
        {
            return Err(LeanCompileError::unsupported("Reduce/SignatureContract"));
        }
        // Positive-real numeric signatures encode their input predicates in
        // the signature itself; they need a separate domain-equality bridge.
        if op_signature.ret_set.as_ref() == &Obj::StandardSet(StandardSet::RPos)
            || (Self::function_uses_numeric_interface(signature)
                && matches!(input, Obj::StandardSet(StandardSet::RPos)))
        {
            return Err(LeanCompileError::unsupported(
                "Reduce/PositiveNumericSignature",
            ));
        }
        let children = &proof.child_obj_well_defined;
        let requirements = &proof.requirement_fact_verified;
        if children.len() != 5 || requirements.len() < 3 {
            return Err(LeanCompileError::unsupported("Reduce/Stages"));
        }
        let subjects = [
            &value.start,
            &value.end,
            &value.func,
            &value.op,
            &value.seed,
        ];
        let mut objects = Vec::new();
        for (index, subject) in subjects.into_iter().enumerate() {
            ensure_object(subject, &children[index])?;
            objects.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, source) in requirements[..3].iter().enumerate() {
            let fact = source_subject(source)?;
            let valid = match (index, &fact) {
                (0 | 1, Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    f.element.ir() == subjects[index].ir()
                        && f.set == Obj::StandardSet(StandardSet::Z)
                }
                (2, Fact::AtomicFact(AtomicFact::InFact(f))) => {
                    f.element.ir() == value.seed.ir() && f.set.ir() == signature.ret_set.ir()
                }
                _ => false,
            };
            if !valid {
                return Err(LeanCompileError::unsupported("Reduce/WDRequirement"));
            }
        }
        // Empty ranges carry the original endpoint-equality checks. Their
        // guarded iterand makes no calls, regardless of its declared domain.
        let mut empty_bounds = Vec::new();
        if matches!(requirements.len(), 5 | 7) {
            for (index, source) in requirements[3..].iter().enumerate() {
                let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = source_subject(source)? else {
                    break;
                };
                if eq.left.ir() != subjects[index % 2].ir() {
                    break;
                }
                let Some(n) =
                    EvalRational::from_obj(&eq.right).and_then(|n| n.to_i128_if_integer())
                else {
                    break;
                };
                empty_bounds.push(n);
            }
        }
        let empty = empty_bounds.len() == requirements.len() - 3
            && empty_bounds.len() >= 2
            && empty_bounds[1] < empty_bounds[0]
            && empty_bounds
                .iter()
                .enumerate()
                .all(|(i, n)| *n == empty_bounds[i % 2]);
        let natural = matches!(input, Obj::StandardSet(StandardSet::N));
        let guard_offset = 3 + usize::from(natural);
        if !empty
            && !matches!(
                input,
                Obj::StandardSet(
                    StandardSet::N
                        | StandardSet::Z
                        | StandardSet::Q
                        | StandardSet::R
                        | StandardSet::C
                )
            )
        {
            return Err(LeanCompileError::unsupported("Reduce/DomainCoverage"));
        }
        let guarded = !signature.dom_facts.is_empty();
        let mut guard_bounds = None;
        if !empty {
            if requirements.len() < guard_offset {
                return Err(LeanCompileError::unsupported("Reduce/DomainCoverage"));
            }
            let guards = &requirements[guard_offset..];
            if !guarded {
                if !guards.is_empty() {
                    return Err(LeanCompileError::unsupported("Reduce/ExtraRequirements"));
                }
            } else if guards.len() == 1 {
                validate_range_fold_guard(signature, value, &source_subject(&guards[0])?)?;
            } else {
                if guards.len() < 2 {
                    return Err(LeanCompileError::unsupported("Reduce/GuardBounds"));
                }
                let mut bounds = Vec::new();
                for (source, endpoint) in guards[..2].iter().zip([&value.start, &value.end]) {
                    let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = source_subject(source)?
                    else {
                        return Err(LeanCompileError::unsupported("Reduce/GuardEndpoint"));
                    };
                    if eq.left.ir() != endpoint.ir() {
                        return Err(LeanCompileError::unsupported("Reduce/GuardEndpointSubject"));
                    }
                    bounds.push(
                        EvalRational::from_obj(&eq.right)
                            .and_then(|n| n.to_i128_if_integer())
                            .ok_or_else(|| {
                                LeanCompileError::unsupported("Reduce/GuardEndpointValue")
                            })?,
                    );
                }
                let count = bounds[1]
                    .checked_sub(bounds[0])
                    .and_then(|n| n.checked_add(1))
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| LeanCompileError::unsupported("Reduce/GuardInterval"))?;
                if count == 0
                    || count.checked_mul(signature.dom_facts.len()) != Some(guards.len() - 2)
                {
                    return Err(LeanCompileError::unsupported("Reduce/GuardCount"));
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
                            return Err(LeanCompileError::unsupported("Reduce/GuardSubject"));
                        }
                    }
                }
                guard_bounds = Some((bounds[0], bounds[1]));
            }
        }
        if !empty
            && natural
            && !matches!(source_subject(&requirements[3])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == value.start.ir() && f.set == Obj::StandardSet(StandardSet::N))
        {
            return Err(LeanCompileError::unsupported("Reduce/NaturalStart"));
        }
        let formed = SourcePosition {
            before: children.len(),
            ..*position
        };
        let hf = self.compile_selected_signature(&value.func, iterand, &formed)?;
        let hop = self.compile_selected_signature(&value.op, operation, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        let mut bindings = String::new();
        let mut references = Vec::new();
        for (index, source) in requirements.iter().enumerate() {
            let prior = SourcePosition {
                before: children.len() + index,
                ..*position
            };
            let checked = self.compile_verify(source, &prior)?;
            let reference = format!("h_{}", source_subject(source)?.fact_id().value());
            bindings.push_str(&format!(
                "let {reference} : {} := {};\n",
                checked.0, checked.1
            ));
            references.push(reference);
        }
        let domain = if empty {
            format!("(fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty {} {} ({} : ℤ) ({} : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by decide) k hlow hhigh))",
                objects[0], objects[1], empty_bounds[0], empty_bounds[1], references[3], references[4])
        } else {
            let output = self.compile_object_reference(&signature.ret_set, &formed)?;
            let (domain, domain_set) =
                self.compile_function_semantic_base_domain(signature, &formed)?;
            let guard = self.compile_function_guard_template(signature, &formed)?;
            let guard_proof = if let Some((first, last)) = guard_bounds {
                let items = (first..=last)
                    .map(|n| format!("({n} : ℤ)"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let rows = &references[guard_offset + 2..];
                let cases = rows.chunks(signature.dom_facts.len()).enumerate().map(|(index, row)| {
                    let term = row.iter().cloned().rev().reduce(|tail, head| format!("⟨{head}, {tail}⟩")).unwrap();
                    let integer = first + index as i128;
                    format!("  · have _recorded : {guard} (M.number ({integer} : ℂ)) := {term}\n    simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using _recorded")
                }).collect::<Vec<_>>().join("\n");
                let branches = std::iter::repeat_n("rfl", rows.len() / signature.dom_facts.len())
                    .collect::<Vec<_>>()
                    .join(" | ");
                bindings.push_str(&format!("let _fold_guards : ∀ k ∈ Litex.integerFoldIndices ({first} : ℤ) ({last} : ℤ), {guard} (M.number (k : ℂ)) := (by\n  intro k hk\n  rw [show Litex.integerFoldIndices ({first} : ℤ) ({last} : ℤ) = [{items}] from by decide] at hk\n  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk\n  rcases hk with {branches}\n{cases}\n);\n"));
                format!("Litex.integerRangeGuards {} {} ({first} : ℤ) ({last} : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) {guard} _fold_guards k hlow hhigh", objects[0], objects[1], references[guard_offset], references[guard_offset+1])
            } else if guarded {
                format!("{} (Litex.number (M := M) (k : ℂ)) (Litex.NativeBridge.numberInZ k) (Litex.integerLowerBound {} {} k hlow) (Litex.integerUpperBound {} {} k hhigh)", references[guard_offset], objects[0], references[0], objects[1], references[1])
            } else {
                "True.intro".into()
            };
            let membership = if natural {
                format!(
                    "Litex.integerInNaturalAbove {} {} k hlow",
                    objects[0], references[3]
                )
            } else {
                let Obj::StandardSet(input) = input else {
                    unreachable!()
                };
                format!(
                    "Litex.integerInUnboundedCarrier .{} (by decide) k",
                    standard_value_constructor(input)?
                )
            };
            format!("(fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {output}) {domain_set} (Litex.isSet {output}) {guard} (M.number (k : ℂ))).mpr ⟨{membership}, {guard_proof}⟩)")
        };
        Ok(format!("({bindings}Litex.rangeFold {} {} {} {} {} {signature_term} {} {} {hf} {hop} {} {domain})",
            objects[0], objects[1], objects[2], objects[3], objects[4], references[0], references[1], references[2]))
    }
}

fn validate_range_fold_guard(
    signature: &FnSet,
    value: &Reduce,
    fact: &Fact,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(all) = fact else {
        return Err(LeanCompileError::unsupported("Reduce/UniversalGuard"));
    };
    let parameters = all
        .typed_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
        .collect::<Vec<_>>();
    let [(parameter, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] = parameters.as_slice()
    else {
        return Err(LeanCompileError::unsupported("Reduce/GuardParameter"));
    };
    let argument = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
    if all.dom_facts.len() != 2
        || all.then_facts.len() != signature.dom_facts.len()
        || !matches!(&all.dom_facts[0], Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==value.start.ir() && f.right.ir()==argument.ir())
        || !matches!(&all.dom_facts[1], Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir()==argument.ir() && f.right.ir()==value.end.ir())
    {
        return Err(LeanCompileError::unsupported("Reduce/GuardInterval"));
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
            return Err(LeanCompileError::unsupported("Reduce/GuardSubject"));
        }
    }
    Ok(())
}
