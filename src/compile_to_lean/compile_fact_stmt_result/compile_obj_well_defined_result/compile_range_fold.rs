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
        let coverage_count = if empty {
            0
        } else {
            super::compile_range_input::validate_range_input(
                input,
                &value.start,
                &value.end,
                &requirements[3..],
            )?
        };
        let guard_offset = 3 + coverage_count;
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
                super::compile_range_guard::validate_range_guard(
                    signature,
                    &value.start,
                    &value.end,
                    &source_subject(&guards[0])?,
                )?;
            } else {
                guard_bounds = Some(super::compile_range_guard::validate_explicit_range_guards(
                    signature,
                    &value.start,
                    &value.end,
                    guards,
                )?);
            }
        }
        let formed = SourcePosition {
            before: children.len(),
            ..*position
        };
        let hf = self.compile_selected_signature(&value.func, iterand, &formed)?;
        let hop = self.compile_selected_signature(&value.op, operation, &formed)?;
        let hop = if op_signature.ret_set.as_ref() == &Obj::StandardSet(StandardSet::RPos) {
            format!("(Litex.positiveFoldOperation {} {hop})", objects[3])
        } else {
            hop
        };
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
            format!(
                "(fun k hlow hhigh => False.elim (Litex.integerBoundsEmpty {} {} ({} : ℤ) ({} : ℤ) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] using {}) (by decide) k hlow hhigh))",
                objects[0],
                objects[1],
                empty_bounds[0],
                empty_bounds[1],
                references[3],
                references[4]
            )
        } else {
            let output = self.compile_object_reference(&signature.ret_set, &formed)?;
            let (domain, domain_set) =
                self.compile_function_semantic_base_domain(signature, &formed)?;
            let guard = self.compile_function_guard_template(signature, &formed)?;
            let source_guard = self.compile_function_explicit_guard_template(signature, &formed)?;
            let guard_proof = if let Some((first, last)) = guard_bounds {
                let (guard_bindings, term) = super::compile_range_guard::explicit_range_guard_term(
                    first,
                    last,
                    signature.dom_facts.len(),
                    &source_guard,
                    [&objects[0], &objects[1]],
                    &references[guard_offset..],
                );
                bindings.push_str(&guard_bindings);
                term
            } else if guarded {
                format!(
                    "{} (Litex.number (M := M) (k : ℂ)) (Litex.NativeBridge.numberInZ k) (Litex.integerLowerBound {} {} k hlow) (Litex.integerUpperBound {} {} k hhigh)",
                    references[guard_offset], objects[0], references[0], objects[1], references[1]
                )
            } else {
                "True.intro".into()
            };
            let membership = self.compile_range_input_member(
                input,
                [&objects[0], &objects[1]],
                [&references[0], &references[1]],
                (coverage_count == 1).then(|| &references[3]),
                &formed,
            )?;
            let (membership, guard_proof) = self.compile_unary_function_domain_certificates(
                signature,
                "(Litex.number (M := M) (k : ℂ))",
                membership,
                &guard_proof,
                &formed,
            )?;
            format!(
                "(fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {output}) {domain_set} (Litex.isSet {output}) {guard} (M.number (k : ℂ))).mpr ⟨{membership}, {guard_proof}⟩)"
            )
        };
        Ok(format!(
            "({bindings}Litex.rangeFold {} {} {} {} {} {signature_term} {} {} {hf} {hop} {} {domain})",
            objects[0],
            objects[1],
            objects[2],
            objects[3],
            objects[4],
            references[0],
            references[1],
            references[2]
        ))
    }
}
