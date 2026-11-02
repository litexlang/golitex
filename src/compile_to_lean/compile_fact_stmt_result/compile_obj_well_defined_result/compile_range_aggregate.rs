use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_range_aggregate_wd(
        &self,
        object: &IteratedOperator,
        proof: &P,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (first, last, function, product, children, requirements, selection) =
            match (object, proof) {
                (IteratedOperator::Sum(s), P::Sum(p)) => (
                    &s.start,
                    &s.end,
                    &s.func,
                    false,
                    &p.child_obj_well_defined,
                    &p.requirement_fact_verified,
                    &p.signature_selection,
                ),
                (IteratedOperator::Product(s), P::Product(p)) => (
                    &s.start,
                    &s.end,
                    &s.func,
                    true,
                    &p.child_obj_well_defined,
                    &p.requirement_fact_verified,
                    &p.signature_selection,
                ),
                _ => return Err(LeanCompileError::unsupported("RangeAggregate/Constructor")),
            };
        let selection = selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("RangeAggregate/SignatureCapture"))?;
        let signature = selection.signature();
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let [input] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported("RangeAggregate/InputArity"));
        };
        if children.len() != 3 || requirements.len() < 4 {
            return Err(LeanCompileError::unsupported("RangeAggregate/Stages"));
        }
        let mut terms = Vec::new();
        for (index, object) in [first, last, function].iter().enumerate() {
            ensure_object(object, &children[index])?;
            terms.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, endpoint) in [first, last].iter().enumerate() {
            if !matches!(source_subject(&requirements[index])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == endpoint.ir() && f.set == Obj::StandardSet(StandardSet::Z))
            {
                return Err(LeanCompileError::unsupported(
                    "RangeAggregate/EndpointMembership",
                ));
            }
        }
        if !matches!(source_subject(&requirements[2])?, Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir() == first.ir() && f.right.ir() == last.ir())
        {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/EndpointOrder",
            ));
        }
        if !matches!(source_subject(&requirements[3])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == signature.ret_set.ir() && f.right == Obj::StandardSet(StandardSet::C))
        {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/OutputCarrier",
            ));
        }
        let coverage_count = super::compile_range_input::validate_range_input(
            input,
            first,
            last,
            &requirements[4..],
        )?;
        let guard_offset = 4 + coverage_count;
        let guards = &requirements[guard_offset..];
        let guard_bounds = if signature.dom_facts.is_empty() {
            if !guards.is_empty() {
                return Err(LeanCompileError::unsupported(
                    "RangeAggregate/ExtraRequirements",
                ));
            }
            None
        } else if guards.len() == 1 {
            super::compile_range_guard::validate_range_guard(
                signature,
                first,
                last,
                &source_subject(&guards[0])?,
            )?;
            None
        } else {
            Some(super::compile_range_guard::validate_explicit_range_guards(
                signature, first, last, guards,
            )?)
        };
        let formed = SourcePosition {
            before: 3,
            ..*position
        };
        let member = self.compile_selected_signature(function, selection, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        if coverage_count == 0 && signature.dom_facts.is_empty() {
            let Obj::StandardSet(input) = input else {
                unreachable!()
            };
            let proofs = requirements
                .iter()
                .enumerate()
                .map(|(index, evidence)| {
                    self.compile_wd_requirement(
                        evidence,
                        &SourcePosition {
                            before: 3 + index,
                            ..*position
                        },
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let input = standard_value_constructor(input)?;
            let domain =
                format!("(fun k _ _ => Litex.unguardedIntegerDomain .{input} _ _ (by decide) k)");
            return Ok(format!(
                "(Litex.rangeAggregate {product} {} {} {} {signature_term} {} {} {} {member} {} {domain})",
                terms[0], terms[1], terms[2], proofs[0], proofs[1], proofs[2], proofs[3]
            ));
        }
        let mut proofs = Vec::new();
        let mut bindings = String::new();
        for (index, evidence) in requirements.iter().enumerate() {
            let (proposition, proof) = self.compile_verify(
                evidence,
                &SourcePosition {
                    before: 3 + index,
                    ..*position
                },
            )?;
            let reference = format!("h_{}", source_subject(evidence)?.fact_id().value());
            bindings.push_str(&format!("let {reference} : {proposition} := {proof};\n"));
            proofs.push(reference);
        }
        let domain = {
            let guard = self.compile_function_guard_template(signature, &formed)?;
            let source_guard = self.compile_function_explicit_guard_template(signature, &formed)?;
            let guard_proof = if let Some((first, last)) = guard_bounds {
                let (guard_bindings, proof) = super::compile_range_guard::explicit_range_guard_term(
                    first,
                    last,
                    signature.dom_facts.len(),
                    &source_guard,
                    [&terms[0], &terms[1]],
                    &proofs[guard_offset..],
                );
                bindings.push_str(&guard_bindings);
                proof
            } else if signature.dom_facts.is_empty() {
                "True.intro".into()
            } else {
                format!(
                    "{} (Litex.number (M := M) (k : ℂ)) (Litex.NativeBridge.numberInZ k) (Litex.integerLowerBound {} {} k hlow) (Litex.integerUpperBound {} {} k hhigh)",
                    proofs[guard_offset], terms[0], proofs[0], terms[1], proofs[1]
                )
            };
            let member = self.compile_range_input_member(
                input,
                [&terms[0], &terms[1]],
                [&proofs[0], &proofs[1]],
                (coverage_count == 1).then(|| &proofs[4]),
                &formed,
            )?;
            let (member, guard_proof) = self.compile_unary_function_domain_certificates(
                signature,
                "(Litex.number (M := M) (k : ℂ))",
                member,
                &guard_proof,
                &formed,
            )?;
            let output = self.compile_object_reference(&signature.ret_set, &formed)?;
            let (domain, domain_set) =
                self.compile_function_semantic_base_domain(signature, &formed)?;
            format!(
                "(fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {output}) {domain_set} (Litex.isSet {output}) {guard} (M.number (k : ℂ))).mpr ⟨{member}, {guard_proof}⟩)"
            )
        };
        Ok(format!(
            "({bindings}Litex.rangeAggregate {product} {} {} {} {signature_term} {} {} {} {member} {} {domain})",
            terms[0], terms[1], terms[2], proofs[0], proofs[1], proofs[2], proofs[3]
        ))
    }

    pub(in crate::compile_to_lean) fn compile_scalar_aggregate_member(
        &self,
        fact: &InFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::AggregateScalarCodomainBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StandardSet(target) = &fact.set else {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/MembershipTarget",
            ));
        };
        let Obj::StandardSet(output) = &proof.iterand_return_set else {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/OutputCarrier",
            ));
        };
        let (product, range) = match &fact.element {
            Obj::IteratedOperator(IteratedOperator::Sum(_)) => (false, true),
            Obj::IteratedOperator(IteratedOperator::Product(_)) => (true, true),
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_)) => (false, false),
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => (true, false),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "RangeAggregate/MemberConstructor",
                ));
            }
        };
        let positive = matches!(
            output,
            StandardSet::NPos | StandardSet::QPos | StandardSet::RPos
        ) && (product || range);
        let base = match output {
            StandardSet::NPos => StandardSet::N,
            StandardSet::RPos => StandardSet::R,
            _ => numeric_refinement(output)
                .map(|(base, _)| base)
                .unwrap_or_else(|| output.clone()),
        };
        let expected = if positive { output } else { &base };
        if &proof.codomain != expected {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/OutputClosureContract",
            ));
        }
        let object = self.compile_object_reference(&fact.element, position)?;
        let checked = position.with_visible_wd(&fact.element, &mut |wd, _| {
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IteratedOperator(p),
                ..
            } = (wd).detailed_ref()
            else {
                return Err(LeanCompileError::unsupported(
                    "RangeAggregate/MemberConstructor",
                ));
            };
            let selected = match p {
                P::Sum(p) => &p.signature_selection,
                P::Product(p) => &p.signature_selection,
                P::SumOfFiniteSet(p) => &p.signature_selection,
                P::ProductOfFiniteSet(p) => &p.signature_selection,
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "RangeAggregate/MemberConstructor",
                    ));
                }
            };
            if selected
                .as_ref()
                .is_none_or(|s| s.signature().ret_set.as_ref() != &proof.iterand_return_set)
            {
                return Err(LeanCompileError::unsupported(
                    "RangeAggregate/MemberSignature",
                ));
            }
            match p {
                P::SumOfFiniteSet(_) | P::ProductOfFiniteSet(_) => {
                    Self::finite_aggregate_uses_standard_input(p)
                }
                _ => Ok(true),
            }
        })?;
        if checked.is_none() {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/MemberProducer",
            ));
        }
        let carrier = standard_value_constructor(&base)?;
        let law = match &fact.element {
            Obj::IteratedOperator(
                IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_),
            ) => {
                if checked == Some(true) {
                    "finiteAggregateMember"
                } else {
                    "finiteAggregateOnMember"
                }
            }
            _ => "rangeAggregateMember",
        };
        let raw_object = "(Litex.semanticObject (M := M) _value (M.member_isSet _member))";
        let member = if output == &base {
            format!("(Litex.{law} {object} .{carrier} rfl)")
        } else {
            let inclusion = standard_inclusion_term(output, &base, raw_object, "_member")?;
            format!(
                "(Litex.{law}OfOutputSubset {object} .{carrier} (fun _value _member => {inclusion}))"
            )
        };
        // A coarser requested carrier uses the base projection of the same
        // validated closure result; do not build unused positivity evidence.
        if matches!(
            target,
            StandardSet::N | StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
        ) {
            return standard_inclusion_term(&base, target, &object, &member);
        }
        let member = if positive {
            let sign = standard_sign_term(output, "positive", raw_object, "_member")?;
            let positive_output = format!(
                "(fun _value _member => (Litex.positiveRealPredicate_iff {raw_object}).mpr {sign})"
            );
            let positive_law = law.trim_end_matches("Member").to_string() + "Positive";
            let sign = if range {
                format!("(Litex.{positive_law} {object} {positive_output})")
            } else {
                format!("(Litex.{positive_law} {object} rfl {positive_output})")
            };
            let name = match output {
                StandardSet::NPos => "NPos",
                StandardSet::QPos => "QPos",
                StandardSet::RPos => "RPos",
                _ => unreachable!(),
            };
            format!("(Litex.in{name}_intro {object} {member} {sign})")
        } else {
            member
        };
        standard_inclusion_term(&proof.codomain, target, &object, &member)
    }
}
