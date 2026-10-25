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
        let [Obj::StandardSet(input)] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported("RangeAggregate/InputCarrier"));
        };
        if !matches!(
            input,
            StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C
        ) || !signature.dom_facts.is_empty()
        {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/DomainCoverage",
            ));
        }
        if children.len() != 3 || requirements.len() != 4 {
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
        let formed = SourcePosition {
            before: 3,
            ..*position
        };
        let member = self.compile_selected_signature(function, selection, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        let mut proofs = Vec::new();
        for (index, evidence) in requirements.iter().enumerate() {
            proofs.push(self.compile_wd_requirement(
                evidence,
                &SourcePosition {
                    before: 3 + index,
                    ..*position
                },
            )?);
        }
        let input = standard_value_constructor(input)?;
        // The recorded unguarded Z/Q/R/C domain includes every integer. Other
        // domains must replay their own original coverage evidence.
        let domain =
            format!("(fun k _ _ => Litex.unguardedIntegerDomain .{input} _ _ (by decide) k)");
        Ok(format!("(Litex.rangeAggregate {product} {} {} {} {signature_term} {} {} {} {member} {} {domain})", terms[0], terms[1], terms[2], proofs[0], proofs[1], proofs[2], proofs[3]))
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
        if proof.iterand_return_set != Obj::StandardSet(proof.codomain.clone()) {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/RefinedOutput",
            ));
        }
        let object = self.compile_object_reference(&fact.element, position)?;
        let checked = position.with_visible_wd(&fact.element, &mut |wd, _| {
            let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IteratedOperator(p),
                ..
            } = wd
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
                    ))
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
            Ok(())
        })?;
        if checked.is_none() {
            return Err(LeanCompileError::unsupported(
                "RangeAggregate/MemberProducer",
            ));
        }
        let carrier = standard_value_constructor(&proof.codomain)?;
        let law = match &fact.element {
            Obj::IteratedOperator(
                IteratedOperator::SumOfFiniteSet(_) | IteratedOperator::ProductOfFiniteSet(_),
            ) => "finiteAggregateMember",
            _ => "rangeAggregateMember",
        };
        let member = format!("(Litex.{law} {object} .{carrier} rfl)");
        standard_inclusion_term(&proof.codomain, target, &object, &member)
    }
}
