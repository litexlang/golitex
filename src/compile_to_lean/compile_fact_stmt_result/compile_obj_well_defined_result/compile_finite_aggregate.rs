use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn finite_aggregate_uses_standard_input(
        proof: &P,
    ) -> Result<bool, LeanCompileError> {
        let selected = match proof {
            P::SumOfFiniteSet(p) => &p.signature_selection,
            P::ProductOfFiniteSet(p) => &p.signature_selection,
            _ => return Err(LeanCompileError::unsupported("FiniteAggregate/Constructor")),
        };
        let signature = selected
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/SignatureCapture"))?
            .signature();
        let groups = &signature.set_bound_parameters.groups;
        if groups.len() != 1 || groups[0].params.len() != 1 {
            return Err(LeanCompileError::unsupported("FiniteAggregate/InputArity"));
        }
        Ok(signature.dom_facts.is_empty()
            && matches!(
                groups[0].param_type.as_ref(),
                Obj::StandardSet(
                    StandardSet::N
                        | StandardSet::Z
                        | StandardSet::Q
                        | StandardSet::R
                        | StandardSet::C
                )
            ))
    }

    pub(in crate::compile_to_lean) fn compile_finite_aggregate_wd(
        &self,
        object: &IteratedOperator,
        proof: &P,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (set, function, product, children, requirements, selection) = match (object, proof) {
            (IteratedOperator::SumOfFiniteSet(s), P::SumOfFiniteSet(p)) => (
                &s.set,
                &s.func,
                false,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                &p.signature_selection,
            ),
            (IteratedOperator::ProductOfFiniteSet(s), P::ProductOfFiniteSet(p)) => (
                &s.set,
                &s.func,
                true,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
                &p.signature_selection,
            ),
            _ => return Err(LeanCompileError::unsupported("FiniteAggregate/Constructor")),
        };
        let selection = selection
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("FiniteAggregate/SignatureCapture"))?;
        let signature = selection.signature();
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |_| g.param_type.as_ref()))
            .collect::<Vec<_>>();
        let [input] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/InputCarrier",
            ));
        };
        if children.len() != 2 || requirements.len() < 3 {
            return Err(LeanCompileError::unsupported("FiniteAggregate/Stages"));
        }
        super::compile_finite_guard::validate_finite_guards(signature, set, &requirements[3..])?;
        if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == set.ir())
            || !matches!(source_subject(&requirements[1])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == set.ir() && f.right.ir() == input.ir())
            || !matches!(source_subject(&requirements[2])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == signature.ret_set.ir() && f.right == Obj::StandardSet(StandardSet::C))
        {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/Requirements",
            ));
        }
        let mut terms = Vec::new();
        for (index, object) in [set, function].iter().enumerate() {
            ensure_object(object, &children[index])?;
            terms.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let formed = SourcePosition {
            before: 2,
            ..*position
        };
        let member = self.compile_selected_signature(function, selection, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        if Self::finite_aggregate_uses_standard_input(proof)? {
            let mut proofs = Vec::new();
            for (index, proof) in requirements.iter().enumerate() {
                proofs.push(self.compile_wd_requirement(
                    proof,
                    &SourcePosition {
                        before: 2 + index,
                        ..*position
                    },
                )?);
            }
            let Obj::StandardSet(input) = input else {
                unreachable!()
            };
            let input_name = standard_value_constructor(input)?;
            let domain = format!(
                "(fun x hx => (Litex.FunctionSignature.oneTarget_domain .{input_name} _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)"
            );
            return Ok(format!(
                "(Litex.finiteAggregate {product} {} {} .{input_name} {signature_term} {} {} {} {member} {domain})",
                terms[0], terms[1], proofs[0], proofs[1], proofs[2]
            ));
        }
        let mut proofs = Vec::new();
        let mut bindings = String::new();
        for (index, source) in requirements.iter().enumerate() {
            let prior = SourcePosition {
                before: 2 + index,
                ..*position
            };
            let local = SourcePosition::new(Some(&prior), SourceOwner::Term, 0);
            let (proposition, proof) = self.compile_verify(source, &local)?;
            let reference = format!("h_{}", source_subject(source)?.fact_id().value());
            bindings.push_str(&format!("let {reference} : {proposition} := {proof};\n"));
            proofs.push(reference);
        }
        let guarded = !signature.dom_facts.is_empty();
        // Explicit guards cover the finite index set, not every member of the
        // function's carrier. The original carrier inclusion is used below.
        let (input_term, subset) = if guarded {
            (terms[0].clone(), format!("(Litex.subsetRefl {})", terms[0]))
        } else {
            (
                self.compile_object_reference(input, &formed)?,
                proofs[1].clone(),
            )
        };
        let guard_proof = self.compile_finite_guard(
            signature,
            set,
            &terms[0],
            &proofs[3..],
            &formed,
            &mut bindings,
        )?;
        let membership = if guarded {
            format!("({} i hi)", proofs[1])
        } else {
            "hi".into()
        };
        let (membership, guard_proof) = self.compile_unary_function_domain_certificates(
            signature,
            "(Litex.semanticObject (M := M) i (M.member_isSet hi))",
            membership,
            &guard_proof,
            &formed,
        )?;
        let (domain, domain_set) =
            self.compile_function_semantic_base_domain(signature, &formed)?;
        let output = self.compile_object_reference(&signature.ret_set, &formed)?;
        let guard = self.compile_function_guard_template(signature, &formed)?;
        let cover = format!(
            "(fun i hi => (Litex.FunctionSignature.withGuard_domain {domain} (Litex.denote {output}) {domain_set} (Litex.isSet {output}) {guard} i).mpr ⟨{membership}, {guard_proof}⟩)"
        );
        Ok(format!(
            "({bindings}Litex.finiteAggregateOn {product} {} {} {input_term} {signature_term} {} {subset} {} {member} {cover})",
            terms[0], terms[1], proofs[0], proofs[2]
        ))
    }
}
