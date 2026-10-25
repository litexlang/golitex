use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::prelude::*;

impl LitexToLeanCompiler {
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
        let [Obj::StandardSet(input)] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/InputCarrier",
            ));
        };
        let input_name = standard_value_constructor(input)?;
        if !signature.dom_facts.is_empty() {
            return Err(LeanCompileError::unsupported(
                "FiniteAggregate/DomainGuards",
            ));
        }
        if children.len() != 2 || requirements.len() != 3 {
            return Err(LeanCompileError::unsupported("FiniteAggregate/Stages"));
        }
        if !matches!(source_subject(&requirements[0])?, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == set.ir())
            || !matches!(source_subject(&requirements[1])?, Fact::AtomicFact(AtomicFact::SubsetFact(f)) if f.left.ir() == set.ir() && f.right == Obj::StandardSet(input.clone()))
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
        let domain = format!("(fun x hx => (Litex.FunctionSignature.oneTarget_domain .{input_name} _ _ (fun _ => True) x).mpr ⟨hx, True.intro⟩)");
        Ok(format!("(Litex.finiteAggregate {product} {} {} .{input_name} {signature_term} {} {} {} {member} {domain})", terms[0], terms[1], proofs[0], proofs[1], proofs[2]))
    }
}
