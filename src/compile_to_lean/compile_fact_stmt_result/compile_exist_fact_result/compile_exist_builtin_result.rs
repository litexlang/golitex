use super::helper::real_comparison_witness;
use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchProofByBuiltinRule;
use crate::prelude::*;
use std::collections::HashSet;

impl LitexToLeanCompiler {
    pub(super) fn compile_exist_builtin_result(
        &self,
        fact: &PlainExistFact,
        proof: &ExistShapedFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            ExistShapedFactSearchProofByBuiltinRule::RealLineComparisonWitness(proof) => self
                .compile_exist_real_comparison_witness(
                    fact,
                    &proof.requirement_facts,
                    &proof.proof_of_requirement_facts,
                    position,
                ),
            _ => Err(LeanCompileError::unsupported("Exist/BuiltinRule")),
        }
    }

    // Replay exactly the selected real-line rule: one real binder against a
    // checked free real, or two distinct real binders. This does not substitute
    // the later known-exist search route for the original builtin evidence.
    fn compile_exist_real_comparison_witness(
        &self,
        fact: &PlainExistFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if fact.typed_parameters.groups.iter().any(|group| {
            !matches!(
                group.param_type,
                ParamType::Obj(Obj::StandardSet(StandardSet::R))
            )
        }) {
            return Err(LeanCompileError::unsupported(
                "Exist/RealLineComparisonShape",
            ));
        }
        let parameters: Vec<_> = fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect();
        let [QuantifierFreeFact::AtomicFact(atom)] = fact.facts.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Exist/RealLineComparisonShape",
            ));
        };
        // Normalize > and >= to the operand order of Litex.Lt and Litex.Le.
        let (left, right, relation) = match atom {
            AtomicFact::EqualFact(f) => (&f.left, &f.right, "eq"),
            AtomicFact::NotEqualFact(f) => (&f.left, &f.right, "ne"),
            AtomicFact::LessFact(f) => (&f.left, &f.right, "lt"),
            AtomicFact::GreaterFact(f) => (&f.right, &f.left, "lt"),
            AtomicFact::LessEqualFact(f) => (&f.left, &f.right, "le"),
            AtomicFact::GreaterEqualFact(f) => (&f.right, &f.left, "le"),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Exist/RealLineComparisonShape",
                ))
            }
        };
        if let [first, second] = parameters.as_slice() {
            let first = Obj::Identifier(IdentifierObj::from_bound_name(first));
            let second = Obj::Identifier(IdentifierObj::from_bound_name(second));
            if first.ir() == second.ir()
                || !((left.ir() == first.ir() && right.ir() == second.ir())
                    || (right.ir() == first.ir() && left.ir() == second.ir()))
            {
                return Err(LeanCompileError::unsupported(
                    "Exist/RealLineComparisonSubject",
                ));
            }
            if !requirements.is_empty() || !children.is_empty() {
                return Err(LeanCompileError::unsupported(
                    "Exist/RealLineComparisonRequirements",
                ));
            }
            return Ok(real_comparison_witness(
                "(Litex.semanticObject (M.number (0 : ℂ)) (Litex.isSet (Litex.number (M := M) 0)))",
                "(Litex.NativeBridge.numberInR (M := M) 0)",
                relation,
                left.ir() == second.ir(),
                true,
            ));
        }
        let [parameter] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Exist/RealLineComparisonShape",
            ));
        };
        let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let operand = if left.ir() == bound.ir() {
            right
        } else if right.ir() == bound.ir() {
            left
        } else {
            return Err(LeanCompileError::unsupported(
                "Exist/RealLineComparisonSubject",
            ));
        };
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(operand, &HashSet::new(), &mut free);
        if free.contains(&parameter.id) {
            return Err(LeanCompileError::new(
                "Exist/RealLineComparisonSubject",
                "The selected free endpoint depends on the existential parameter.",
            ));
        }
        let ([requirement], [child]) = (requirements, children) else {
            return Err(LeanCompileError::new(
                "Exist/RealLineComparisonRequirements",
                "The selected one-real witness requires its one ordered membership and verification.",
            ));
        };
        if !matches!(requirement,
            Fact::AtomicFact(AtomicFact::InFact(member))
                if member.element.ir() == operand.ir()
                    && matches!(member.set, Obj::StandardSet(StandardSet::R)))
        {
            return Err(LeanCompileError::new(
                "Exist/RealLineComparisonMembership",
                "The original requirement is not membership of this free endpoint in R.",
            ));
        }
        let checked = source_subject(child)?;
        if checked != *requirement || checked.fact_id() != requirement.fact_id() {
            return Err(LeanCompileError::new(
                "Exist/RealLineComparisonChild",
                "The selected child does not prove the exact original membership requirement.",
            ));
        }
        let membership = self.compile_verify(child, position)?;
        let complete = SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let value = self.compile_object_reference(operand, &complete)?;
        if relation == "eq" {
            return Ok(format!(
                "⟨Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}), {}, (by rfl)⟩",
                membership.1,
            ));
        }
        Ok(real_comparison_witness(
            &value,
            &membership.1,
            relation,
            left.ir() == bound.ir(),
            false,
        ))
    }
}
