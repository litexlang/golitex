use crate::compile_to_lean::compile_real_set_bounds::contains_parameter;
use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_exist_reciprocal_witness(
        &self,
        fact: &PlainExistFact,
        child: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let parameter = witness_parameter(fact, StandardSet::NPos)?;
        let [QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(bound))] = fact.facts.as_slice()
        else {
            return Err(invalid("ReciprocalBody"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = &bound.left else {
            return Err(invalid("ReciprocalQuotient"));
        };
        let witness = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        if !matches!(quotient.left.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
            || quotient.right.ir() != witness.ir()
            || contains_parameter(&bound.right, parameter.id)
            || !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==bound.right.ir() && f.set==Obj::StandardSet(StandardSet::RPos))
        {
            return Err(invalid("ReciprocalSubject"));
        }
        let proof = self.compile_verify(child, position)?.1;
        let complete = SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let epsilon = self.compile_object_reference(&bound.right, &complete)?;
        // The lemma states Lt's denotation predicate. The original existential
        // WD still forms the guarded division; no replacement WD proof is added.
        Ok(format!(
            "(Litex.reciprocalNaturalWitness {epsilon} {proof})"
        ))
    }

    pub(super) fn compile_exist_midpoint_witness(
        &self,
        fact: &PlainExistFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let parameter = witness_parameter(fact, StandardSet::R)?;
        let [QuantifierFreeFact::ChainFact(chain)] = fact.facts.as_slice() else {
            return Err(invalid("MidpointBody"));
        };
        let witness = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        if chain.objs.len() != 3
            || chain.prop_names.len() != 2
            || chain
                .prop_names
                .iter()
                .any(|p| !matches!(p,AtomicName::Plain{name} if name=="<"))
            || chain.objs[1].ir() != witness.ir()
            || contains_parameter(&chain.objs[0], parameter.id)
            || contains_parameter(&chain.objs[2], parameter.id)
            || requirements.len() != 3
            || children.len() != 3
        {
            return Err(invalid("MidpointShape"));
        }
        let (left, right) = (&chain.objs[0], &chain.objs[2]);
        for (requirement, endpoint) in requirements[..2].iter().zip([left, right]) {
            if !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==endpoint.ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("MidpointRealPremise"));
            }
        }
        if !matches!(&requirements[2],Fact::AtomicFact(AtomicFact::LessFact(f))
            if f.left.ir()==left.ir() && f.right.ir()==right.ir())
        {
            return Err(invalid("MidpointOrderPremise"));
        }
        let mut proofs = Vec::new();
        for (requirement, child) in requirements.iter().zip(children) {
            if source_subject(child)? != *requirement {
                return Err(invalid("MidpointPremiseCapture"));
            }
            // These original verifications do not publish stores between children.
            proofs.push(self.compile_verify(child, position)?.1);
        }
        let left = self.compile_object_reference(
            left,
            &SourcePosition::new(
                Some(position),
                SourceOwner::Verify(&children[0]),
                usize::MAX,
            ),
        )?;
        let right = self.compile_object_reference(
            right,
            &SourcePosition::new(
                Some(position),
                SourceOwner::Verify(&children[1]),
                usize::MAX,
            ),
        )?;
        Ok(format!(
            "(Litex.realMidpointWitness {left} {right} {} {} {})",
            proofs[0], proofs[1], proofs[2]
        ))
    }
}

fn witness_parameter(
    fact: &PlainExistFact,
    carrier: StandardSet,
) -> Result<&BoundName, LeanCompileError> {
    let [group] = fact.typed_parameters.groups.as_slice() else {
        return Err(invalid("WitnessGroup"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("WitnessCount"));
    };
    if group.param_type != ParamType::Obj(Obj::StandardSet(carrier)) {
        return Err(invalid("WitnessCarrier"));
    }
    Ok(parameter)
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Exist/DenseOrder/{stage}"))
}
