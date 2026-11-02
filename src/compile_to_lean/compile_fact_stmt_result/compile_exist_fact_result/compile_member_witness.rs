use crate::compile_to_lean::compile_real_set_bounds::contains_parameter;
use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_exist_member_witness(
        &self,
        fact: &PlainExistFact,
        child: &VerifyFactResult,
        equality: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [group] = fact.typed_parameters.groups.as_slice() else {
            return Err(invalid("Group"));
        };
        let ([parameter], ParamType::Obj(set)) = (group.params.as_slice(), &group.param_type)
        else {
            return Err(invalid("Binder"));
        };
        if contains_parameter(set, parameter.id) {
            return Err(invalid("CarrierCapture"));
        }
        let [QuantifierFreeFact::AtomicFact(atom)] = fact.facts.as_slice() else {
            return Err(invalid("Body"));
        };
        let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let subject = source_subject(child)?;
        let (member, reversed) = if equality {
            let AtomicFact::EqualFact(f) = atom else {
                return Err(invalid("Equality"));
            };
            let (member, reversed) = if f.left.ir() == bound.ir() {
                (&f.right, false)
            } else if f.right.ir() == bound.ir() {
                (&f.left, true)
            } else {
                return Err(invalid("EqualityBinder"));
            };
            if contains_parameter(member, parameter.id)
                || !matches!(&subject,Fact::AtomicFact(AtomicFact::InFact(p))
                    if p.element.ir()==member.ir() && p.set.ir()==set.ir())
            {
                return Err(invalid("MembershipSubject"));
            }
            (Some(member), reversed)
        } else {
            if !matches!(atom, AtomicFact::InFact(f)
                if f.element.ir()==bound.ir() && f.set.ir()==set.ir())
                || !matches!(&subject,Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f))
                    if f.set.ir()==set.ir())
            {
                return Err(invalid("NonemptySubject"));
            }
            (None, false)
        };
        let (_, proof) = self.compile_verify(child, position)?;
        let complete = SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let set = self.compile_object_reference(set, &complete)?;
        if let Some(member) = member {
            let member = self.compile_object_reference(member, &complete)?;
            let witness = format!("Litex.memberEqualityWitness {member} {set} {proof}");
            if reversed {
                Ok(format!(
                    "(by obtain ⟨x,hx,heq⟩ := {witness}; exact ⟨x,hx,heq.symm⟩)"
                ))
            } else {
                Ok(format!("({witness})"))
            }
        } else {
            Ok(format!("(Litex.nonemptyMemberWitness {set} {proof})"))
        }
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Exist/MemberWitness/{stage}"))
}
