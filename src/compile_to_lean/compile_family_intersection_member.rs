use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_family_intersection_member(
        &self,
        fact: &InFact,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::FamilyIntersect(p)) = &fact.set else {
            return Err(LeanCompileError::unsupported("FamilyIntersect/Subject"));
        };
        if requirements.len() != 4
            || references.len() != 4
            || !matches!(&requirements[0], Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==p.left.ir())
            || !matches!(&requirements[1], Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==p.left.ir())
        {
            return Err(LeanCompileError::unsupported(
                "FamilyIntersect/Requirements",
            ));
        }
        for (index, requirement) in requirements[2..].iter().enumerate() {
            let Fact::ForallFact(all) = requirement else {
                return Err(LeanCompileError::unsupported("FamilyIntersect/Universal"));
            };
            if all.typed_parameters.groups.len() != 1 || all.then_facts.len() != 1 {
                return Err(LeanCompileError::unsupported(
                    "FamilyIntersect/UniversalShape",
                ));
            }
            let group = &all.typed_parameters.groups[0];
            if group.params.len() != 1
                || !matches!(&group.param_type, ParamType::Obj(o) if o.ir()==p.left.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "FamilyIntersect/UniversalDomain",
                ));
            }
            let variable = Obj::Identifier(IdentifierObj::from_bound_name(&group.params[0]));
            let valid = if index == 0 {
                all.dom_facts.is_empty()
                    && matches!(&all.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==variable.ir())
            } else {
                all.dom_facts.len() == 1
                    && matches!(&all.dom_facts[0], Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==variable.ir())
                    && matches!(&all.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fact.element.ir() && f.set.ir()==variable.ir())
            };
            if !valid {
                return Err(LeanCompileError::unsupported(
                    "FamilyIntersect/UniversalBody",
                ));
            }
        }
        let formed = self.compile_object_reference(&fact.set, position)?;
        let element = self.compile_object_reference(&fact.element, position)?;
        Ok(format!("(Litex.familyIntersectMember {formed} {element} (Litex.forallMembersOfRepresentations {} (fun _factor _hi => {} _factor _hi (Litex.isSet _factor))))", self.compile_object_reference(&p.left, position)?, references[3]))
    }
}
