use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

fn unary_call(f: &Obj, x: Obj) -> Obj {
    Obj::FnObj(FnObj {
        head: Box::new(FnObjHead::from_obj(f.clone())),
        body: vec![vec![Box::new(x)]],
    })
}

impl LitexToLeanCompiler {
    pub(super) fn compile_index_union_member(
        &self,
        fact: &InFact,
        index_id: FactId,
        fiber: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::IndexUnion(p)) = &fact.set else {
            return Err(LeanCompileError::unsupported("IndexUnion/Subject"));
        };
        let cited = self.resolve_fact(index_id, position)?;
        let Fact::AtomicFact(AtomicFact::InFact(index)) = &cited else {
            return Err(LeanCompileError::unsupported("IndexUnion/IndexCitation"));
        };
        if index.set.ir() != p.index_set.ir()
            || !matches!(source_subject(fiber)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fact.element.ir() && f.set.ir()==unary_call(&p.family_fn,index.element.clone()).ir())
        {
            return Err(LeanCompileError::unsupported("IndexUnion/FiberSubject"));
        }
        let reference = self.cited_fact_reference(index_id, position)?;
        if *reference.0 != cited {
            return Err(LeanCompileError::unsupported("IndexUnion/IndexProducer"));
        }
        let proof = self
            .compile_verify(fiber, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        Ok(format!(
            "(Litex.indexUnionMember {} {} {} {} {})",
            self.compile_object_reference(&fact.set, &complete)?,
            self.compile_object_reference(&index.element, &complete)?,
            self.compile_object_reference(&fact.element, &complete)?,
            reference.1,
            proof
        ))
    }

    pub(super) fn compile_indexed_member_theorem(
        &self,
        id: BuiltinTheoremId,
        fact: &InFact,
        requirements: &[Fact],
        references: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 2 || references.len() != 2 {
            return Err(LeanCompileError::unsupported("IndexedMember/Requirements"));
        }
        let term = self.compile_object_reference(&fact.set, position)?;
        let element = self.compile_object_reference(&fact.element, position)?;
        match (id, &fact.set) {
            (
                BuiltinTheoremId::IndexedIntersectionMember,
                Obj::SetOperator(SetOperator::IndexIntersect(p)),
            ) => {
                if !matches!(&requirements[0],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fact.element.ir() && f.set.ir()==p.ambient_set.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "IndexIntersect/AmbientMember",
                    ));
                }
                let Fact::ForallFact(all) = &requirements[1] else {
                    return Err(LeanCompileError::unsupported("IndexIntersect/Universal"));
                };
                if all.typed_parameters.groups.len() != 1
                    || !all.dom_facts.is_empty()
                    || all.then_facts.len() != 1
                {
                    return Err(LeanCompileError::unsupported(
                        "IndexIntersect/UniversalShape",
                    ));
                }
                let group = &all.typed_parameters.groups[0];
                if group.params.len() != 1
                    || !matches!(&group.param_type, ParamType::Obj(o) if o.ir()==p.index_set.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "IndexIntersect/UniversalDomain",
                    ));
                }
                let variable = Obj::Identifier(IdentifierObj::from_bound_name(&group.params[0]));
                if !matches!(&all.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fact.element.ir() && f.set.ir()==unary_call(&p.family_fn,variable).ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "IndexIntersect/UniversalFiber",
                    ));
                }
                Ok(format!("(Litex.indexIntersectMember {term} {element} {} (Litex.forallMembersOfRepresentations {} {}))",references[0], self.compile_object_reference(&p.index_set, position)?, references[1]))
            }
            (
                BuiltinTheoremId::IndexCartesianMember,
                Obj::SetOperator(SetOperator::IndexCart(p)),
            ) => {
                let Fact::AtomicFact(AtomicFact::InFact(member)) = &requirements[0] else {
                    return Err(LeanCompileError::unsupported("IndexCart/FunctionMember"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
                    return Err(LeanCompileError::unsupported("IndexCart/FunctionType"));
                };
                if member.element.ir() != fact.element.ir()
                    || signature.set_bound_parameters.groups.len() != 1
                    || signature.set_bound_parameters.groups[0].params.len() != 1
                    || signature.set_bound_parameters.groups[0].param_type.ir() != p.index_set.ir()
                    || !signature.dom_facts.is_empty()
                    || !matches!(&*signature.ret_set, Obj::SetOperator(SetOperator::FamilyUnion(f)) if f.left.ir()==p.family_set.ir())
                    || !matches!(&requirements[1],Fact::AtomicFact(AtomicFact::IsChoiceFunctionForFact(f)) if f.index.ir()==p.index_set.ir() && f.set.ir()==p.family_set.ir() && f.family.ir()==p.family_fn.ir() && f.choice.ir()==fact.element.ir())
                {
                    return Err(LeanCompileError::unsupported("IndexCart/MemberSubjects"));
                }
                Ok(format!(
                    "(Litex.indexCartMember {term} {element} {} {})",
                    references[0], references[1]
                ))
            }
            _ => Err(LeanCompileError::unsupported("IndexedMember/Constructor")),
        }
    }
}
