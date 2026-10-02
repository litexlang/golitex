//! The exact integer range comprehension, including empty and reversed ranges.
use crate::ast::fact::{AtomicFact, EqualFact, QuantifierFreeFact};
use crate::ast::obj::{IdentifierObj, Obj, SetFormer, StandardSet};
use crate::parse::keywords::{GREATER, GREATER_EQUAL, LESS, LESS_EQUAL};

pub struct IntegerRangeBuilderBuiltinRuleProof { pub closed: bool }
pub(super) fn integer_range_builder(fact:&EqualFact)->Option<IntegerRangeBuilderBuiltinRuleProof> {
    for (range,builder) in [(&fact.left,&fact.right),(&fact.right,&fact.left)] {
        let (start,end,closed)=match range {
            Obj::SetFormer(SetFormer::Range(r))=>(&r.start,&r.end,false),
            Obj::SetFormer(SetFormer::ClosedRange(r))=>(&r.start,&r.end,true), _=>continue,
        };
        let Obj::SetFormer(SetFormer::SetBuilder(b))=builder else { continue; };
        if !matches!(b.param_set.as_ref(),Obj::StandardSet(StandardSet::Z)) {continue;}
        let var=Obj::Identifier(IdentifierObj::from_bound_name(&b.param_binding));
        let mut bounds=Vec::new();
        if !b.facts.iter().all(|f| collect_bounds(f,&mut bounds)) || bounds.len()!=2 {continue;}
        let lower=bounds.iter().any(|(strict,l,r)| !strict && l.ir()==start.ir() && r.ir()==var.ir());
        let upper=bounds.iter().any(|(strict,l,r)| *strict==!closed && l.ir()==var.ir() && r.ir()==end.ir());
        if lower && upper { return Some(IntegerRangeBuilderBuiltinRuleProof {closed}); }
    }
    None
}
fn atomic_bound(f:&AtomicFact)->Option<(bool,&Obj,&Obj)> {
    match f {
        AtomicFact::LessFact(f)=>Some((true,&f.left,&f.right)),
        AtomicFact::LessEqualFact(f)=>Some((false,&f.left,&f.right)),
        AtomicFact::GreaterFact(f)=>Some((true,&f.right,&f.left)),
        AtomicFact::GreaterEqualFact(f)=>Some((false,&f.right,&f.left)), _=>None,
    }
}
fn collect_bounds<'a>(f:&'a QuantifierFreeFact,out:&mut Vec<(bool,&'a Obj,&'a Obj)>)->bool {
    match f {
        QuantifierFreeFact::AtomicFact(a)=>match atomic_bound(a) {Some(b)=>{out.push(b);true},None=>false},
        QuantifierFreeFact::AndFact(a)=>a.facts.iter().all(|f|match atomic_bound(f){Some(b)=>{out.push(b);true},None=>false}),
        QuantifierFreeFact::ChainFact(c)=>{
            if c.objs.len()!=c.prop_names.len()+1 {return false;}
            for (objs,name) in c.objs.windows(2).zip(&c.prop_names) {
                let crate::ast::names::AtomicName::Plain {name}=name else {return false;};
                let (strict,l,r)=match name.as_str() {
                    LESS=>(true,&objs[0],&objs[1]), LESS_EQUAL=>(false,&objs[0],&objs[1]),
                    GREATER=>(true,&objs[1],&objs[0]), GREATER_EQUAL=>(false,&objs[1],&objs[0]), _=>return false,
                };
                out.push((strict,l,r));
            }
            true
        }, _=>false,
    }
}
