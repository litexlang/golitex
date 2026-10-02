//! Display evaluation of checked finite literal objects. No facts are stored.
use super::evaluate_obj::evaluate_obj;
use super::helper::ActiveAlgoCalls;
use super::result::ExecEvalStmtFailed;
use crate::ast::obj::{ArithmeticOperator, FiniteSetStat, Literal, Number, Obj, ProductShape, SetFormer, Sub, Tuple};
use crate::rational_expression::exact_rational::EvalRational;
use crate::runtime::{Runtime, RuntimeResult};

pub(super) fn evaluate_finite_object(runtime:&mut Runtime,obj:&Obj,depth:usize,context:&mut ActiveAlgoCalls)
    -> RuntimeResult<Result<Obj,ExecEvalStmtFailed>> {
    match obj {
        Obj::ProductShape(ProductShape::Tuple(tuple))=>{
            let mut args=Vec::new();
            for arg in &tuple.args {
                match evaluate_obj(runtime,arg,depth+1,context)? {Ok(v)=>args.push(Box::new(v)),Err(e)=>return Ok(Err(e))}
            }
            Ok(Ok(Obj::ProductShape(ProductShape::Tuple(Tuple {args}))))
        },
        Obj::ProductShape(ProductShape::TupleDim(d))=>{
            if let Obj::ProductShape(ProductShape::Tuple(t))=d.arg.as_ref() {return Ok(Ok(number(t.args.len())));}
            Ok(Err(ExecEvalStmtFailed::UnsupportedExpression))
        },
        Obj::ProductShape(ProductShape::ObjAtIndex(at))=>{
            let index=match evaluate_obj(runtime,&at.index,depth+1,context)? {Ok(v)=>v,Err(e)=>return Ok(Err(e))};
            let Some(i)=EvalRational::from_obj(&index).and_then(|v|v.to_i128_if_integer()).and_then(|i|usize::try_from(i).ok()) else {
                return Ok(Err(ExecEvalStmtFailed::EvaluationFailed));
            };
            let tuple=match at.obj.as_ref() {
                Obj::ProductShape(ProductShape::Tuple(t))=>t.clone(),
                other=>match evaluate_obj(runtime,other,depth+1,context)? {
                    Ok(Obj::ProductShape(ProductShape::Tuple(t)))=>t,Ok(_)=>return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression)),Err(e)=>return Ok(Err(e)),
                },
            };
            let Some(component)=i.checked_sub(1).and_then(|i|tuple.args.get(i)) else {return Ok(Err(ExecEvalStmtFailed::EvaluationFailed));};
            evaluate_obj(runtime,component,depth+1,context)
        },
        Obj::FiniteSetStat(stat)=>{
            let (set,max)=match stat {
                FiniteSetStat::FiniteSetSize(s)=>(&s.set,None),
                FiniteSetStat::FiniteSetMax(s)=>(&s.set,Some(true)),
                FiniteSetStat::FiniteSetMin(s)=>(&s.set,Some(false)),
            };
            let Obj::SetFormer(SetFormer::ListSet(list))=set.as_ref() else {return Ok(Err(ExecEvalStmtFailed::UnsupportedExpression));};
            // Source WD proves mutual distinctness; count that exact enumeration.
            let Some(max)=max else {return Ok(Ok(number(list.list.len())));};
            let mut best=None;
            for raw in &list.list {
                let value=match evaluate_obj(runtime,raw,depth+1,context)? {Ok(v)=>v,Err(e)=>return Ok(Err(e))};
                let Some(current)=&best else {best=Some(value);continue;};
                let difference=Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {left:Box::new(value.clone()),right:Box::new(current.clone())}));
                let Some(normal)=EvalRational::from_obj(&difference).map(|r|r.to_obj()) else {return Ok(Err(ExecEvalStmtFailed::EvaluationFailed));};
                // EvalRational normalizes denominator positive, so the sign is
                // determined exactly by its integer numerator, without floats.
                let numerator=match &normal {Obj::ArithmeticOperator(ArithmeticOperator::Div(d))=>d.left.as_ref(),other=>other};
                let Some(n)=EvalRational::from_obj(numerator).and_then(|r|r.to_i128_if_integer()) else {return Ok(Err(ExecEvalStmtFailed::EvaluationFailed));};
                if (max && n>0) || (!max && n<0) {best=Some(value);}
            }
            Ok(best.ok_or(ExecEvalStmtFailed::EvaluationFailed))
        }, _=>Ok(Err(ExecEvalStmtFailed::UnsupportedExpression)),
    }
}
fn number(n:usize)->Obj {Obj::Literal(Literal::Number(Number::new(n.to_string())))}
