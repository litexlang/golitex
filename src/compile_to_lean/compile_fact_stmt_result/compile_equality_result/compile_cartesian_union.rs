use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn cart_pair(object: &Obj) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::ProductShape(ProductShape::Cart(p)) if p.args.len() == 2 => {
            Some((&p.args[0], &p.args[1]))
        }
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_cartesian_union(
        &self,
        fact: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (cart, union, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (Some((s, tu)), Obj::SetOperator(SetOperator::Union(result))) =
                (cart_pair(cart), union)
            else {
                continue;
            };
            let Obj::SetOperator(SetOperator::Union(factors)) = tu else {
                continue;
            };
            let (Some((s1, t)), Some((s2, u))) =
                (cart_pair(&result.left), cart_pair(&result.right))
            else {
                continue;
            };
            if s.ir() != s1.ir()
                || s.ir() != s2.ir()
                || t.ir() != factors.left.ir()
                || u.ir() != factors.right.ir()
            {
                continue;
            }
            let s = self.compile_object_reference(s, position)?;
            let t = self.compile_object_reference(t, position)?;
            let u = self.compile_object_reference(u, position)?;
            return Ok(format!("(let _s := {s}; let _t := {t}; let _u := {u}; (Litex.cartesianUnionValue (Litex.denote _s) (Litex.denote _t) (Litex.denote _u) (Litex.isSet _s) (Litex.isSet _t) (Litex.isSet _u)){})",if reversed {".symm"} else {""}));
        }
        Err(LeanCompileError::unsupported("CartesianUnion/ExactFactors"))
    }
}
