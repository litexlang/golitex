use crate::prelude::*;

impl FnObjHead {
    pub fn contains_forall_free_param_obj(&self) -> bool {
        let head_obj: Obj = self.clone().into();
        head_obj.contains_forall_free_param_obj()
    }
}

impl Obj {
    pub fn contains_forall_free_param_obj(&self) -> bool {
        match self {
            Obj::Atom(AtomObj::Forall(_)) => true,
            Obj::Atom(_) | Obj::Number(_) | Obj::StandardSet(_) => false,
            Obj::FnObj(x) => {
                x.head.contains_forall_free_param_obj()
                    || x.body
                        .iter()
                        .flatten()
                        .any(|obj| obj.contains_forall_free_param_obj())
            }
            Obj::Add(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Sub(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Mul(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Div(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Mod(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Pow(x) => contains_forall_free_param_obj_in_pair(&x.base, &x.exponent),
            Obj::Abs(x) => x.arg.contains_forall_free_param_obj(),
            Obj::Sqrt(x) => x.arg.contains_forall_free_param_obj(),
            Obj::Log(x) => contains_forall_free_param_obj_in_pair(&x.base, &x.arg),
            Obj::Max(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Min(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Union(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Intersect(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::SetMinus(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::SetDiff(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::Cup(x) => x.left.contains_forall_free_param_obj(),
            Obj::Cap(x) => x.left.contains_forall_free_param_obj(),
            Obj::PowerSet(x) => x.set.contains_forall_free_param_obj(),
            Obj::ListSet(x) => x
                .list
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::SetBuilder(x) => {
                x.param_set.contains_forall_free_param_obj()
                    || or_and_chain_facts_contain_forall_free_param_obj(&x.facts)
            }
            Obj::FnSet(x) => fn_set_body_contains_forall_free_param_obj(&x.body),
            Obj::AnonymousFn(x) => {
                fn_set_body_contains_forall_free_param_obj(&x.body)
                    || x.equal_to.contains_forall_free_param_obj()
            }
            Obj::Cart(x) => x
                .args
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::CartDim(x) => x.set.contains_forall_free_param_obj(),
            Obj::Proj(x) => contains_forall_free_param_obj_in_pair(&x.set, &x.dim),
            Obj::TupleDim(x) => x.arg.contains_forall_free_param_obj(),
            Obj::Tuple(x) => x
                .args
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::Count(x) => x.set.contains_forall_free_param_obj(),
            Obj::FnRange(x) => x.function.contains_forall_free_param_obj(),
            Obj::FnRangeOn(x) => {
                x.function.contains_forall_free_param_obj()
                    || x.set.contains_forall_free_param_obj()
            }
            Obj::Sum(x) => {
                x.start.contains_forall_free_param_obj()
                    || x.end.contains_forall_free_param_obj()
                    || x.func.contains_forall_free_param_obj()
            }
            Obj::SumOfFiniteSet(x) => {
                x.set.contains_forall_free_param_obj() || x.func.contains_forall_free_param_obj()
            }
            Obj::Product(x) => {
                x.start.contains_forall_free_param_obj()
                    || x.end.contains_forall_free_param_obj()
                    || x.func.contains_forall_free_param_obj()
            }
            Obj::ProductOfFiniteSet(x) => {
                x.set.contains_forall_free_param_obj() || x.func.contains_forall_free_param_obj()
            }
            Obj::Range(x) => contains_forall_free_param_obj_in_pair(&x.start, &x.end),
            Obj::ClosedRange(x) => contains_forall_free_param_obj_in_pair(&x.start, &x.end),
            Obj::FiniteSeqSet(x) => contains_forall_free_param_obj_in_pair(&x.set, &x.n),
            Obj::SeqSet(x) => x.set.contains_forall_free_param_obj(),
            Obj::FiniteSeqListObj(x) => x
                .objs
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::ObjAtIndex(x) => contains_forall_free_param_obj_in_pair(&x.obj, &x.index),
            Obj::MatrixSet(x) => {
                x.set.contains_forall_free_param_obj()
                    || x.row_len.contains_forall_free_param_obj()
                    || x.col_len.contains_forall_free_param_obj()
            }
            Obj::MatrixListObj(x) => x
                .rows
                .iter()
                .flatten()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::MatrixAdd(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::MatrixSub(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::MatrixMul(x) => contains_forall_free_param_obj_in_pair(&x.left, &x.right),
            Obj::MatrixScalarMul(x) => contains_forall_free_param_obj_in_pair(&x.scalar, &x.matrix),
            Obj::MatrixPow(x) => contains_forall_free_param_obj_in_pair(&x.base, &x.exponent),
            Obj::StructObj(x) => x
                .params
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                x.struct_obj
                    .params
                    .iter()
                    .any(|obj| obj.contains_forall_free_param_obj())
                    || x.obj.contains_forall_free_param_obj()
            }
            Obj::InstantiatedTemplateObj(x) => x
                .args
                .iter()
                .any(|obj| obj.contains_forall_free_param_obj()),
            Obj::OneSideInfinityIntervalObj(x) => x.start().contains_forall_free_param_obj(),
            Obj::IntervalObj(x) => {
                x.start().contains_forall_free_param_obj()
                    || x.end().contains_forall_free_param_obj()
            }
        }
    }
}

fn contains_forall_free_param_obj_in_pair(left: &Obj, right: &Obj) -> bool {
    left.contains_forall_free_param_obj() || right.contains_forall_free_param_obj()
}

fn fn_set_body_contains_forall_free_param_obj(body: &FnSetBody) -> bool {
    body.params_def_with_set
        .iter()
        .any(|group| group.param_type.contains_forall_free_param_obj())
        || or_and_chain_facts_contain_forall_free_param_obj(&body.dom_facts)
        || body.ret_set.contains_forall_free_param_obj()
}

fn or_and_chain_facts_contain_forall_free_param_obj(facts: &[OrAndChainAtomicFact]) -> bool {
    facts.iter().any(|fact| {
        fact.get_args_from_fact()
            .iter()
            .any(|arg| arg.contains_forall_free_param_obj())
    })
}
