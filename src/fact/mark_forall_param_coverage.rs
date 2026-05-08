use crate::prelude::*;
use std::collections::HashMap;

// coverage_by_forall_param: one entry per forall parameter, values start false.
// Walk the clause: Identifier base name appears and is a key -> set true.

fn mark_forall_param_name_if_tracked(
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
    name: &IdentifierName,
) {
    match coverage_by_forall_param.get_mut(name) {
        Some(is_mentioned) => {
            *is_mentioned = true;
        }
        None => {}
    }
}

fn mark_forall_param_coverage_in_param_type(
    param_type: &ParamType,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match param_type {
        ParamType::Obj(obj) => {
            mark_forall_param_coverage_in_obj(obj, coverage_by_forall_param);
        }
        ParamType::Struct(struct_ty) => {
            for arg in struct_ty.args.iter() {
                mark_forall_param_coverage_in_obj(arg, coverage_by_forall_param);
            }
        }
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {}
    }
}

fn mark_forall_param_coverage_in_fn_obj_head(
    head: &FnObjHead,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match head {
        FnObjHead::Identifier(i) => {
            mark_forall_param_coverage_in_obj(
                &Obj::Atom(AtomObj::Identifier(i.clone())),
                coverage_by_forall_param,
            );
        }
        FnObjHead::IdentifierWithMod(m) => {
            mark_forall_param_coverage_in_obj(
                &Obj::Atom(AtomObj::IdentifierWithMod(m.clone())),
                coverage_by_forall_param,
            );
        }
        FnObjHead::Forall(p) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        FnObjHead::DefHeader(_)
        | FnObjHead::Exist(_)
        | FnObjHead::SetBuilder(_)
        | FnObjHead::FnSet(_)
        | FnObjHead::Induc(_)
        | FnObjHead::DefAlgo(_) => {}
        FnObjHead::AnonymousFnLiteral(a) => {
            mark_forall_param_coverage_in_obj(
                &Obj::AnonymousFn((**a).clone()),
                coverage_by_forall_param,
            );
        }
    }
}

fn mark_forall_param_coverage_in_obj(
    obj: &Obj,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match obj {
        Obj::Atom(AtomObj::Identifier(identifier)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &identifier.name);
        }
        Obj::Atom(AtomObj::IdentifierWithMod(_)) => {}
        Obj::FnObj(fn_obj) => {
            mark_forall_param_coverage_in_fn_obj_head(
                fn_obj.head.as_ref(),
                coverage_by_forall_param,
            );
            for group in fn_obj.body.iter() {
                for boxed_obj in group.iter() {
                    mark_forall_param_coverage_in_obj(boxed_obj.as_ref(), coverage_by_forall_param);
                }
            }
        }
        Obj::Number(_) | Obj::StandardSet(_) => {}
        Obj::Add(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Sub(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Mul(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Div(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Mod(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Pow(binary) => {
            mark_forall_param_coverage_in_obj(binary.base.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.exponent.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixAdd(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixSub(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixMul(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixScalarMul(binary) => {
            mark_forall_param_coverage_in_obj(binary.scalar.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.matrix.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixPow(binary) => {
            mark_forall_param_coverage_in_obj(binary.base.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.exponent.as_ref(), coverage_by_forall_param);
        }
        Obj::Abs(unary) => {
            mark_forall_param_coverage_in_obj(unary.arg.as_ref(), coverage_by_forall_param);
        }
        Obj::Log(binary) => {
            mark_forall_param_coverage_in_obj(binary.base.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.arg.as_ref(), coverage_by_forall_param);
        }
        Obj::Max(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Min(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Union(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Intersect(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::SetMinus(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::SetDiff(binary) => {
            mark_forall_param_coverage_in_obj(binary.left.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(binary.right.as_ref(), coverage_by_forall_param);
        }
        Obj::Cup(unary) => {
            mark_forall_param_coverage_in_obj(unary.left.as_ref(), coverage_by_forall_param);
        }
        Obj::Cap(unary) => {
            mark_forall_param_coverage_in_obj(unary.left.as_ref(), coverage_by_forall_param);
        }
        Obj::PowerSet(unary) => {
            mark_forall_param_coverage_in_obj(unary.set.as_ref(), coverage_by_forall_param);
        }
        Obj::ListSet(list_set) => {
            for boxed_obj in list_set.list.iter() {
                mark_forall_param_coverage_in_obj(boxed_obj.as_ref(), coverage_by_forall_param);
            }
        }
        Obj::SetBuilder(set_builder) => {
            mark_forall_param_coverage_in_obj(
                set_builder.param_set.as_ref(),
                coverage_by_forall_param,
            );
            for inner_fact in set_builder.facts.iter() {
                mark_forall_param_coverage_in_or_and_chain_atomic_fact(
                    inner_fact,
                    coverage_by_forall_param,
                );
            }
        }
        Obj::FnSet(fn_set) => {
            for param_def_with_set in fn_set.body.params_def_with_set.iter() {
                mark_forall_param_coverage_in_obj(
                    &param_def_with_set.set,
                    coverage_by_forall_param,
                );
            }
            for dom_fact in fn_set.body.dom_facts.iter() {
                mark_forall_param_coverage_in_or_and_chain_atomic_fact(
                    dom_fact,
                    coverage_by_forall_param,
                );
            }
            mark_forall_param_coverage_in_obj(
                fn_set.body.ret_set.as_ref(),
                coverage_by_forall_param,
            );
        }
        Obj::AnonymousFn(anon) => {
            for param_def_with_set in anon.body.params_def_with_set.iter() {
                mark_forall_param_coverage_in_obj(
                    &param_def_with_set.set,
                    coverage_by_forall_param,
                );
            }
            for dom_fact in anon.body.dom_facts.iter() {
                mark_forall_param_coverage_in_or_and_chain_atomic_fact(
                    dom_fact,
                    coverage_by_forall_param,
                );
            }
            mark_forall_param_coverage_in_obj(anon.body.ret_set.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(anon.equal_to.as_ref(), coverage_by_forall_param);
        }
        Obj::Cart(cart) => {
            for boxed_arg in cart.args.iter() {
                mark_forall_param_coverage_in_obj(boxed_arg.as_ref(), coverage_by_forall_param);
            }
        }
        Obj::CartDim(cart_dim) => {
            mark_forall_param_coverage_in_obj(cart_dim.set.as_ref(), coverage_by_forall_param);
        }
        Obj::Proj(proj) => {
            mark_forall_param_coverage_in_obj(proj.set.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(proj.dim.as_ref(), coverage_by_forall_param);
        }
        Obj::TupleDim(tuple_dim) => {
            mark_forall_param_coverage_in_obj(tuple_dim.arg.as_ref(), coverage_by_forall_param);
        }
        Obj::Tuple(tuple_obj) => {
            for boxed_arg in tuple_obj.args.iter() {
                mark_forall_param_coverage_in_obj(boxed_arg.as_ref(), coverage_by_forall_param);
            }
        }
        Obj::Count(count) => {
            mark_forall_param_coverage_in_obj(count.set.as_ref(), coverage_by_forall_param);
        }
        Obj::Sum(s) => {
            mark_forall_param_coverage_in_obj(s.start.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(s.end.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(s.func.as_ref(), coverage_by_forall_param);
        }
        Obj::Product(s) => {
            mark_forall_param_coverage_in_obj(s.start.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(s.end.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(s.func.as_ref(), coverage_by_forall_param);
        }
        Obj::Range(range) => {
            mark_forall_param_coverage_in_obj(range.start.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(range.end.as_ref(), coverage_by_forall_param);
        }
        Obj::ClosedRange(closed_range) => {
            mark_forall_param_coverage_in_obj(
                closed_range.start.as_ref(),
                coverage_by_forall_param,
            );
            mark_forall_param_coverage_in_obj(closed_range.end.as_ref(), coverage_by_forall_param);
        }
        Obj::FiniteSeqSet(fs) => {
            mark_forall_param_coverage_in_obj(fs.set.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(fs.n.as_ref(), coverage_by_forall_param);
        }
        Obj::SeqSet(ss) => {
            mark_forall_param_coverage_in_obj(ss.set.as_ref(), coverage_by_forall_param);
        }
        Obj::FiniteSeqListObj(v) => {
            for o in v.objs.iter() {
                mark_forall_param_coverage_in_obj(o.as_ref(), coverage_by_forall_param);
            }
        }
        Obj::MatrixSet(ms) => {
            mark_forall_param_coverage_in_obj(ms.set.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(ms.row_len.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(ms.col_len.as_ref(), coverage_by_forall_param);
        }
        Obj::MatrixListObj(v) => {
            for row in v.rows.iter() {
                for o in row.iter() {
                    mark_forall_param_coverage_in_obj(o.as_ref(), coverage_by_forall_param);
                }
            }
        }
        Obj::Choose(choose) => {
            mark_forall_param_coverage_in_obj(choose.set.as_ref(), coverage_by_forall_param);
        }
        Obj::ObjAtIndex(obj_at_index) => {
            mark_forall_param_coverage_in_obj(obj_at_index.obj.as_ref(), coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(
                obj_at_index.index.as_ref(),
                coverage_by_forall_param,
            );
        }
        Obj::FamilyObj(family) => {
            for o in family.params.iter() {
                mark_forall_param_coverage_in_obj(o, coverage_by_forall_param);
            }
        }
        Obj::FieldAccess(field_access) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &field_access.left);
        }
        Obj::Atom(AtomObj::Forall(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::Def(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::Exist(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::SetBuilder(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::FnSet(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::Induc(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::DefAlgo(p)) => {
            mark_forall_param_name_if_tracked(coverage_by_forall_param, &p.name);
        }
        Obj::Atom(AtomObj::DefStructField(_)) => {}
    }
}

fn mark_forall_param_coverage_in_atomic_fact(
    atomic_fact: &AtomicFact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match atomic_fact {
        AtomicFact::NormalAtomicFact(fact) => {
            for body_obj in fact.body.iter() {
                mark_forall_param_coverage_in_obj(body_obj, coverage_by_forall_param);
            }
        }
        AtomicFact::NotNormalAtomicFact(fact) => {
            for body_obj in fact.body.iter() {
                mark_forall_param_coverage_in_obj(body_obj, coverage_by_forall_param);
            }
        }
        AtomicFact::EqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::LessFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::GreaterFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::LessEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::GreaterEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotLessFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotGreaterFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotLessEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::IsSetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotIsSetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::IsNonemptySetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotIsNonemptySetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::IsFiniteSetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotIsFiniteSetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::InFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.element, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotInFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.element, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::IsCartFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotIsCartFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::IsTupleFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::NotIsTupleFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::SubsetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::SupersetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotSubsetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::NotSupersetFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
        AtomicFact::RestrictFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.obj, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(
                &fact.obj_can_restrict_to_fn_set,
                coverage_by_forall_param,
            );
        }
        AtomicFact::NotRestrictFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.obj, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(
                &fact.obj_cannot_restrict_to_fn_set,
                coverage_by_forall_param,
            );
        }
        AtomicFact::FnEqualInFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.set, coverage_by_forall_param);
        }
        AtomicFact::FnEqualFact(fact) => {
            mark_forall_param_coverage_in_obj(&fact.left, coverage_by_forall_param);
            mark_forall_param_coverage_in_obj(&fact.right, coverage_by_forall_param);
        }
    }
}

fn mark_forall_param_coverage_in_and_chain_atomic_fact(
    parent_fact: &AndChainAtomicFact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match parent_fact {
        AndChainAtomicFact::AtomicFact(atomic_fact) => {
            mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
        }
        AndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                mark_forall_param_coverage_in_atomic_fact(inner_atomic, coverage_by_forall_param);
            }
        }
        AndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                mark_forall_param_coverage_in_obj(chain_obj, coverage_by_forall_param);
            }
        }
    }
}

fn mark_forall_param_coverage_in_or_and_chain_atomic_fact(
    parent_fact: &OrAndChainAtomicFact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match parent_fact {
        OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
        }
        OrAndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                mark_forall_param_coverage_in_atomic_fact(inner_atomic, coverage_by_forall_param);
            }
        }
        OrAndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                mark_forall_param_coverage_in_obj(chain_obj, coverage_by_forall_param);
            }
        }
        OrAndChainAtomicFact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                mark_forall_param_coverage_in_and_chain_atomic_fact(
                    branch,
                    coverage_by_forall_param,
                );
            }
        }
    }
}

fn mark_forall_param_coverage_in_exist_body_fact(
    parent_fact: &ExistBodyFact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match parent_fact {
        ExistBodyFact::AtomicFact(atomic_fact) => {
            mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
        }
        ExistBodyFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                mark_forall_param_coverage_in_atomic_fact(inner_atomic, coverage_by_forall_param);
            }
        }
        ExistBodyFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                mark_forall_param_coverage_in_obj(chain_obj, coverage_by_forall_param);
            }
        }
        ExistBodyFact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                mark_forall_param_coverage_in_and_chain_atomic_fact(
                    branch,
                    coverage_by_forall_param,
                );
            }
        }
        ExistBodyFact::InlineForall(forall_fact) => {
            for param_def_with_type in forall_fact.params_def_with_type.groups.iter() {
                mark_forall_param_coverage_in_param_type(
                    &param_def_with_type.param_type,
                    coverage_by_forall_param,
                );
            }
            for fact in forall_fact.dom_facts.iter() {
                mark_forall_param_coverage_in_fact(fact, coverage_by_forall_param);
            }
            for fact in forall_fact.then_facts.iter() {
                mark_forall_param_coverage_in_exist_or_and_chain_atomic_fact(
                    fact,
                    coverage_by_forall_param,
                );
            }
        }
    }
}

fn mark_forall_param_coverage_in_fact(
    parent_fact: &Fact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match parent_fact {
        Fact::AtomicFact(atomic_fact) => {
            mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
        }
        Fact::ExistFact(exist_fact) => {
            mark_forall_param_coverage_in_exist_fact(exist_fact, coverage_by_forall_param);
        }
        Fact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                mark_forall_param_coverage_in_and_chain_atomic_fact(
                    branch,
                    coverage_by_forall_param,
                );
            }
        }
        Fact::AndFact(and_fact) => {
            for atomic_fact in and_fact.facts.iter() {
                mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
            }
        }
        Fact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                mark_forall_param_coverage_in_obj(chain_obj, coverage_by_forall_param);
            }
        }
        Fact::ForallFact(forall_fact) => {
            for fact in forall_fact.dom_facts.iter() {
                mark_forall_param_coverage_in_fact(fact, coverage_by_forall_param);
            }
            for fact in forall_fact.then_facts.iter() {
                mark_forall_param_coverage_in_exist_or_and_chain_atomic_fact(
                    fact,
                    coverage_by_forall_param,
                );
            }
        }
        Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {}
    }
}

fn mark_forall_param_coverage_in_exist_fact(
    exist_fact: &ExistFactEnum,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    for param_def_with_type in exist_fact.params_def_with_type().groups.iter() {
        mark_forall_param_coverage_in_param_type(
            &param_def_with_type.param_type,
            coverage_by_forall_param,
        );
    }
    for inner_fact in exist_fact.facts().iter() {
        mark_forall_param_coverage_in_exist_body_fact(inner_fact, coverage_by_forall_param);
    }
}

fn mark_forall_param_coverage_in_exist_or_and_chain_atomic_fact(
    parent_fact: &ExistOrAndChainAtomicFact,
    coverage_by_forall_param: &mut HashMap<IdentifierName, bool>,
) {
    match parent_fact {
        ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            mark_forall_param_coverage_in_atomic_fact(atomic_fact, coverage_by_forall_param);
        }
        ExistOrAndChainAtomicFact::AndFact(and_fact) => {
            for inner_atomic in and_fact.facts.iter() {
                mark_forall_param_coverage_in_atomic_fact(inner_atomic, coverage_by_forall_param);
            }
        }
        ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
            for chain_obj in chain_fact.objs.iter() {
                mark_forall_param_coverage_in_obj(chain_obj, coverage_by_forall_param);
            }
        }
        ExistOrAndChainAtomicFact::OrFact(or_fact) => {
            for branch in or_fact.facts.iter() {
                mark_forall_param_coverage_in_and_chain_atomic_fact(
                    branch,
                    coverage_by_forall_param,
                );
            }
        }
        ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
            mark_forall_param_coverage_in_exist_fact(exist_fact, coverage_by_forall_param);
        }
    }
}

impl ForallFact {
    pub fn error_messages_if_forall_param_missing_in_some_then_clause(
        &self,
    ) -> Vec<(usize, String)> {
        let forall_param_names = self.params_def_with_type.collect_param_names();
        if forall_param_names.is_empty() {
            return Vec::new();
        }
        let mut error_messages = Vec::new();
        let mut then_index: usize = 0;
        while then_index < self.then_facts.len() {
            let then_fact = &self.then_facts[then_index];
            let mut coverage_by_forall_param: HashMap<IdentifierName, bool> = HashMap::new();
            for param_name in forall_param_names.iter() {
                coverage_by_forall_param.insert(param_name.clone(), false);
            }
            mark_forall_param_coverage_in_exist_or_and_chain_atomic_fact(
                then_fact,
                &mut coverage_by_forall_param,
            );
            let mut missing_param_names = Vec::new();
            for param_name in forall_param_names.iter() {
                let is_mentioned_in_then_clause = match coverage_by_forall_param.get(param_name) {
                    Some(flag) => *flag,
                    None => false,
                };
                if !is_mentioned_in_then_clause {
                    missing_param_names.push(param_name.clone());
                }
            }
            if !missing_param_names.is_empty() {
                let missing_list = missing_param_names.join(", ");
                error_messages.push((
                    then_index,
                    format!(
                        "then-clause `{}` does not mention forall parameter(s) {{{}}}",
                        then_fact, missing_list,
                    ),
                ));
            }
            then_index += 1;
        }
        error_messages
    }
}

impl ForallFactWithIff {
    /// Only checks the embedded [`ForallFact`]'s `then_facts` (not `iff_facts`).
    pub fn error_messages_if_forall_param_missing_in_forall_then_clause(
        &self,
    ) -> Vec<(usize, String)> {
        self.forall_fact
            .error_messages_if_forall_param_missing_in_some_then_clause()
    }
}
