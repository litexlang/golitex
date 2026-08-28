use crate::prelude::*;
use std::collections::HashSet;

impl FnObjHead {
    pub fn contains_forall_free_param_obj(&self) -> bool {
        let mut collector = FreeParamNameCollector::new(false);
        self.collect_free_param_names_into(&mut collector);
        !collector.names.is_empty()
    }

    fn collect_free_param_names_into(&self, collector: &mut FreeParamNameCollector) {
        match self {
            FnObjHead::Identifier(_) => {}
            FnObjHead::Bound(param) => collector.insert_bound(param.name()),
            FnObjHead::AnonymousFnLiteral(anonymous_fn) => {
                collect_forall_free_param_names_in_fn_set_body(&anonymous_fn.body, collector);
                anonymous_fn
                    .equal_to
                    .collect_free_param_names_into(collector);
            }
            FnObjHead::FiniteSeqListObj(sequence) => {
                collect_forall_free_param_names_in_boxed_objs(&sequence.objs, collector);
            }
            FnObjHead::ObjAtIndex(obj_at_index) => {
                collect_forall_free_param_names_in_pair(
                    &obj_at_index.obj,
                    &obj_at_index.index,
                    collector,
                );
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                collect_forall_free_param_names_in_objs(&field_access.struct_obj.params, collector);
                field_access.obj.collect_free_param_names_into(collector);
            }
            FnObjHead::InstantiatedTemplateObj(template) => {
                collect_forall_free_param_names_in_objs(&template.args, collector);
            }
            FnObjHead::MatrixOperator(matrix) => {
                matrix.collect_free_param_names_into(collector);
            }
            FnObjHead::IdentifierWithMod(_) => {}
        }
    }
}

impl Obj {
    /// Collect all local binder names, independent of the AST construct that
    /// owns each binder.
    pub fn collect_bound_param_names(&self) -> HashSet<String> {
        let mut collector = FreeParamNameCollector::new(true);
        self.collect_free_param_names_into(&mut collector);
        collector.names
    }

    /// Historical wrapper; this is an all-name set, not a scope-subtracted free-variable set.
    pub fn collect_forall_free_param_names(&self) -> HashSet<String> {
        self.collect_bound_param_names()
    }

    pub fn contains_forall_free_param_obj(&self) -> bool {
        let mut collector = FreeParamNameCollector::new(false);
        self.collect_free_param_names_into(&mut collector);
        !collector.names.is_empty()
    }

    fn collect_free_param_names_into(&self, collector: &mut FreeParamNameCollector) {
        match self {
            Obj::Atom(atom) => collector.collect_atom(atom),
            Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => {}
            Obj::FnObj(fn_obj) => {
                fn_obj.head.collect_free_param_names_into(collector);
                for args in &fn_obj.body {
                    collect_forall_free_param_names_in_boxed_objs(args, collector);
                }
            }
            Obj::Add(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Sub(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Mul(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Div(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Mod(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Quot(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Gcd(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Lcm(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Min(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Max(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Pow(x) => collect_forall_free_param_names_in_pair(&x.base, &x.exponent, collector),
            Obj::Abs(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Floor(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Ceil(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Exp(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Ln(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Sign(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Factorial(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Sin(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Arcsin(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Cos(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Tan(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Cot(x) => x.arg.collect_free_param_names_into(collector),
            Obj::RealPart(x) => x.arg.collect_free_param_names_into(collector),
            Obj::ImaginaryPart(x) => x.arg.collect_free_param_names_into(collector),
            Obj::ComplexAbs(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Sqrt(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Log(x) => collect_forall_free_param_names_in_pair(&x.base, &x.arg, collector),
            Obj::Union(x) => collect_forall_free_param_names_in_pair(&x.left, &x.right, collector),
            Obj::Intersect(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::SetMinus(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::BigUnion(x) => x.left.collect_free_param_names_into(collector),
            Obj::BigIntersect(x) => x.left.collect_free_param_names_into(collector),
            Obj::IndexUnion(x) => {
                x.index_set.collect_free_param_names_into(collector);
                x.ambient_set.collect_free_param_names_into(collector);
                x.family_fn.collect_free_param_names_into(collector);
            }
            Obj::IndexIntersect(x) => {
                x.index_set.collect_free_param_names_into(collector);
                x.ambient_set.collect_free_param_names_into(collector);
                x.family_fn.collect_free_param_names_into(collector);
            }
            Obj::PowerSet(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSetMax(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSetMin(x) => x.set.collect_free_param_names_into(collector),
            Obj::GeneralCart(x) => {
                x.index_set.collect_free_param_names_into(collector);
                x.family_set.collect_free_param_names_into(collector);
                x.family_fn.collect_free_param_names_into(collector);
            }
            Obj::ListSet(x) => collect_forall_free_param_names_in_boxed_objs(&x.list, collector),
            Obj::SetBuilder(x) => {
                collector.insert_binder(x.param_name());
                x.param_set.collect_free_param_names_into(collector);
                collect_forall_free_param_names_in_quantifier_free_facts(&x.facts, collector);
            }
            Obj::FnSet(x) => collect_forall_free_param_names_in_fn_set_body(&x.body, collector),
            Obj::AnonymousFn(x) => {
                collect_forall_free_param_names_in_fn_set_body(&x.body, collector);
                x.equal_to.collect_free_param_names_into(collector);
            }
            Obj::Cart(x) => collect_forall_free_param_names_in_boxed_objs(&x.args, collector),
            Obj::CartDim(x) => x.set.collect_free_param_names_into(collector),
            Obj::Proj(x) => collect_forall_free_param_names_in_pair(&x.set, &x.dim, collector),
            Obj::TupleDim(x) => x.arg.collect_free_param_names_into(collector),
            Obj::Tuple(x) => collect_forall_free_param_names_in_boxed_objs(&x.args, collector),
            Obj::FiniteSetSize(x) => x.set.collect_free_param_names_into(collector),
            Obj::FnRange(x) => x.function.collect_free_param_names_into(collector),
            Obj::Replacement(x) => x.source_set.collect_free_param_names_into(collector),
            Obj::Sum(x) => {
                x.start.collect_free_param_names_into(collector);
                x.end.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::SumOfFiniteSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::Product(x) => {
                x.start.collect_free_param_names_into(collector);
                x.end.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::ProductOfFiniteSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
            }
            Obj::Reduce(x) => {
                x.start.collect_free_param_names_into(collector);
                x.end.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
                x.op.collect_free_param_names_into(collector);
                x.seed.collect_free_param_names_into(collector);
            }
            Obj::FiniteSetReduce(x) => {
                x.set.collect_free_param_names_into(collector);
                x.func.collect_free_param_names_into(collector);
                x.op.collect_free_param_names_into(collector);
                x.seed.collect_free_param_names_into(collector);
            }
            Obj::Range(x) => collect_forall_free_param_names_in_pair(&x.start, &x.end, collector),
            Obj::ClosedRange(x) => {
                collect_forall_free_param_names_in_pair(&x.start, &x.end, collector);
            }
            Obj::FiniteSeqSet(x) => {
                collect_forall_free_param_names_in_pair(&x.set, &x.n, collector);
            }
            Obj::SeqSet(x) => x.set.collect_free_param_names_into(collector),
            Obj::FiniteSeqListObj(x) => {
                collect_forall_free_param_names_in_boxed_objs(&x.objs, collector);
            }
            Obj::ObjAtIndex(x) => {
                collect_forall_free_param_names_in_pair(&x.obj, &x.index, collector);
            }
            Obj::MatrixSet(x) => {
                x.set.collect_free_param_names_into(collector);
                x.row_len.collect_free_param_names_into(collector);
                x.col_len.collect_free_param_names_into(collector);
            }
            Obj::MatrixListObj(x) => {
                for row in &x.rows {
                    collect_forall_free_param_names_in_boxed_objs(row, collector);
                }
            }
            Obj::MatrixAdd(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixSub(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixMul(x) => {
                collect_forall_free_param_names_in_pair(&x.left, &x.right, collector)
            }
            Obj::MatrixScalarMul(x) => {
                collect_forall_free_param_names_in_pair(&x.scalar, &x.matrix, collector);
            }
            Obj::MatrixPow(x) => {
                collect_forall_free_param_names_in_pair(&x.base, &x.exponent, collector);
            }
            Obj::StructObj(x) => collect_forall_free_param_names_in_objs(&x.params, collector),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                collect_forall_free_param_names_in_objs(&x.struct_obj.params, collector);
                x.obj.collect_free_param_names_into(collector);
            }
            Obj::InstantiatedTemplateObj(x) => {
                collect_forall_free_param_names_in_objs(&x.args, collector);
            }
            Obj::OneSideInfinityIntervalObj(x) => {
                x.start().collect_free_param_names_into(collector);
            }
            Obj::IntervalObj(x) => {
                collect_forall_free_param_names_in_pair(x.start(), x.end(), collector);
            }
        }
    }
}

struct FreeParamNameCollector {
    names: HashSet<String>,
    include_binder_headers: bool,
}

impl FreeParamNameCollector {
    fn new(include_binder_headers: bool) -> Self {
        FreeParamNameCollector {
            names: HashSet::new(),
            include_binder_headers,
        }
    }

    fn insert_binder(&mut self, name: &str) {
        if self.include_binder_headers {
            self.names.insert(name.to_string());
        }
    }

    fn insert_bound(&mut self, name: &str) {
        self.names.insert(name.to_string());
    }

    fn collect_atom(&mut self, atom: &AtomObj) {
        match atom {
            AtomObj::Identifier(_) => {}
            AtomObj::IdentifierWithMod(_) => {}
            AtomObj::Bound(param) => self.insert_bound(param.name()),
        }
    }
}

fn collect_forall_free_param_names_in_pair(
    left: &Obj,
    right: &Obj,
    collector: &mut FreeParamNameCollector,
) {
    left.collect_free_param_names_into(collector);
    right.collect_free_param_names_into(collector);
}

fn collect_forall_free_param_names_in_objs(objs: &[Obj], collector: &mut FreeParamNameCollector) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_boxed_objs(
    objs: &[Box<Obj>],
    collector: &mut FreeParamNameCollector,
) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_obj_refs(
    objs: &[&Obj],
    collector: &mut FreeParamNameCollector,
) {
    for obj in objs {
        obj.collect_free_param_names_into(collector);
    }
}

fn collect_forall_free_param_names_in_fn_set_body(
    body: &FnSetBody,
    collector: &mut FreeParamNameCollector,
) {
    for group in body.set_bound_parameters.iter() {
        for name in &group.params {
            collector.insert_binder(name.name());
        }
        group.param_type.collect_free_param_names_into(collector);
    }
    collect_forall_free_param_names_in_or_and_chain_facts(&body.dom_facts, collector);
    body.ret_set.collect_free_param_names_into(collector);
}

fn collect_forall_free_param_names_in_or_and_chain_facts(
    facts: &[QuantifierFreeFact],
    collector: &mut FreeParamNameCollector,
) {
    for fact in facts {
        collect_forall_free_param_names_in_obj_refs(&fact.get_args_from_fact_ref(), collector);
    }
}

fn collect_forall_free_param_names_in_quantifier_free_facts(
    facts: &[QuantifierFreeFact],
    collector: &mut FreeParamNameCollector,
) {
    for fact in facts {
        match fact {
            QuantifierFreeFact::AtomicFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            QuantifierFreeFact::AndFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            QuantifierFreeFact::ChainFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
            QuantifierFreeFact::OrFact(fact) => collect_forall_free_param_names_in_obj_refs(
                &fact.get_args_from_fact_ref(),
                collector,
            ),
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/object/parameter_names/tests.rs"]
mod tests;
