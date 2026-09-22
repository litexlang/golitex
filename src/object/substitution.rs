//! Capture-aware bound-identifier substitution for objects.

use crate::prelude::*;

impl Obj {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Obj {
        self.replace_bound_identifier_with_runtime(&Runtime::default(), from, to)
    }

    pub fn replace_bound_identifier_with_runtime(
        self,
        runtime: &Runtime,
        from: &str,
        to: &str,
    ) -> Obj {
        if from == to {
            return self;
        }
        match self {
            Obj::Atom(a) => Obj::Atom(a.replace_bound_identifier(from, to)),
            Obj::FnObj(inner) => {
                let head = replace_bound_identifier_with_runtime_in_fn_obj_head(
                    *inner.head,
                    runtime,
                    from,
                    to,
                );
                let body = inner
                    .body
                    .into_iter()
                    .map(|group| {
                        group
                            .into_iter()
                            .map(|b| {
                                Box::new(Obj::replace_bound_identifier_with_runtime(
                                    *b, runtime, from, to,
                                ))
                            })
                            .collect()
                    })
                    .collect();
                FnObj::new(head, body).into()
            }
            Obj::Number(n) => n.into(),
            Obj::ImaginaryUnit(i) => i.into(),
            Obj::EulerNumber(e) => e.into(),
            Obj::Pi(pi) => pi.into(),
            Obj::Add(x) => Add::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Sub(x) => Sub::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Mul(x) => Mul::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Div(x) => Div::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Mod(x) => Mod::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Quot(x) => Quot::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Gcd(x) => Gcd::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Lcm(x) => Lcm::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Floor(x) => Floor::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Ceil(x) => Ceil::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Min(x) => Min::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Max(x) => Max::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Exp(x) => Exp::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Ln(x) => Ln::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Sign(x) => Sign::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Factorial(x) => Factorial::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Pow(x) => Pow::new(
                Obj::replace_bound_identifier_with_runtime(*x.base, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.exponent, runtime, from, to),
            )
            .into(),
            Obj::Abs(x) => Abs::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Sin(x) => Sin::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Arcsin(x) => Arcsin::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Cos(x) => Cos::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Tan(x) => Tan::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Cot(x) => Cot::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::RealPart(x) => RealPart::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::ImaginaryPart(x) => ImaginaryPart::new(
                Obj::replace_bound_identifier_with_runtime(*x.arg, runtime, from, to),
            )
            .into(),
            Obj::ComplexAbs(x) => ComplexAbs::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Sqrt(x) => Sqrt::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Log(x) => Log::new(
                Obj::replace_bound_identifier_with_runtime(*x.base, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.arg, runtime, from, to),
            )
            .into(),
            Obj::Union(x) => Union::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::Intersect(x) => Intersect::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::SetMinus(x) => SetMinus::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::FamilyUnion(x) => FamilyUnion::new(Obj::replace_bound_identifier_with_runtime(
                *x.left, runtime, from, to,
            ))
            .into(),
            Obj::FamilyIntersect(x) => FamilyIntersect::new(Obj::replace_bound_identifier_with_runtime(
                *x.left, runtime, from, to,
            ))
            .into(),
            Obj::IndexUnion(x) => IndexUnion::new(
                Obj::replace_bound_identifier_with_runtime(*x.index_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.ambient_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.family_fn, runtime, from, to),
            )
            .into(),
            Obj::IndexIntersect(x) => IndexIntersect::new(
                Obj::replace_bound_identifier_with_runtime(*x.index_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.ambient_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.family_fn, runtime, from, to),
            )
            .into(),
            Obj::PowerSet(x) => PowerSet::new(Obj::replace_bound_identifier_with_runtime(
                *x.set, runtime, from, to,
            ))
            .into(),
            Obj::IndexCart(x) => IndexCart::new(
                Obj::replace_bound_identifier_with_runtime(*x.index_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.family_set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.family_fn, runtime, from, to),
            )
            .into(),
            Obj::ListSet(x) => ListSet::new(
                x.list
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier_with_runtime(*b, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::SetBuilder(sb) => {
                let param_binding = if sb.param_name() == from {
                    sb.param_binding.with_local_name(to.to_string())
                } else {
                    sb.param_binding
                };
                let param_set =
                    Obj::replace_bound_identifier_with_runtime(*sb.param_set, runtime, from, to);
                let facts = sb
                    .facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier_with_runtime(runtime, from, to))
                    .collect();
                Obj::SetBuilder(
                    SetBuilder::new(param_binding, param_set, facts)
                        .expect("renaming a valid set builder preserves object scope validity"),
                )
            }
            Obj::FnSet(fs) => {
                let FnSet { body } = fs;
                let FnSetBody {
                    set_bound_parameters,
                    dom_facts,
                    ret_set,
                } = body;
                let set_bound_parameters: Vec<SetBoundParameterGroup> = set_bound_parameters
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| {
                                if p.name() == from {
                                    p.with_local_name(to.to_string())
                                } else {
                                    p
                                }
                            })
                            .collect();
                        SetBoundParameterGroup::new(
                            params,
                            Obj::replace_bound_identifier_with_runtime(
                                *pg.param_type,
                                runtime,
                                from,
                                to,
                            ),
                        )
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier_with_runtime(runtime, from, to))
                    .collect();
                let ret_set =
                    Obj::replace_bound_identifier_with_runtime(*ret_set, runtime, from, to);
                FnSet::new(set_bound_parameters, dom_facts, ret_set)
                    .expect("renaming a valid fn set preserves object scope validity")
                    .into()
            }
            Obj::AnonymousFn(af) => {
                let AnonymousFn { body, equal_to } = af;
                let FnSetBody {
                    set_bound_parameters,
                    dom_facts,
                    ret_set,
                } = body;
                let set_bound_parameters: Vec<SetBoundParameterGroup> = set_bound_parameters
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| {
                                if p.name() == from {
                                    p.with_local_name(to.to_string())
                                } else {
                                    p
                                }
                            })
                            .collect();
                        SetBoundParameterGroup::new(
                            params,
                            Obj::replace_bound_identifier_with_runtime(
                                *pg.param_type,
                                runtime,
                                from,
                                to,
                            ),
                        )
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier_with_runtime(runtime, from, to))
                    .collect();
                let ret_set =
                    Obj::replace_bound_identifier_with_runtime(*ret_set, runtime, from, to);
                let equal_to =
                    Obj::replace_bound_identifier_with_runtime(*equal_to, runtime, from, to);
                AnonymousFn::new(set_bound_parameters, dom_facts, ret_set, equal_to)
                    .expect("renaming a valid anonymous fn preserves object scope validity")
                    .into()
            }
            Obj::Cart(c) => Cart::new(
                c.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier_with_runtime(*b, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::CartDim(x) => CartDim::new(Obj::replace_bound_identifier_with_runtime(
                *x.set, runtime, from, to,
            ))
            .into(),
            Obj::Proj(x) => Proj::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.dim, runtime, from, to),
            )
            .into(),
            Obj::TupleDim(x) => TupleDim::new(Obj::replace_bound_identifier_with_runtime(
                *x.arg, runtime, from, to,
            ))
            .into(),
            Obj::Tuple(t) => Tuple::new(
                t.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier_with_runtime(*b, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::FiniteSetSize(x) => FiniteSetSize::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
            )
            .into(),
            Obj::FiniteSetMax(x) => FiniteSetMax::new(Obj::replace_bound_identifier_with_runtime(
                *x.set, runtime, from, to,
            ))
            .into(),
            Obj::FiniteSetMin(x) => FiniteSetMin::new(Obj::replace_bound_identifier_with_runtime(
                *x.set, runtime, from, to,
            ))
            .into(),
            Obj::FnRange(x) => FnRange::new(Obj::replace_bound_identifier_with_runtime(
                *x.function,
                runtime,
                from,
                to,
            ))
            .into(),
            Obj::Replacement(x) => Replacement::new(
                x.prop_name,
                Obj::replace_bound_identifier_with_runtime(*x.source_set, runtime, from, to),
            )
            .into(),
            Obj::Sum(x) => Sum::new(
                Obj::replace_bound_identifier_with_runtime(*x.start, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.end, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
            )
            .into(),
            Obj::SumOfFiniteSet(x) => SumOfFiniteSet::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
            )
            .into(),
            Obj::Product(x) => Product::new(
                Obj::replace_bound_identifier_with_runtime(*x.start, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.end, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
            )
            .into(),
            Obj::ProductOfFiniteSet(x) => ProductOfFiniteSet::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
            )
            .into(),
            Obj::Reduce(x) => Reduce::new(
                Obj::replace_bound_identifier_with_runtime(*x.start, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.end, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.op, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.seed, runtime, from, to),
            )
            .into(),
            Obj::FiniteSetReduce(x) => FiniteSetReduce::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.func, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.op, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.seed, runtime, from, to),
            )
            .into(),
            Obj::Range(x) => Range::new(
                Obj::replace_bound_identifier_with_runtime(*x.start, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.end, runtime, from, to),
            )
            .into(),
            Obj::ClosedRange(x) => ClosedRange::new(
                Obj::replace_bound_identifier_with_runtime(*x.start, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.end, runtime, from, to),
            )
            .into(),
            Obj::FiniteSeqSet(x) => FiniteSeqSet::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.n, runtime, from, to),
            )
            .into(),
            Obj::SeqSet(x) => SeqSet::new(Obj::replace_bound_identifier_with_runtime(
                *x.set, runtime, from, to,
            ))
            .into(),
            Obj::FiniteSeqListObj(x) => FiniteSeqListObj::new(
                x.objs
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier_with_runtime(*b, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::MatrixSet(x) => MatrixSet::new(
                Obj::replace_bound_identifier_with_runtime(*x.set, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.row_len, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.col_len, runtime, from, to),
            )
            .into(),
            Obj::MatrixListObj(x) => MatrixListObj::new(
                x.rows
                    .into_iter()
                    .map(|row| {
                        row.into_iter()
                            .map(|b| {
                                Obj::replace_bound_identifier_with_runtime(*b, runtime, from, to)
                            })
                            .collect()
                    })
                    .collect(),
            )
            .into(),
            Obj::MatrixAdd(x) => MatrixAdd::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::MatrixSub(x) => MatrixSub::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::MatrixMul(x) => MatrixMul::new(
                Obj::replace_bound_identifier_with_runtime(*x.left, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.right, runtime, from, to),
            )
            .into(),
            Obj::MatrixScalarMul(x) => MatrixScalarMul::new(
                Obj::replace_bound_identifier_with_runtime(*x.scalar, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.matrix, runtime, from, to),
            )
            .into(),
            Obj::MatrixPow(x) => MatrixPow::new(
                Obj::replace_bound_identifier_with_runtime(*x.base, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.exponent, runtime, from, to),
            )
            .into(),
            Obj::ObjAtIndex(x) => ObjAtIndex::new(
                Obj::replace_bound_identifier_with_runtime(*x.obj, runtime, from, to),
                Obj::replace_bound_identifier_with_runtime(*x.index, runtime, from, to),
            )
            .into(),
            Obj::StandardSet(s) => s.into(),
            Obj::StructObj(s) => StructObj::new(
                s.name,
                s.params
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier_with_runtime(o, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::ObjAsStructInstanceWithFieldAccess(s) => {
                let obj = Obj::replace_bound_identifier_with_runtime(*s.obj, runtime, from, to);
                match s.resolved_struct_carrier {
                    Some(struct_obj) => {
                        let replaced = Obj::StructObj(*struct_obj)
                            .replace_bound_identifier_with_runtime(runtime, from, to);
                        let Obj::StructObj(struct_obj) = replaced else {
                            unreachable!("substituting a struct carrier preserves its object kind")
                        };
                        ObjAsStructInstanceWithFieldAccess::new_resolved(
                            obj,
                            s.field_name,
                            struct_obj,
                        )
                        .into()
                    }
                    None => ObjAsStructInstanceWithFieldAccess::new(obj, s.field_name).into(),
                }
            }
            Obj::InstantiatedTemplateObj(t) => InstantiatedTemplateObj::new(
                t.template_name,
                t.args
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier_with_runtime(o, runtime, from, to))
                    .collect(),
            )
            .into(),
            Obj::IntervalObj(x) => match x {
                IntervalObj::LeftOpenRightOpen(i) => IntervalObj::new_left_open_right_open(
                    Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    Obj::replace_bound_identifier_with_runtime(*i.end, runtime, from, to),
                )
                .into(),
                IntervalObj::LeftOpenRightClosed(i) => IntervalObj::new_left_open_right_closed(
                    Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    Obj::replace_bound_identifier_with_runtime(*i.end, runtime, from, to),
                )
                .into(),
                IntervalObj::LeftClosedRightOpen(i) => IntervalObj::new_left_closed_right_open(
                    Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    Obj::replace_bound_identifier_with_runtime(*i.end, runtime, from, to),
                )
                .into(),
                IntervalObj::LeftClosedRightClosed(i) => IntervalObj::new_left_closed_right_closed(
                    Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    Obj::replace_bound_identifier_with_runtime(*i.end, runtime, from, to),
                )
                .into(),
            },
            Obj::OneSideInfinityIntervalObj(x) => match x {
                OneSideInfinityIntervalObj::LeftOpen(i) => {
                    OneSideInfinityIntervalObj::new_left_open(
                        Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    )
                    .into()
                }
                OneSideInfinityIntervalObj::LeftClosed(i) => {
                    OneSideInfinityIntervalObj::new_left_closed(
                        Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    )
                    .into()
                }
                OneSideInfinityIntervalObj::RightOpen(i) => {
                    OneSideInfinityIntervalObj::new_right_open(
                        Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    )
                    .into()
                }
                OneSideInfinityIntervalObj::RightClosed(i) => {
                    OneSideInfinityIntervalObj::new_right_closed(
                        Obj::replace_bound_identifier_with_runtime(*i.start, runtime, from, to),
                    )
                    .into()
                }
            },
        }
    }
}

/// Replace in identifier / `mod::name` name-shaped [`Obj`] values only.
fn replace_bound_identifier_with_runtime_in_name_obj(obj: Obj, from: &str, to: &str) -> Obj {
    if from == to {
        return obj;
    }
    match obj {
        Obj::Atom(AtomObj::Identifier(i)) => {
            if i.name == from {
                Identifier::new(to.to_string()).into()
            } else {
                Obj::Atom(AtomObj::Identifier(i))
            }
        }
        Obj::Atom(AtomObj::IdentifierWithMod(m)) => {
            let name = if m.name == from {
                to.to_string()
            } else {
                m.name
            };
            Obj::from(IdentifierWithMod::new(m.mod_name, name))
        }
        _ => obj,
    }
}

fn replace_bound_identifier_with_runtime_in_fn_obj_head(
    head: FnObjHead,
    runtime: &Runtime,
    from: &str,
    to: &str,
) -> FnObjHead {
    if from == to {
        return head;
    }
    match head {
        FnObjHead::Identifier(i) => FnObjHead::given_an_atom_return_a_fn_obj_head(
            replace_bound_identifier_with_runtime_in_name_obj(
                Obj::Atom(AtomObj::Identifier(i.clone())),
                from,
                to,
            ),
        )
        .expect("name replace preserves fn head shape"),
        FnObjHead::IdentifierWithMod(m) => FnObjHead::given_an_atom_return_a_fn_obj_head(
            replace_bound_identifier_with_runtime_in_name_obj(
                Obj::Atom(AtomObj::IdentifierWithMod(m.clone())),
                from,
                to,
            ),
        )
        .expect("name replace preserves fn head shape"),
        FnObjHead::Bound(p) => {
            let symbol = if p.name() == from {
                p.symbol.with_display_name(to.to_string())
            } else {
                p.symbol
            };
            BoundParamObj::new(symbol).into()
        }
        FnObjHead::AnonymousFnLiteral(a) => {
            let inner = (*a).clone();
            let replaced =
                Obj::AnonymousFn(inner).replace_bound_identifier_with_runtime(runtime, from, to);
            let Obj::AnonymousFn(new_af) = replaced else {
                unreachable!()
            };
            FnObjHead::AnonymousFnLiteral(Box::new(new_af))
        }
        FnObjHead::FiniteSeqListObj(v) => {
            let replaced =
                Obj::FiniteSeqListObj(v).replace_bound_identifier_with_runtime(runtime, from, to);
            let Obj::FiniteSeqListObj(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::FiniteSeqListObj(new_v)
        }
        FnObjHead::ObjAtIndex(v) => {
            let replaced =
                Obj::ObjAtIndex(v).replace_bound_identifier_with_runtime(runtime, from, to);
            let Obj::ObjAtIndex(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::ObjAtIndex(new_v)
        }
        FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => {
            let replaced = Obj::ObjAsStructInstanceWithFieldAccess(v)
                .replace_bound_identifier_with_runtime(runtime, from, to);
            let Obj::ObjAsStructInstanceWithFieldAccess(new_v) = replaced else {
                unreachable!()
            };
            FnObjHead::ObjAsStructInstanceWithFieldAccess(new_v)
        }
        FnObjHead::InstantiatedTemplateObj(t) => {
            let replaced = Obj::InstantiatedTemplateObj(t)
                .replace_bound_identifier_with_runtime(runtime, from, to);
            let Obj::InstantiatedTemplateObj(new_t) = replaced else {
                unreachable!()
            };
            FnObjHead::InstantiatedTemplateObj(new_t)
        }
        FnObjHead::MatrixOperator(matrix) => {
            let replaced = (*matrix)
                .clone()
                .replace_bound_identifier_with_runtime(runtime, from, to);
            FnObjHead::MatrixOperator(Box::new(replaced))
        }
    }
}
