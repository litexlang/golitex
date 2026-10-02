//! Recover a free induction identity from objects, goals, or ordinary proof actions.

use crate::ast::fact::{and_chain_as_fact, Fact};
use crate::ast::stmt::Stmt;

// Recover the parser-assigned binder identity, independent of the goal's
// atomic predicate. Compound goals use the same object-argument traversal.
pub(super) fn recover_induction_param(
    name: &str,
    goals: &[crate::ast::fact::ExistOrAndChainAtomicFact],
    proofs: &[&[Stmt]],
) -> Option<crate::ast::names::BoundName> {
    use crate::ast::fact::{
        atomic_fact_args_ref, or_fact_args_ref, plain_exist_fact_free_args_ref,
        ExistOrAndChainAtomicFact,
    };
    for goal in goals {
        let args = match goal {
            ExistOrAndChainAtomicFact::AtomicFact(a) => atomic_fact_args_ref(a),
            ExistOrAndChainAtomicFact::AndFact(a) => {
                a.facts.iter().flat_map(atomic_fact_args_ref).collect()
            }
            ExistOrAndChainAtomicFact::ChainFact(c) => c.objs.iter().collect(),
            ExistOrAndChainAtomicFact::OrFact(o) => or_fact_args_ref(o),
            ExistOrAndChainAtomicFact::ExistFact(e)
            | ExistOrAndChainAtomicFact::ExistUniqueFact(e)
            | ExistOrAndChainAtomicFact::NotExistFact(e) => {
                if e.typed_parameters
                    .groups
                    .iter()
                    .any(|g| g.params.iter().any(|p| p.name == name))
                {
                    continue;
                }
                plain_exist_fact_free_args_ref(e)
            }
        };
        if let Some(param) = args
            .into_iter()
            .find_map(|obj| induction_bound_from_obj(name, obj))
        {
            return Some(param);
        }
    }
    proofs
        .iter()
        .flat_map(|proof| proof.iter())
        .find_map(|stmt| induction_bound_from_stmt(name, stmt))
}

fn induction_bound_from_obj(
    name: &str,
    obj: &crate::ast::obj::Obj,
) -> Option<crate::ast::names::BoundName> {
    use crate::ast::obj::*;
    if let Obj::Identifier(IdentifierObj::Plain { id, name: found }) = obj {
        return (found == name).then(|| crate::ast::names::BoundName::new(*id, found.clone()));
    }
    let children: Vec<&Obj> = match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => vec![&a.arg],
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => vec![&a.base, &a.exponent],
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => vec![&a.arg],
        Obj::ArithmeticOperator(ArithmeticOperator::Min(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Max(a)) => vec![&a.left, &a.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)) => vec![&a.arg],
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)) => vec![&a.arg],
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(a)) => vec![&a.arg],
        Obj::IntegerOperator(IntegerOperator::Mod(a)) => vec![&a.left, &a.right],
        Obj::IntegerOperator(IntegerOperator::Quot(a)) => vec![&a.left, &a.right],
        Obj::IntegerOperator(IntegerOperator::Gcd(a)) => vec![&a.left, &a.right],
        Obj::IntegerOperator(IntegerOperator::Lcm(a)) => vec![&a.left, &a.right],
        Obj::IntegerOperator(IntegerOperator::Factorial(a)) => vec![&a.arg],
        Obj::ExpLogOperator(ExpLogOperator::Exp(a)) => vec![&a.arg],
        Obj::ExpLogOperator(ExpLogOperator::Ln(a)) => vec![&a.arg],
        Obj::ExpLogOperator(ExpLogOperator::Log(a)) => vec![&a.base, &a.arg],
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Sin(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Cos(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Tan(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Cot(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Arcsin(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Arccos(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Arctan(a)) => vec![&a.arg],
        Obj::TrigOperator(TrigOperator::Arccot(a)) => vec![&a.arg],
        Obj::ComplexOperator(ComplexOperator::RealPart(a)) => vec![&a.arg],
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(a)) => vec![&a.arg],
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(a)) => vec![&a.arg],
        Obj::FnObj(f) => {
            let head = match f.head.as_ref() {
                FnObjHead::Identifier(IdentifierObj::Plain { id, name: found }) => {
                    (found == name).then(|| crate::ast::names::BoundName::new(*id, found.clone()))
                }
                FnObjHead::Identifier(_) => None,
                FnObjHead::AnonymousFnLiteral(af) => induction_bound_from_anonymous_fn(name, af),
                FnObjHead::FieldAccess(a) => induction_bound_from_obj(name, &a.obj),
                FnObjHead::InstantiatedTemplateObj(a) => a
                    .args
                    .iter()
                    .find_map(|o| induction_bound_from_obj(name, o)),
            };
            return head.or_else(|| {
                f.body
                    .iter()
                    .flatten()
                    .find_map(|o| induction_bound_from_obj(name, o))
            });
        }
        Obj::SetOperator(SetOperator::Union(a)) => vec![&a.left, &a.right],
        Obj::SetOperator(SetOperator::Intersect(a)) => vec![&a.left, &a.right],
        Obj::SetOperator(SetOperator::SetMinus(a)) => vec![&a.left, &a.right],
        Obj::SetOperator(SetOperator::FamilyUnion(a)) => vec![&a.left],
        Obj::SetOperator(SetOperator::FamilyIntersect(a)) => vec![&a.left],
        Obj::SetOperator(SetOperator::PowerSet(a)) => vec![&a.set],
        Obj::SetOperator(SetOperator::IndexUnion(a)) => {
            vec![&a.index_set, &a.ambient_set, &a.family_fn]
        }
        Obj::SetOperator(SetOperator::IndexIntersect(a)) => {
            vec![&a.index_set, &a.ambient_set, &a.family_fn]
        }
        Obj::SetOperator(SetOperator::IndexCart(a)) => {
            vec![&a.index_set, &a.family_set, &a.family_fn]
        }
        Obj::SetFormer(SetFormer::ListSet(a)) => a.list.iter().map(|o| o.as_ref()).collect(),
        Obj::SetFormer(SetFormer::SetBuilder(a)) => {
            return induction_bound_from_obj(name, &a.param_set).or_else(|| {
                if a.param_binding.name == name {
                    return None;
                }
                a.facts
                    .iter()
                    .flat_map(crate::ast::fact::quantifier_free_fact_args_ref)
                    .find_map(|o| induction_bound_from_obj(name, o))
            });
        }
        Obj::FunctionSpace(FunctionSpace::FnSet(a)) => return induction_bound_from_fn_set(name, a),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)) => {
            return induction_bound_from_anonymous_fn(name, a)
        }
        Obj::FunctionSpace(FunctionSpace::FnRange(a)) => vec![&a.function],
        Obj::ProductShape(ProductShape::Cart(a)) => a.args.iter().map(|o| o.as_ref()).collect(),
        Obj::ProductShape(ProductShape::Tuple(a)) => a.args.iter().map(|o| o.as_ref()).collect(),
        Obj::ProductShape(ProductShape::CartDim(a)) => vec![&a.set],
        Obj::ProductShape(ProductShape::Proj(a)) => vec![&a.set, &a.dim],
        Obj::ProductShape(ProductShape::TupleDim(a)) => vec![&a.arg],
        Obj::ProductShape(ProductShape::ObjAtIndex(a)) => vec![&a.obj, &a.index],
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(a)) => vec![&a.set],
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(a)) => vec![&a.set],
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(a)) => vec![&a.set],
        Obj::IteratedOperator(IteratedOperator::Sum(a)) => vec![&a.start, &a.end, &a.func],
        Obj::IteratedOperator(IteratedOperator::Product(a)) => vec![&a.start, &a.end, &a.func],
        Obj::IteratedOperator(IteratedOperator::Reduce(a)) => {
            vec![&a.start, &a.end, &a.func, &a.op, &a.seed]
        }
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(a)) => vec![&a.set, &a.func],
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(a)) => vec![&a.set, &a.func],
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(a)) => {
            vec![&a.set, &a.func, &a.op, &a.seed]
        }
        Obj::SetFormer(SetFormer::Range(a)) => vec![&a.start, &a.end],
        Obj::SetFormer(SetFormer::ClosedRange(a)) => vec![&a.start, &a.end],
        Obj::SetFormer(SetFormer::FiniteSeqSet(a)) => vec![&a.set, &a.n],
        Obj::SetFormer(SetFormer::SeqSet(a)) => vec![&a.set],
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(a)) => {
            a.params.iter().collect()
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a)) => vec![&a.obj],
        Obj::InstantiatedTemplateObj(a) => a.args.iter().collect(),
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(a)) => match a {
            OneSideInfinityIntervalObj::LowerOpen(a)
            | OneSideInfinityIntervalObj::LowerClosed(a)
            | OneSideInfinityIntervalObj::UpperOpen(a)
            | OneSideInfinityIntervalObj::UpperClosed(a) => vec![&a.start],
        },
        Obj::SetFormer(SetFormer::IntervalObj(a)) => match a {
            IntervalObj::LeftOpenRightOpen(a)
            | IntervalObj::LeftOpenRightClosed(a)
            | IntervalObj::LeftClosedRightOpen(a)
            | IntervalObj::LeftClosedRightClosed(a) => vec![&a.start, &a.end],
        },
        Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_) => return None,
    };
    children
        .into_iter()
        .find_map(|child| induction_bound_from_obj(name, child))
}

fn induction_bound_from_fn_set(
    name: &str,
    fs: &crate::ast::obj::FnSet,
) -> Option<crate::ast::names::BoundName> {
    if fs
        .set_bound_parameters
        .groups
        .iter()
        .any(|g| g.params.iter().any(|p| p.name == name))
    {
        return None;
    }
    fs.set_bound_parameters
        .groups
        .iter()
        .find_map(|g| induction_bound_from_obj(name, &g.param_type))
        .or_else(|| {
            fs.dom_facts
                .iter()
                .flat_map(crate::ast::fact::quantifier_free_fact_args_ref)
                .find_map(|o| induction_bound_from_obj(name, o))
        })
        .or_else(|| induction_bound_from_obj(name, &fs.ret_set))
}

fn induction_bound_from_anonymous_fn(
    name: &str,
    af: &crate::ast::obj::AnonymousFn,
) -> Option<crate::ast::names::BoundName> {
    if af
        .body
        .set_bound_parameters
        .groups
        .iter()
        .any(|g| g.params.iter().any(|p| p.name == name))
    {
        return None;
    }
    induction_bound_from_fn_set(name, &af.body)
        .or_else(|| induction_bound_from_obj(name, &af.equal_to))
}

// A constant target may use the induction variable only in a proof action.
// Recover that same parsed ID rather than manufacturing another variable.
fn induction_bound_from_stmt(name: &str, stmt: &Stmt) -> Option<crate::ast::names::BoundName> {
    use crate::ast::stmt::*;
    let mut objs: Vec<&crate::ast::obj::Obj> = Vec::new();
    let mut facts: Vec<Fact> = Vec::new();
    let mut bodies: Vec<&[Stmt]> = Vec::new();
    match stmt {
        Stmt::Fact(f) => facts.push(f.clone()),
        Stmt::Trust(TrustBoundaryStmt::TrustStmt(s)) => facts.extend(s.facts.clone()),
        Stmt::Trust(TrustBoundaryStmt::TrustHaveStmt(s)) => {
            if let Some(p) = induction_bound_from_typed_params(name, &s.param_def) {
                return Some(p);
            }
            facts.extend(s.facts.clone());
        }
        Stmt::Definition(s) => return induction_bound_from_definition(name, s),
        Stmt::ReleaseAndExpand(s) => match s {
            ReleaseAndExpandStmt::ReleaseThmStmt(s) => {
                if let TheoremCallArguments::Parenthesized(args) = &s.call.arguments {
                    objs.extend(args);
                }
            }
            ReleaseAndExpandStmt::ReleaseStructDefStmt(s) => objs.push(&s.obj),
            ReleaseAndExpandStmt::ReleaseObjDefStmt(s) => {
                return induction_bound_from_obj(
                    name,
                    &crate::ast::obj::Obj::Identifier(s.name.clone()),
                );
            }
            ReleaseAndExpandStmt::ExpandRangeStmt(s) => {
                objs.push(&s.element);
                match &s.range {
                    ClosedRangeOrRange::Range(r) => objs.extend([r.start.as_ref(), r.end.as_ref()]),
                    ClosedRangeOrRange::ClosedRange(r) => {
                        objs.extend([r.start.as_ref(), r.end.as_ref()])
                    }
                }
            }
            ReleaseAndExpandStmt::ReleaseZornLemmaStmt(s) => {
                objs.push(&s.set);
                bodies.push(&s.proof);
            }
            ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(s) => {
                objs.push(&s.family);
                bodies.push(&s.proof);
            }
            ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(s) => objs.push(&s.set),
        },
        Stmt::By(s) => match s {
            ByStmt::ByCasesStmt(s) => {
                facts.extend(s.then_facts.clone());
                facts.extend(s.cases.iter().map(and_chain_as_fact));
                facts.extend(s.impossible_facts.iter().flatten().cloned().map(Into::into));
                bodies.extend(s.proofs.iter().map(|p| p.as_slice()));
            }
            ByStmt::ByContraStmt(s) => {
                facts.push(s.to_prove.clone());
                facts.push(s.impossible_fact.clone().into());
                bodies.push(&s.proof);
            }
            ByStmt::ByEnumerateFiniteSetStmt(s) => {
                facts.push(Fact::ForallFact(s.forall_fact.clone()));
                bodies.push(&s.proof);
            }
            ByStmt::ByForStmt(s) => {
                facts.push(Fact::ForallFact(s.forall_fact.clone()));
                bodies.push(&s.proof);
            }
            ByStmt::ByInducStmt(s) => {
                if s.param_binding == name {
                    return induction_bound_from_obj(name, &s.induc_from);
                }
                objs.push(&s.induc_from);
                facts.extend(s.to_prove.iter().cloned().map(Into::into));
                bodies.push(&s.proof);
                bodies.extend(s.base_proof.as_deref());
                bodies.extend(s.step_proof.as_deref());
            }
            ByStmt::ByStrongInducStmt(s) => {
                if s.param_binding == name {
                    return induction_bound_from_obj(name, &s.induc_from);
                }
                objs.push(&s.induc_from);
                facts.extend(s.to_prove.iter().cloned().map(Into::into));
                bodies.push(&s.proof);
                bodies.extend(s.base_proof.as_deref());
                bodies.extend(s.step_proof.as_deref());
            }
            ByStmt::ByExtensionStmt(s) => {
                objs.extend([&s.left, &s.right]);
                bodies.push(&s.proof);
            }
            ByStmt::ByFnExtensionStmt(s) => {
                objs.extend([&s.left, &s.right]);
                bodies.push(&s.proof);
            }
            ByStmt::ByDefStmt(s) => facts.push(s.fact.clone().into()),
            ByStmt::ByThmStmt(s) => {
                if let TheoremCallArguments::Parenthesized(args) = &s.call.arguments {
                    objs.extend(args);
                }
                facts.push(s.selected_fact.clone().into());
            }
        },
        Stmt::Register(s) => facts.push(match s {
            RegisterStmt::RegisterTransitivePropStmt(s) => Fact::ForallFact(s.forall_fact.clone()),
            RegisterStmt::RegisterSymmetricPropStmt(s) => Fact::ForallFact(s.forall_fact.clone()),
            RegisterStmt::RegisterReflexivePropStmt(s) => Fact::ForallFact(s.forall_fact.clone()),
        }),
        Stmt::Witness(s) => match s {
            WitnessStmt::WitnessExistFact(s) => {
                objs.extend(&s.equal_tos);
                facts.push(crate::ast::fact::exist_shaped_fact_to_fact(
                    &s.exist_shaped_fact_in_witness,
                ));
                bodies.push(&s.proof);
            }
            WitnessStmt::WitnessAtomicFact(s) => {
                objs.extend(&s.witnesses);
                facts.push(s.atomic_fact.clone().into());
                bodies.push(&s.proof);
            }
            WitnessStmt::WitnessNonemptySet(s) => {
                objs.extend([&s.obj, &s.set]);
                bodies.push(&s.proof);
            }
        },
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
            facts.push(s.fact.clone());
            bodies.push(&s.proof);
        }
        Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => bodies.push(&s.proof),
        Stmt::Command(CommandStmt::EvalStmt(s)) => objs.push(&s.obj_to_eval),
    }
    objs.into_iter()
        .find_map(|o| induction_bound_from_obj(name, o))
        .or_else(|| {
            facts
                .iter()
                .find_map(|f| induction_bound_from_fact(name, f))
        })
        .or_else(|| {
            bodies
                .into_iter()
                .flatten()
                .find_map(|s| induction_bound_from_stmt(name, s))
        })
}

fn induction_bound_from_fact(name: &str, fact: &Fact) -> Option<crate::ast::names::BoundName> {
    use crate::ast::fact::*;
    match fact {
        Fact::ForallFact(f) => {
            if f.typed_parameters
                .groups
                .iter()
                .any(|g| g.params.iter().any(|p| p.name == name))
            {
                return None;
            }
            induction_bound_from_typed_params(name, &f.typed_parameters)
                .or_else(|| {
                    f.dom_facts
                        .iter()
                        .find_map(|f| induction_bound_from_fact(name, f))
                })
                .or_else(|| recover_induction_param(name, &f.then_facts, &[]))
        }
        Fact::ForallFactWithIff(f) => {
            if f.forall_fact
                .typed_parameters
                .groups
                .iter()
                .any(|g| g.params.iter().any(|p| p.name == name))
            {
                return None;
            }
            induction_bound_from_fact(name, &Fact::ForallFact(f.forall_fact.clone()))
                .or_else(|| recover_induction_param(name, &f.iff_facts, &[]))
        }
        Fact::NotForall(f) => {
            if f.typed_parameters
                .groups
                .iter()
                .any(|g| g.params.iter().any(|p| p.name == name))
            {
                return None;
            }
            induction_bound_from_typed_params(name, &f.typed_parameters).or_else(|| {
                f.dom_facts
                    .iter()
                    .chain(&f.then_facts)
                    .flat_map(quantifier_free_fact_args_ref)
                    .find_map(|o| induction_bound_from_obj(name, o))
            })
        }
        Fact::AtomicFact(a) => atomic_fact_args_ref(a)
            .into_iter()
            .find_map(|o| induction_bound_from_obj(name, o)),
        Fact::AndFact(a) => a
            .facts
            .iter()
            .flat_map(atomic_fact_args_ref)
            .find_map(|o| induction_bound_from_obj(name, o)),
        Fact::ChainFact(a) => a
            .objs
            .iter()
            .find_map(|o| induction_bound_from_obj(name, o)),
        Fact::OrFact(a) => or_fact_args_ref(a)
            .into_iter()
            .find_map(|o| induction_bound_from_obj(name, o)),
        Fact::ExistFact(a) | Fact::ExistUniqueFact(a) | Fact::NotExistFact(a) => {
            if a.typed_parameters
                .groups
                .iter()
                .any(|g| g.params.iter().any(|p| p.name == name))
            {
                return None;
            }
            plain_exist_fact_free_args_ref(a)
                .into_iter()
                .find_map(|o| induction_bound_from_obj(name, o))
        }
    }
}

fn induction_bound_from_typed_params(
    name: &str,
    params: &crate::ast::param::TypedParameterList,
) -> Option<crate::ast::names::BoundName> {
    params
        .groups
        .iter()
        .find_map(|group| match &group.param_type {
            crate::ast::param::ParamType::Obj(obj) => induction_bound_from_obj(name, obj),
            crate::ast::param::ParamType::Set(_)
            | crate::ast::param::ParamType::NonemptySet(_)
            | crate::ast::param::ParamType::FiniteSet(_) => None,
        })
}

fn induction_bound_from_definition(
    name: &str,
    stmt: &crate::ast::stmt::DefinitionStmt,
) -> Option<crate::ast::names::BoundName> {
    use crate::ast::stmt::*;
    let mut objs: Vec<&crate::ast::obj::Obj> = Vec::new();
    let mut facts: Vec<Fact> = Vec::new();
    let mut bodies: Vec<&[Stmt]> = Vec::new();
    let mut typed_params = Vec::new();
    let mut clauses = Vec::new();
    match stmt {
        DefinitionStmt::DefineObj(s) => match s {
            DefineObjStmt::LetObjStmt(s) => objs.push(&s.value),
            DefineObjStmt::HaveObjInNonemptySetStmt(s) => typed_params.push(&s.param_def),
            DefineObjStmt::HaveObjEqualStmt(s) => {
                typed_params.push(&s.param_def);
                objs.extend(&s.objs_equal_to);
            }
            DefineObjStmt::HaveObjByExistFactsStmt(s) => {
                typed_params.push(&s.param_def);
                facts.extend(
                    s.facts
                        .iter()
                        .cloned()
                        .map(crate::instantiate::quantifier_free_fact_to_fact),
                );
            }
            DefineObjStmt::ObtainObjFromExistFact(s) => {
                facts.push(crate::ast::fact::exist_shaped_fact_to_fact(&s.fact))
            }
            DefineObjStmt::ObtainObjFromAtomicFact(s) => facts.push(s.fact.clone().into()),
            DefineObjStmt::HaveByPreimageStmt(s) => facts.push(s.range_membership.clone().into()),
            DefineObjStmt::HaveByReplacementAxiomStmt(s) => objs.push(&s.source_set),
        },
        DefinitionStmt::HaveFnEqualStmt(s) => {
            return induction_bound_from_anonymous_fn(name, &s.equal_to_anonymous_fn)
        }
        DefinitionStmt::HaveFnEqualCaseByCaseStmt(s) => {
            clauses.push(&s.fn_set_clause);
            facts.extend(s.cases.iter().map(and_chain_as_fact));
            objs.extend(&s.equal_tos);
        }
        DefinitionStmt::DefAlgoByCasesStmt(s) => {
            clauses.push(&s.fn_set_clause);
            facts.extend(s.cases.iter().map(and_chain_as_fact));
            objs.extend(&s.equal_tos);
        }
        DefinitionStmt::HaveFnByInducStmt(s) => {
            if let Some(p) = induction_bound_from_case_list(name, &s.cases) {
                return Some(p);
            }
            clauses.push(&s.fn_set_clause);
            objs.extend([&s.measure, &s.lower_bound]);
        }
        DefinitionStmt::DefAlgoByInducStmt(s) => {
            if let Some(p) = induction_bound_from_case_list(name, &s.cases) {
                return Some(p);
            }
            clauses.push(&s.fn_set_clause);
            objs.extend([&s.measure, &s.lower_bound]);
        }
        DefinitionStmt::HaveFnByForallExistUniqueStmt(s) => {
            facts.push(Fact::ForallFact(s.forall.clone()))
        }
        DefinitionStmt::DefPropStmt(s) => {
            typed_params.push(&s.typed_parameters);
            facts.extend(s.iff_facts.clone());
        }
        DefinitionStmt::DefAbstractPropStmt(_) => {}
        DefinitionStmt::DefTemplateStmt(s) => {
            typed_params.push(&s.template_arg_def);
            facts.extend(
                s.template_arg_dom
                    .iter()
                    .cloned()
                    .map(crate::instantiate::quantifier_free_fact_to_fact),
            );
            let definition = match &s.template_def_stmt {
                TemplateDefEnum::HaveObjInNonemptySetStmt(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::HaveObjInNonemptySetStmt(s.clone()))
                }
                TemplateDefEnum::HaveObjEqualStmt(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::HaveObjEqualStmt(s.clone()))
                }
                TemplateDefEnum::HaveObjByExistFactsStmt(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::HaveObjByExistFactsStmt(s.clone()))
                }
                TemplateDefEnum::HaveByReplacementAxiomStmt(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::HaveByReplacementAxiomStmt(s.clone()))
                }
                TemplateDefEnum::TrustHaveStmt(s) => {
                    return induction_bound_from_stmt(
                        name,
                        &Stmt::Trust(TrustBoundaryStmt::TrustHaveStmt(s.clone())),
                    )
                }
                TemplateDefEnum::ObtainObjFromExistFact(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromExistFact(s.clone()))
                }
                TemplateDefEnum::ObtainObjFromAtomicFact(s) => {
                    DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromAtomicFact(s.clone()))
                }
                TemplateDefEnum::HaveFnEqualStmt(s) => DefinitionStmt::HaveFnEqualStmt(s.clone()),
                TemplateDefEnum::HaveFnEqualCaseByCaseStmt(s) => {
                    DefinitionStmt::HaveFnEqualCaseByCaseStmt(s.clone())
                }
                TemplateDefEnum::HaveFnByInducStmt(s) => {
                    DefinitionStmt::HaveFnByInducStmt(s.clone())
                }
                TemplateDefEnum::HaveFnByForallExistUniqueStmt(s) => {
                    DefinitionStmt::HaveFnByForallExistUniqueStmt(s.clone())
                }
            };
            if let Some(p) = induction_bound_from_definition(name, &definition) {
                return Some(p);
            }
        }
        DefinitionStmt::DefStructStmt(s) => {
            if let Some((params, dom)) = &s.param_def_with_dom {
                typed_params.push(params);
                facts.extend(
                    dom.iter()
                        .cloned()
                        .map(crate::instantiate::quantifier_free_fact_to_fact),
                );
            }
            objs.extend(s.fields.iter().map(|f| &f.field_type));
            facts.extend(s.equivalent_facts.clone());
        }
        DefinitionStmt::DefThmStmt(s) => {
            facts.push(s.fact.clone());
            bodies.push(&s.prove_process);
        }
        DefinitionStmt::AxiomStmt(s) => facts.push(Fact::ForallFact(s.forall_fact.clone())),
        DefinitionStmt::DefStrategyStmt(s) => {
            facts.push(Fact::ForallFact(s.forall_fact.clone()));
            bodies.push(&s.prove_process);
        }
    }
    typed_params
        .into_iter()
        .find_map(|p| induction_bound_from_typed_params(name, p))
        .or_else(|| {
            clauses.into_iter().find_map(|clause| {
                clause
                    .set_bound_parameters
                    .groups
                    .iter()
                    .find_map(|g| induction_bound_from_obj(name, &g.param_type))
                    .or_else(|| {
                        clause
                            .dom_facts
                            .iter()
                            .flat_map(crate::ast::fact::quantifier_free_fact_args_ref)
                            .find_map(|o| induction_bound_from_obj(name, o))
                    })
                    .or_else(|| induction_bound_from_obj(name, &clause.ret_set))
            })
        })
        .or_else(|| {
            objs.into_iter()
                .find_map(|o| induction_bound_from_obj(name, o))
        })
        .or_else(|| {
            facts
                .iter()
                .find_map(|f| induction_bound_from_fact(name, f))
        })
        .or_else(|| {
            bodies
                .into_iter()
                .flatten()
                .find_map(|s| induction_bound_from_stmt(name, s))
        })
}

fn induction_bound_from_case_list(
    name: &str,
    cases: &[crate::ast::stmt::HaveFnByInducCase],
) -> Option<crate::ast::names::BoundName> {
    for case in cases {
        if let Some(p) = induction_bound_from_fact(name, &and_chain_as_fact(&case.case_fact)) {
            return Some(p);
        }
        let found = match &case.body {
            crate::ast::stmt::HaveFnByInducCaseBody::EqualTo(o) => {
                induction_bound_from_obj(name, o)
            }
            crate::ast::stmt::HaveFnByInducCaseBody::NestedCases(cases) => {
                induction_bound_from_case_list(name, cases)
            }
        };
        if found.is_some() {
            return found;
        }
    }
    None
}
