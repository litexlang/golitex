use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum AtomicFactTag {
    Normal,
    Equal,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    IsSet,
    IsNonemptySet,
    IsFiniteSet,
    In,
    IsCart,
    IsTuple,
    Subset,
    Superset,
    NotNormal,
    NotEqual,
    NotLess,
    NotGreater,
    NotLessEqual,
    NotGreaterEqual,
    NotIsSet,
    NotIsNonemptySet,
    NotIsFiniteSet,
    NotIn,
    NotIsCart,
    NotIsTuple,
    NotSubset,
    NotSuperset,
    FnEqualIn,
    FnEqual,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct AtomicFactHead {
    pub tag: AtomicFactTag,
    pub predicate: Option<(Option<String>, String)>,
    pub arity: usize,
}

pub(crate) fn atomic_fact_head(fact: &AtomicFact) -> AtomicFactHead {
    let (tag, predicate) = match fact {
        AtomicFact::NormalAtomicFact(fact) => (
            AtomicFactTag::Normal,
            Some(atomic_name_scalar(&fact.predicate)),
        ),
        AtomicFact::EqualFact(_) => (AtomicFactTag::Equal, None),
        AtomicFact::LessFact(_) => (AtomicFactTag::Less, None),
        AtomicFact::GreaterFact(_) => (AtomicFactTag::Greater, None),
        AtomicFact::LessEqualFact(_) => (AtomicFactTag::LessEqual, None),
        AtomicFact::GreaterEqualFact(_) => (AtomicFactTag::GreaterEqual, None),
        AtomicFact::IsSetFact(_) => (AtomicFactTag::IsSet, None),
        AtomicFact::IsNonemptySetFact(_) => (AtomicFactTag::IsNonemptySet, None),
        AtomicFact::IsFiniteSetFact(_) => (AtomicFactTag::IsFiniteSet, None),
        AtomicFact::InFact(_) => (AtomicFactTag::In, None),
        AtomicFact::IsCartFact(_) => (AtomicFactTag::IsCart, None),
        AtomicFact::IsTupleFact(_) => (AtomicFactTag::IsTuple, None),
        AtomicFact::SubsetFact(_) => (AtomicFactTag::Subset, None),
        AtomicFact::SupersetFact(_) => (AtomicFactTag::Superset, None),
        AtomicFact::NotNormalAtomicFact(fact) => (
            AtomicFactTag::NotNormal,
            Some(atomic_name_scalar(&fact.predicate)),
        ),
        AtomicFact::NotEqualFact(_) => (AtomicFactTag::NotEqual, None),
        AtomicFact::NotLessFact(_) => (AtomicFactTag::NotLess, None),
        AtomicFact::NotGreaterFact(_) => (AtomicFactTag::NotGreater, None),
        AtomicFact::NotLessEqualFact(_) => (AtomicFactTag::NotLessEqual, None),
        AtomicFact::NotGreaterEqualFact(_) => (AtomicFactTag::NotGreaterEqual, None),
        AtomicFact::NotIsSetFact(_) => (AtomicFactTag::NotIsSet, None),
        AtomicFact::NotIsNonemptySetFact(_) => (AtomicFactTag::NotIsNonemptySet, None),
        AtomicFact::NotIsFiniteSetFact(_) => (AtomicFactTag::NotIsFiniteSet, None),
        AtomicFact::NotInFact(_) => (AtomicFactTag::NotIn, None),
        AtomicFact::NotIsCartFact(_) => (AtomicFactTag::NotIsCart, None),
        AtomicFact::NotIsTupleFact(_) => (AtomicFactTag::NotIsTuple, None),
        AtomicFact::NotSubsetFact(_) => (AtomicFactTag::NotSubset, None),
        AtomicFact::NotSupersetFact(_) => (AtomicFactTag::NotSuperset, None),
        AtomicFact::FnEqualInFact(_) => (AtomicFactTag::FnEqualIn, None),
        AtomicFact::FnEqualFact(_) => (AtomicFactTag::FnEqual, None),
    };
    AtomicFactHead {
        tag,
        predicate,
        arity: fact.args_ref().len(),
    }
}

fn atomic_name_scalar(name: &AtomicName) -> (Option<String>, String) {
    match name {
        AtomicName::WithoutMod(name) => (None, name.clone()),
        AtomicName::WithMod(module, name) => (Some(module.clone()), name.clone()),
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) enum CanonicalScalar {
    Symbol(SymbolId),
    Text(String),
    AtomicName(Option<String>, String),
    Number(String),
    Variant(u8),
    Arity(usize),
}

pub(crate) struct CanonicalObjView<'a> {
    pub tag: ObjKind,
    pub scalars: Vec<CanonicalScalar>,
    pub children: Vec<&'a Obj>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CanonicalMatchError {
    pub message: String,
}

impl CanonicalMatchError {
    fn unsupported(obj: &Obj) -> Self {
        Self {
            message: format!(
                "canonical local-rule matching does not yet support fixed {:?} nodes",
                obj.kind()
            ),
        }
    }
}

fn atom_scalars(atom: &AtomObj) -> Vec<CanonicalScalar> {
    if let Some(symbol) = atom.symbol_ref() {
        return vec![CanonicalScalar::Symbol(symbol.id())];
    }
    match atom {
        AtomObj::Identifier(identifier) => vec![CanonicalScalar::Text(identifier.name.clone())],
        AtomObj::IdentifierWithMod(identifier) => vec![
            CanonicalScalar::Text(identifier.mod_name.clone()),
            CanonicalScalar::Text(identifier.name.clone()),
        ],
        _ => Vec::new(),
    }
}

fn standard_set_variant(set: &StandardSet) -> u8 {
    match set {
        StandardSet::NPos => 0,
        StandardSet::N => 1,
        StandardSet::Q => 2,
        StandardSet::Z => 3,
        StandardSet::R => 4,
        StandardSet::C => 5,
        StandardSet::QPos => 6,
        StandardSet::RPos => 7,
        StandardSet::QNeg => 8,
        StandardSet::ZNeg => 9,
        StandardSet::RNeg => 10,
        StandardSet::QStar => 11,
        StandardSet::ZStar => 12,
        StandardSet::RStar => 13,
        StandardSet::CStar => 14,
    }
}

fn atomic_name_canonical_scalar(name: &AtomicName) -> CanonicalScalar {
    let (module, name) = atomic_name_scalar(name);
    CanonicalScalar::AtomicName(module, name)
}

pub(crate) fn canonical_obj_view(obj: &Obj) -> Result<CanonicalObjView<'_>, CanonicalMatchError> {
    let empty = |tag| CanonicalObjView {
        tag,
        scalars: Vec::new(),
        children: Vec::new(),
    };
    let unary = |tag, child| CanonicalObjView {
        tag,
        scalars: Vec::new(),
        children: vec![child],
    };
    let binary = |tag, left, right| CanonicalObjView {
        tag,
        scalars: Vec::new(),
        children: vec![left, right],
    };

    Ok(match obj {
        Obj::Atom(atom) => CanonicalObjView {
            tag: obj.kind(),
            scalars: atom_scalars(atom),
            children: Vec::new(),
        },
        Obj::Number(number) => CanonicalObjView {
            tag: ObjKind::Number,
            scalars: vec![CanonicalScalar::Number(number.normalized_value.clone())],
            children: Vec::new(),
        },
        Obj::ImaginaryUnit(_) => empty(ObjKind::ImaginaryUnit),
        Obj::EulerNumber(_) => empty(ObjKind::EulerNumber),
        Obj::Pi(_) => empty(ObjKind::Pi),
        Obj::StandardSet(set) => CanonicalObjView {
            tag: ObjKind::StandardSet,
            scalars: vec![CanonicalScalar::Variant(standard_set_variant(set))],
            children: Vec::new(),
        },
        Obj::Add(x) => binary(ObjKind::Add, &x.left, &x.right),
        Obj::Sub(x) => binary(ObjKind::Sub, &x.left, &x.right),
        Obj::Mul(x) => binary(ObjKind::Mul, &x.left, &x.right),
        Obj::Div(x) => binary(ObjKind::Div, &x.left, &x.right),
        Obj::Mod(x) => binary(ObjKind::Mod, &x.left, &x.right),
        Obj::Quot(x) => binary(ObjKind::Quot, &x.left, &x.right),
        Obj::Gcd(x) => binary(ObjKind::Gcd, &x.left, &x.right),
        Obj::Lcm(x) => binary(ObjKind::Lcm, &x.left, &x.right),
        Obj::Min(x) => binary(ObjKind::Min, &x.left, &x.right),
        Obj::Max(x) => binary(ObjKind::Max, &x.left, &x.right),
        Obj::Union(x) => binary(ObjKind::Union, &x.left, &x.right),
        Obj::Intersect(x) => binary(ObjKind::Intersect, &x.left, &x.right),
        Obj::SetMinus(x) => binary(ObjKind::SetMinus, &x.left, &x.right),
        Obj::MatrixAdd(x) => binary(ObjKind::MatrixAdd, &x.left, &x.right),
        Obj::MatrixSub(x) => binary(ObjKind::MatrixSub, &x.left, &x.right),
        Obj::MatrixMul(x) => binary(ObjKind::MatrixMul, &x.left, &x.right),
        Obj::Pow(x) => binary(ObjKind::Pow, &x.base, &x.exponent),
        Obj::MatrixScalarMul(x) => binary(ObjKind::MatrixScalarMul, &x.scalar, &x.matrix),
        Obj::MatrixPow(x) => binary(ObjKind::MatrixPow, &x.base, &x.exponent),
        Obj::Floor(x) => unary(ObjKind::Floor, &x.arg),
        Obj::Ceil(x) => unary(ObjKind::Ceil, &x.arg),
        Obj::Exp(x) => unary(ObjKind::Exp, &x.arg),
        Obj::Ln(x) => unary(ObjKind::Ln, &x.arg),
        Obj::Sign(x) => unary(ObjKind::Sign, &x.arg),
        Obj::Factorial(x) => unary(ObjKind::Factorial, &x.arg),
        Obj::Abs(x) => unary(ObjKind::Abs, &x.arg),
        Obj::Sin(x) => unary(ObjKind::Sin, &x.arg),
        Obj::Cos(x) => unary(ObjKind::Cos, &x.arg),
        Obj::Tan(x) => unary(ObjKind::Tan, &x.arg),
        Obj::Cot(x) => unary(ObjKind::Cot, &x.arg),
        Obj::RealPart(x) => unary(ObjKind::RealPart, &x.arg),
        Obj::ImaginaryPart(x) => unary(ObjKind::ImaginaryPart, &x.arg),
        Obj::ComplexAbs(x) => unary(ObjKind::ComplexAbs, &x.arg),
        Obj::Sqrt(x) => unary(ObjKind::Sqrt, &x.arg),
        Obj::BigUnion(x) => unary(ObjKind::BigUnion, &x.left),
        Obj::BigIntersect(x) => unary(ObjKind::BigIntersect, &x.left),
        Obj::PowerSet(x) => unary(ObjKind::PowerSet, &x.set),
        Obj::SeqSet(x) => unary(ObjKind::SeqSet, &x.set),
        Obj::FiniteSetSize(x) => unary(ObjKind::FiniteSetSize, &x.set),
        Obj::FiniteSetMax(x) => unary(ObjKind::FiniteSetMax, &x.set),
        Obj::FiniteSetMin(x) => unary(ObjKind::FiniteSetMin, &x.set),
        Obj::FnRange(x) => unary(ObjKind::FnRange, &x.function),
        Obj::TupleDim(x) => unary(ObjKind::TupleDim, &x.arg),
        Obj::CartDim(x) => unary(ObjKind::CartDim, &x.set),
        Obj::Log(x) => binary(ObjKind::Log, &x.base, &x.arg),
        Obj::Proj(x) => binary(ObjKind::Proj, &x.set, &x.dim),
        Obj::ObjAtIndex(x) => binary(ObjKind::ObjAtIndex, &x.obj, &x.index),
        Obj::Range(x) => binary(ObjKind::Range, &x.start, &x.end),
        Obj::ClosedRange(x) => binary(ObjKind::ClosedRange, &x.start, &x.end),
        Obj::FiniteSeqSet(x) => binary(ObjKind::FiniteSeqSet, &x.set, &x.n),
        Obj::GeneralCart(x) => CanonicalObjView {
            tag: ObjKind::GeneralCart,
            scalars: Vec::new(),
            children: vec![&x.index_set, &x.family_set, &x.family_fn],
        },
        Obj::ListSet(x) => CanonicalObjView {
            tag: ObjKind::ListSet,
            scalars: vec![CanonicalScalar::Arity(x.list.len())],
            children: x.list.iter().map(Box::as_ref).collect(),
        },
        Obj::Cart(x) => CanonicalObjView {
            tag: ObjKind::Cart,
            scalars: vec![CanonicalScalar::Arity(x.args.len())],
            children: x.args.iter().map(Box::as_ref).collect(),
        },
        Obj::Tuple(x) => CanonicalObjView {
            tag: ObjKind::Tuple,
            scalars: vec![CanonicalScalar::Arity(x.args.len())],
            children: x.args.iter().map(Box::as_ref).collect(),
        },
        Obj::FiniteSeqListObj(x) => CanonicalObjView {
            tag: ObjKind::FiniteSeqListObj,
            scalars: vec![CanonicalScalar::Arity(x.objs.len())],
            children: x.objs.iter().map(Box::as_ref).collect(),
        },
        Obj::Sum(x) => CanonicalObjView {
            tag: ObjKind::Sum,
            scalars: Vec::new(),
            children: vec![&x.start, &x.end, &x.func],
        },
        Obj::Product(x) => CanonicalObjView {
            tag: ObjKind::Product,
            scalars: Vec::new(),
            children: vec![&x.start, &x.end, &x.func],
        },
        Obj::SumOfFiniteSet(x) => binary(ObjKind::SumOfFiniteSet, &x.set, &x.func),
        Obj::ProductOfFiniteSet(x) => binary(ObjKind::ProductOfFiniteSet, &x.set, &x.func),
        Obj::Reduce(x) => CanonicalObjView {
            tag: ObjKind::Reduce,
            scalars: Vec::new(),
            children: vec![&x.start, &x.end, &x.func, &x.op, &x.seed],
        },
        Obj::FiniteSetReduce(x) => CanonicalObjView {
            tag: ObjKind::FiniteSetReduce,
            scalars: Vec::new(),
            children: vec![&x.set, &x.func, &x.op, &x.seed],
        },
        Obj::MatrixSet(x) => CanonicalObjView {
            tag: ObjKind::MatrixSet,
            scalars: Vec::new(),
            children: vec![&x.set, &x.row_len, &x.col_len],
        },
        Obj::StructObj(x) => CanonicalObjView {
            tag: ObjKind::StructObj,
            scalars: vec![
                atomic_name_canonical_scalar(&x.name),
                CanonicalScalar::Arity(x.params.len()),
            ],
            children: x.params.iter().collect(),
        },
        Obj::ObjAsStructInstanceWithFieldAccess(x) => {
            let mut children = x.struct_obj.params.iter().collect::<Vec<_>>();
            children.push(x.obj.as_ref());
            CanonicalObjView {
                tag: ObjKind::ObjAsStructInstanceWithFieldAccess,
                scalars: vec![
                    atomic_name_canonical_scalar(&x.struct_obj.name),
                    CanonicalScalar::Arity(x.struct_obj.params.len()),
                    CanonicalScalar::Text(x.field_name.clone()),
                ],
                children,
            }
        }
        Obj::InstantiatedTemplateObj(x) => CanonicalObjView {
            tag: ObjKind::InstantiatedTemplateObj,
            scalars: vec![
                atomic_name_canonical_scalar(&x.template_name),
                CanonicalScalar::Symbol(x.symbol.id()),
                CanonicalScalar::Arity(x.args.len()),
            ],
            children: x.args.iter().collect(),
        },
        Obj::Replacement(x) => CanonicalObjView {
            tag: ObjKind::Replacement,
            scalars: vec![atomic_name_canonical_scalar(&x.prop_name)],
            children: vec![&x.source_set],
        },
        Obj::OneSideInfinityIntervalObj(x) => CanonicalObjView {
            tag: ObjKind::OneSideInfinityIntervalObj,
            scalars: vec![CanonicalScalar::Variant(match x {
                OneSideInfinityIntervalObj::LeftOpen(_) => 0,
                OneSideInfinityIntervalObj::LeftClosed(_) => 1,
                OneSideInfinityIntervalObj::RightOpen(_) => 2,
                OneSideInfinityIntervalObj::RightClosed(_) => 3,
            })],
            children: vec![x.start()],
        },
        Obj::IntervalObj(x) => CanonicalObjView {
            tag: ObjKind::IntervalObj,
            scalars: vec![CanonicalScalar::Variant(match x {
                IntervalObj::LeftOpenRightOpen(_) => 0,
                IntervalObj::LeftOpenRightClosed(_) => 1,
                IntervalObj::LeftClosedRightOpen(_) => 2,
                IntervalObj::LeftClosedRightClosed(_) => 3,
            })],
            children: vec![x.start(), x.end()],
        },
        // Fixed matching below binders and callable heads is intentionally
        // outside the local-schema language. A complete object may still be a
        // pattern-variable binding; the matcher stops before decomposing it.
        Obj::FnObj(_)
        | Obj::SetBuilder(_)
        | Obj::FnSet(_)
        | Obj::AnonymousFn(_)
        | Obj::MatrixListObj(_) => return Err(CanonicalMatchError::unsupported(obj)),
    })
}
