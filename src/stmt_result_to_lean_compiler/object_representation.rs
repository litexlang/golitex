use super::function_contracts::*;
use crate::prelude::*;

/// A structural compiler representation of one Litex object.
///
/// The tree preserves source object syntax and symbol identity without fixing
/// a universal target carrier. Compiler selects Mathlib-native carriers while
/// retaining numeric, user-set, and function membership as explicit evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanTargetObjectRepresentation {
    Symbol {
        symbol_id: SymbolId,
        name: String,
    },
    Number {
        normalized_value: String,
    },
    Constant(LeanTargetConstantObject),
    StandardSet(LeanTargetStandardSet),
    /// A Litex function set carries an exact source application contract; a
    /// backend decides its native carrier representation.
    FunctionSet {
        function: Box<LeanTargetFunctionTypeRepresentation>,
    },
    /// A source set-builder object. The binder stays owned by this node; its
    /// identity must not leak into the surrounding context.
    SetBuilder(Box<LeanTargetSetBuilderRepresentation>),
    /// An anonymous source function object. Its application contract and
    /// output-membership certificate remain explicit proof evidence.
    AnonymousFunction(Box<LeanTargetAnonymousFunctionRepresentation>),
    /// Exact Litex application layers; target currying must not erase them.
    FunctionApplication(LeanTargetFunctionApplicationRepresentation),
    /// Exact image/range of one unary source function.
    FunctionRange {
        function: Box<LeanTargetObjectRepresentation>,
    },
    /// Native-real interval with independently open or closed endpoints.
    RealInterval {
        start: Box<LeanTargetObjectRepresentation>,
        end: Box<LeanTargetObjectRepresentation>,
        left_closed: bool,
        right_closed: bool,
    },
    /// Native-real one-sided interval. `extends_right` means the endpoint is
    /// the left bound; otherwise it is the right bound.
    RealRay {
        endpoint: Box<LeanTargetObjectRepresentation>,
        closed: bool,
        extends_right: bool,
    },
    ClosedRange {
        start: Box<LeanTargetObjectRepresentation>,
        end: Box<LeanTargetObjectRepresentation>,
    },
    Range {
        start: Box<LeanTargetObjectRepresentation>,
        end: Box<LeanTargetObjectRepresentation>,
    },
    CartesianProduct {
        factors: Vec<LeanTargetObjectRepresentation>,
    },
    GeneralCartesianProduct {
        index_set: Box<LeanTargetObjectRepresentation>,
        family_set: Box<LeanTargetObjectRepresentation>,
        family_function: Box<LeanTargetObjectRepresentation>,
    },
    SequenceSet {
        values: Box<LeanTargetObjectRepresentation>,
        length: Option<Box<LeanTargetObjectRepresentation>>,
    },
    MatrixSet {
        values: Box<LeanTargetObjectRepresentation>,
        row_count: Box<LeanTargetObjectRepresentation>,
        column_count: Box<LeanTargetObjectRepresentation>,
    },
    Aggregate {
        /// Parser-owned identity used to select the exact aggregate WD use.
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        /// Structural identity used only after occurrence selection.
        semantic_key: String,
        kind: LeanTargetAggregateObjectConstructor,
        arguments: Vec<LeanTargetObjectRepresentation>,
    },
    TupleDimension(Box<LeanTargetObjectRepresentation>),
    IndexedAccess {
        object: Box<LeanTargetObjectRepresentation>,
        index: Box<LeanTargetObjectRepresentation>,
    },
    BuiltinApp {
        /// Parser-owned identity used to join a proof-carrying syntax node to
        /// its exact verifier-owned WD use. Non-proof-carrying or synthetic
        /// builtin nodes may leave this absent.
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        /// Structural identity used only to validate that the cited WD node
        /// still represents the same object; it is not used for selection.
        semantic_key: String,
        operator: LeanTargetBuiltinObjectOperator,
        arguments: Vec<LeanTargetObjectRepresentation>,
    },
    Collection {
        /// Parser-owned identity used to select the exact constructor WD use.
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        /// Structural identity used only for post-selection validation.
        semantic_key: String,
        constructor: LeanTargetCollectionObjectConstructor,
        items: Vec<LeanTargetObjectRepresentation>,
    },
}

#[derive(Clone)]
pub struct LeanTargetSetBuilderRepresentation {
    pub semantic_key: String,
    pub symbol_id: SymbolId,
    pub name: String,
    pub set: Box<LeanTargetObjectRepresentation>,
    pub facts: Vec<Fact>,
}

impl PartialEq for LeanTargetSetBuilderRepresentation {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key == other.semantic_key
    }
}

impl Eq for LeanTargetSetBuilderRepresentation {}

impl std::fmt::Debug for LeanTargetSetBuilderRepresentation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LeanTargetSetBuilderRepresentation")
            .field("semantic_key", &self.semantic_key)
            .field("symbol_id", &self.symbol_id)
            .field("name", &self.name)
            .field("set", &self.set)
            .field(
                "facts",
                &self
                    .facts
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

#[derive(Clone)]
pub struct LeanTargetAnonymousFunctionRepresentation {
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
    /// Structural identity used only after occurrence selection to detect a
    /// retargeted representation node; it is never a certificate-selection key.
    pub semantic_key: String,
    pub function: LeanTargetFunctionTypeRepresentation,
    /// Keep the source body until a Result-owned binder context is active.
    /// Definition replay may synthesize occurrence-free application nodes;
    /// context-free IR lowering cannot select their verifier certificates.
    pub source_body: Obj,
}

impl PartialEq for LeanTargetAnonymousFunctionRepresentation {
    fn eq(&self, other: &Self) -> bool {
        self.source_occurrence_id == other.source_occurrence_id
            && self.semantic_key == other.semantic_key
            && self.function == other.function
            && obj_equality_key(&self.source_body) == obj_equality_key(&other.source_body)
    }
}

impl Eq for LeanTargetAnonymousFunctionRepresentation {}

impl std::fmt::Debug for LeanTargetAnonymousFunctionRepresentation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LeanTargetAnonymousFunctionRepresentation")
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("semantic_key", &self.semantic_key)
            .field("function", &self.function)
            .field("source_body", &self.source_body.to_string())
            .finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanTargetConstantObject {
    ImaginaryUnit,
    EulerNumber,
    Pi,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanTargetStandardSet {
    PositiveNatural,
    Natural,
    Rational,
    Integer,
    Real,
    Complex,
    PositiveRational,
    PositiveReal,
    NegativeRational,
    NegativeInteger,
    NegativeReal,
    NonzeroRational,
    NonzeroInteger,
    NonzeroReal,
    NonzeroComplex,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanTargetBuiltinObjectOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gcd,
    Lcm,
    Floor,
    Ceil,
    Min,
    Max,
    Exp,
    Ln,
    Sign,
    Factorial,
    Pow,
    Abs,
    Sin,
    Arcsin,
    Cos,
    Tan,
    Cot,
    RealPart,
    ImaginaryPart,
    ComplexAbs,
    Sqrt,
    Log,
    Union,
    Intersect,
    SetMinus,
    BigUnion,
    BigIntersect,
    PowerSet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanTargetCollectionObjectConstructor {
    ListSet,
    Tuple,
    SequenceLiteral,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanTargetAggregateObjectConstructor {
    Sum,
    Product,
    FiniteSetSum,
    FiniteSetProduct,
    Reduce,
    FiniteSetReduce,
}

impl LeanTargetObjectRepresentation {
    pub fn lower(obj: &Obj) -> Result<Self, String> {
        match obj {
            Obj::Atom(atom) => lower_atom(atom),
            Obj::Number(number) => Ok(LeanTargetObjectRepresentation::Number {
                normalized_value: number.normalized_value.clone(),
            }),
            Obj::ImaginaryUnit(_) => Ok(LeanTargetObjectRepresentation::Constant(
                LeanTargetConstantObject::ImaginaryUnit,
            )),
            Obj::EulerNumber(_) => Ok(LeanTargetObjectRepresentation::Constant(
                LeanTargetConstantObject::EulerNumber,
            )),
            Obj::Pi(_) => Ok(LeanTargetObjectRepresentation::Constant(
                LeanTargetConstantObject::Pi,
            )),
            Obj::StandardSet(set) => Ok(LeanTargetObjectRepresentation::StandardSet(set.into())),
            Obj::FnSet(function_set) => Ok(LeanTargetObjectRepresentation::FunctionSet {
                function: Box::new(LeanTargetFunctionTypeRepresentation::lower(function_set)?),
            }),
            Obj::SetBuilder(set_builder) => {
                let set = LeanTargetObjectRepresentation::lower(set_builder.param_set.as_ref())?;
                Ok(LeanTargetObjectRepresentation::SetBuilder(Box::new(
                    LeanTargetSetBuilderRepresentation {
                        semantic_key: obj_equality_key(&set_builder.clone().into()),
                        symbol_id: set_builder.param_binding.id(),
                        name: set_builder.param_binding.name().to_string(),
                        set: Box::new(set),
                        facts: set_builder
                            .facts
                            .iter()
                            .map(QuantifierFreeFact::from_ref_to_cloned_fact)
                            .collect(),
                    },
                )))
            }
            Obj::AnonymousFn(function) => Ok(LeanTargetObjectRepresentation::AnonymousFunction(Box::new(
                LeanTargetAnonymousFunctionRepresentation {
                    source_occurrence_id: function.source_occurrence_id,
                    semantic_key: obj_equality_key(obj),
                    function: LeanTargetFunctionTypeRepresentation::lower_anonymous(function)?,
                    source_body: function.equal_to.as_ref().clone(),
                },
            ))),
            Obj::FnObj(application) => lower_function_application(application),
            Obj::FnRange(range) => Ok(LeanTargetObjectRepresentation::FunctionRange {
                function: Box::new(LeanTargetObjectRepresentation::lower(
                    range.function.as_ref(),
                )?),
            }),
            Obj::IntervalObj(interval) => Ok(LeanTargetObjectRepresentation::RealInterval {
                start: Box::new(LeanTargetObjectRepresentation::lower(interval.start())?),
                end: Box::new(LeanTargetObjectRepresentation::lower(interval.end())?),
                left_closed: interval.left_closed(),
                right_closed: interval.right_closed(),
            }),
            Obj::OneSideInfinityIntervalObj(interval) => {
                Ok(LeanTargetObjectRepresentation::RealRay {
                    endpoint: Box::new(LeanTargetObjectRepresentation::lower(interval.start())?),
                    closed: interval.left_closed() || interval.right_closed(),
                    extends_right: interval.left_bounded(),
                })
            }
            Obj::ClosedRange(range) => Ok(LeanTargetObjectRepresentation::ClosedRange {
                start: Box::new(LeanTargetObjectRepresentation::lower(range.start.as_ref())?),
                end: Box::new(LeanTargetObjectRepresentation::lower(range.end.as_ref())?),
            }),
            Obj::Range(range) => Ok(LeanTargetObjectRepresentation::Range {
                start: Box::new(LeanTargetObjectRepresentation::lower(range.start.as_ref())?),
                end: Box::new(LeanTargetObjectRepresentation::lower(range.end.as_ref())?),
            }),
            Obj::Cart(product) => Ok(LeanTargetObjectRepresentation::CartesianProduct {
                factors: product
                    .args
                    .iter()
                    .map(|factor| LeanTargetObjectRepresentation::lower(factor.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Obj::GeneralCart(product) => Ok(LeanTargetObjectRepresentation::GeneralCartesianProduct {
                index_set: Box::new(LeanTargetObjectRepresentation::lower(product.index_set.as_ref())?),
                family_set: Box::new(LeanTargetObjectRepresentation::lower(product.family_set.as_ref())?),
                family_function: Box::new(LeanTargetObjectRepresentation::lower(product.family_fn.as_ref())?),
            }),
            Obj::FiniteSeqSet(sequence) => Ok(LeanTargetObjectRepresentation::SequenceSet {
                values: Box::new(LeanTargetObjectRepresentation::lower(sequence.set.as_ref())?),
                length: Some(Box::new(LeanTargetObjectRepresentation::lower(sequence.n.as_ref())?)),
            }),
            Obj::SeqSet(sequence) => Ok(LeanTargetObjectRepresentation::SequenceSet {
                values: Box::new(LeanTargetObjectRepresentation::lower(sequence.set.as_ref())?),
                length: None,
            }),
            Obj::MatrixSet(matrix) => Ok(LeanTargetObjectRepresentation::MatrixSet {
                values: Box::new(LeanTargetObjectRepresentation::lower(matrix.set.as_ref())?),
                row_count: Box::new(LeanTargetObjectRepresentation::lower(matrix.row_len.as_ref())?),
                column_count: Box::new(LeanTargetObjectRepresentation::lower(matrix.col_len.as_ref())?),
            }),
            Obj::Sum(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::Sum,
                [
                    value.start.as_ref(),
                    value.end.as_ref(),
                    value.func.as_ref(),
                ],
            ),
            Obj::Product(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::Product,
                [
                    value.start.as_ref(),
                    value.end.as_ref(),
                    value.func.as_ref(),
                ],
            ),
            Obj::SumOfFiniteSet(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::FiniteSetSum,
                [value.set.as_ref(), value.func.as_ref()],
            ),
            Obj::ProductOfFiniteSet(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::FiniteSetProduct,
                [value.set.as_ref(), value.func.as_ref()],
            ),
            Obj::Reduce(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::Reduce,
                [
                    value.start.as_ref(),
                    value.end.as_ref(),
                    value.func.as_ref(),
                    value.op.as_ref(),
                    value.seed.as_ref(),
                ],
            ),
            Obj::FiniteSetReduce(value) => aggregate(
                obj,
                LeanTargetAggregateObjectConstructor::FiniteSetReduce,
                [
                    value.set.as_ref(),
                    value.func.as_ref(),
                    value.op.as_ref(),
                    value.seed.as_ref(),
                ],
            ),
            Obj::TupleDim(dimension) => Ok(LeanTargetObjectRepresentation::TupleDimension(Box::new(
                LeanTargetObjectRepresentation::lower(dimension.arg.as_ref())?,
            ))),
            Obj::ObjAtIndex(access) => Ok(LeanTargetObjectRepresentation::IndexedAccess {
                object: Box::new(LeanTargetObjectRepresentation::lower(access.obj.as_ref())?),
                index: Box::new(LeanTargetObjectRepresentation::lower(access.index.as_ref())?),
            }),
            Obj::Add(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Add,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Sub(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Sub,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mul(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Mul,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Div(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Div,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mod(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Mod,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Quot(_) => Err(
                "Litex-to-Lean object representation does not yet support the builtin `quot` object".to_string(),
            ),
            Obj::Gcd(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Gcd,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Lcm(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Lcm,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Floor(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Floor,
                value.arg.as_ref(),
            ),
            Obj::Ceil(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Ceil,
                value.arg.as_ref(),
            ),
            Obj::Min(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Min,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Max(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Max,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Exp(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Exp,
                value.arg.as_ref(),
            ),
            Obj::Ln(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Ln,
                value.arg.as_ref(),
            ),
            Obj::Sign(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Sign,
                value.arg.as_ref(),
            ),
            Obj::Factorial(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Factorial,
                value.arg.as_ref(),
            ),
            Obj::Pow(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Pow,
                value.base.as_ref(),
                value.exponent.as_ref(),
            ),
            Obj::Abs(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Abs,
                value.arg.as_ref(),
            ),
            Obj::Sin(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Sin,
                value.arg.as_ref(),
            ),
            Obj::Arcsin(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Arcsin,
                value.arg.as_ref(),
            ),
            Obj::Cos(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Cos,
                value.arg.as_ref(),
            ),
            Obj::Tan(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Tan,
                value.arg.as_ref(),
            ),
            Obj::Cot(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Cot,
                value.arg.as_ref(),
            ),
            Obj::RealPart(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::RealPart,
                value.arg.as_ref(),
            ),
            Obj::ImaginaryPart(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::ImaginaryPart,
                value.arg.as_ref(),
            ),
            Obj::ComplexAbs(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::ComplexAbs,
                value.arg.as_ref(),
            ),
            Obj::Sqrt(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::Sqrt,
                value.arg.as_ref(),
            ),
            Obj::Log(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Log,
                value.base.as_ref(),
                value.arg.as_ref(),
            ),
            Obj::Union(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Union,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Intersect(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::Intersect,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::SetMinus(value) => binary(
                obj,
                LeanTargetBuiltinObjectOperator::SetMinus,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::BigUnion(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::BigUnion,
                value.left.as_ref(),
            ),
            Obj::BigIntersect(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::BigIntersect,
                value.left.as_ref(),
            ),
            Obj::IndexUnion(_) => Err(
                "Litex-to-Lean does not yet support `index_union`; native indexed-set-family semantics are intentionally deferred"
                    .to_string(),
            ),
            Obj::IndexIntersect(_) => Err(
                "Litex-to-Lean does not yet support `index_intersect`; native indexed-set-family semantics are intentionally deferred"
                    .to_string(),
            ),
            Obj::PowerSet(value) => unary(
                obj,
                LeanTargetBuiltinObjectOperator::PowerSet,
                value.set.as_ref(),
            ),
            Obj::ListSet(value) => Ok(LeanTargetObjectRepresentation::Collection {
                source_occurrence_id: value.source_occurrence_id,
                semantic_key: obj_equality_key(obj),
                constructor: LeanTargetCollectionObjectConstructor::ListSet,
                items: value
                    .list
                    .iter()
                    .map(|item| LeanTargetObjectRepresentation::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Obj::Tuple(value) => Ok(LeanTargetObjectRepresentation::Collection {
                source_occurrence_id: None,
                semantic_key: obj_equality_key(obj),
                constructor: LeanTargetCollectionObjectConstructor::Tuple,
                items: value
                    .args
                    .iter()
                    .map(|item| LeanTargetObjectRepresentation::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Obj::FiniteSeqListObj(value) => Ok(LeanTargetObjectRepresentation::Collection {
                source_occurrence_id: None,
                semantic_key: obj_equality_key(obj),
                constructor: LeanTargetCollectionObjectConstructor::SequenceLiteral,
                items: value
                    .objs
                    .iter()
                    .map(|item| LeanTargetObjectRepresentation::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Err(format!(
                "Litex-to-Lean object representation does not support {:?} object `{}`",
                other.kind(),
                other
            )),
        }
    }
}

fn lower_function_application(
    application: &FnObj,
) -> Result<LeanTargetObjectRepresentation, String> {
    let source_occurrence_id = application.source_occurrence_id.ok_or_else(|| {
        format!(
            "Litex-to-Lean requires parser-owned occurrence identity for application `{}`",
            application
        )
    })?;
    let head_obj: Obj = (*application.head).clone().into();
    let head = LeanTargetObjectRepresentation::lower(&head_obj)?;
    let argument_layers = application
        .body
        .iter()
        .map(|layer| {
            layer
                .iter()
                .map(|argument| LeanTargetObjectRepresentation::lower(argument.as_ref()))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let source_argument_layers = application
        .body
        .iter()
        .map(|layer| {
            layer
                .iter()
                .map(|argument| argument.as_ref().clone())
                .collect::<Vec<_>>()
        })
        .collect();
    Ok(LeanTargetObjectRepresentation::FunctionApplication(
        LeanTargetFunctionApplicationRepresentation {
            head: Box::new(head),
            source_occurrence_id,
            source_application: application.clone().into(),
            argument_layers,
            source_argument_layers,
        },
    ))
}

fn lower_atom(atom: &AtomObj) -> Result<LeanTargetObjectRepresentation, String> {
    let Some(symbol) = atom.symbol_ref() else {
        return Err(format!(
            "Litex-to-Lean object representation requires a resolved SymbolId for atom `{}`",
            atom
        ));
    };
    Ok(LeanTargetObjectRepresentation::Symbol {
        symbol_id: symbol.id(),
        name: symbol.display_name().to_string(),
    })
}

fn unary(
    source: &Obj,
    operator: LeanTargetBuiltinObjectOperator,
    argument: &Obj,
) -> Result<LeanTargetObjectRepresentation, String> {
    Ok(LeanTargetObjectRepresentation::BuiltinApp {
        source_occurrence_id: source.source_occurrence_id(),
        semantic_key: obj_equality_key(source),
        operator,
        arguments: vec![LeanTargetObjectRepresentation::lower(argument)?],
    })
}

fn binary(
    source: &Obj,
    operator: LeanTargetBuiltinObjectOperator,
    left: &Obj,
    right: &Obj,
) -> Result<LeanTargetObjectRepresentation, String> {
    Ok(LeanTargetObjectRepresentation::BuiltinApp {
        source_occurrence_id: source.source_occurrence_id(),
        semantic_key: obj_equality_key(source),
        operator,
        arguments: vec![
            LeanTargetObjectRepresentation::lower(left)?,
            LeanTargetObjectRepresentation::lower(right)?,
        ],
    })
}

fn aggregate<'a, const N: usize>(
    source: &Obj,
    kind: LeanTargetAggregateObjectConstructor,
    arguments: [&'a Obj; N],
) -> Result<LeanTargetObjectRepresentation, String> {
    Ok(LeanTargetObjectRepresentation::Aggregate {
        source_occurrence_id: source.source_occurrence_id(),
        semantic_key: obj_equality_key(source),
        kind,
        arguments: arguments
            .into_iter()
            .map(LeanTargetObjectRepresentation::lower)
            .collect::<Result<Vec<_>, _>>()?,
    })
}

impl From<&StandardSet> for LeanTargetStandardSet {
    fn from(value: &StandardSet) -> Self {
        match value {
            StandardSet::NPos => LeanTargetStandardSet::PositiveNatural,
            StandardSet::N => LeanTargetStandardSet::Natural,
            StandardSet::Q => LeanTargetStandardSet::Rational,
            StandardSet::Z => LeanTargetStandardSet::Integer,
            StandardSet::R => LeanTargetStandardSet::Real,
            StandardSet::C => LeanTargetStandardSet::Complex,
            StandardSet::QPos => LeanTargetStandardSet::PositiveRational,
            StandardSet::RPos => LeanTargetStandardSet::PositiveReal,
            StandardSet::QNeg => LeanTargetStandardSet::NegativeRational,
            StandardSet::ZNeg => LeanTargetStandardSet::NegativeInteger,
            StandardSet::RNeg => LeanTargetStandardSet::NegativeReal,
            StandardSet::QStar => LeanTargetStandardSet::NonzeroRational,
            StandardSet::ZStar => LeanTargetStandardSet::NonzeroInteger,
            StandardSet::RStar => LeanTargetStandardSet::NonzeroReal,
            StandardSet::CStar => LeanTargetStandardSet::NonzeroComplex,
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/stmt_result_to_lean_compiler/object_representation/tests.rs"]
mod tests;
