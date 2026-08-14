use crate::prelude::*;

/// A structural compiler representation of one Litex object.
///
/// The tree preserves source object syntax and symbol identity. Every node
/// lowers to the one target type `LitexObject`; membership in numeric, user,
/// and function sets is retained separately as `Litex.In` evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitexToLeanObjectIr {
    Symbol {
        symbol_id: SymbolId,
        name: String,
    },
    Number {
        normalized_value: String,
    },
    Constant(LitexToLeanConstantObjectIr),
    StandardSet(LitexToLeanStandardSetIr),
    /// A Litex function set is itself one `LitexObject`, carrying a restricted
    /// source application contract.
    FunctionSet {
        function: Box<LitexToLeanFunctionTypeIr>,
    },
    /// A source set-builder object. The binder stays owned by this node; its
    /// identity must not leak into the surrounding context.
    SetBuilder(Box<LitexToLeanSetBuilderIr>),
    /// An anonymous source function object. Its application contract and
    /// output-membership certificate remain explicit proof evidence.
    AnonymousFunction(Box<LitexToLeanAnonymousFunctionIr>),
    /// Exact Litex application layers; target currying must not erase them.
    FunctionApplication(LitexToLeanFunctionApplicationIr),
    ClosedRange {
        start: Box<LitexToLeanObjectIr>,
        end: Box<LitexToLeanObjectIr>,
    },
    TupleDimension(Box<LitexToLeanObjectIr>),
    IndexedAccess {
        object: Box<LitexToLeanObjectIr>,
        index: Box<LitexToLeanObjectIr>,
    },
    BuiltinApp {
        /// Parser-owned identity used to join a proof-carrying syntax node to
        /// its exact verifier-owned WD use. Non-proof-carrying or synthetic
        /// builtin nodes may leave this absent.
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        /// Structural identity used only to validate that the cited WD node
        /// still represents the same object; it is not used for selection.
        semantic_key: String,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: Vec<LitexToLeanObjectIr>,
    },
    Collection {
        /// Parser-owned identity used to select the exact constructor WD use.
        source_occurrence_id: Option<SourceObjectOccurrenceId>,
        /// Structural identity used only for post-selection validation.
        semantic_key: String,
        constructor: LitexToLeanCollectionObjectIr,
        items: Vec<LitexToLeanObjectIr>,
    },
}

#[derive(Clone)]
pub struct LitexToLeanSetBuilderIr {
    pub semantic_key: String,
    pub symbol_id: SymbolId,
    pub name: String,
    pub set: Box<LitexToLeanObjectIr>,
    pub facts: Vec<Fact>,
}

impl PartialEq for LitexToLeanSetBuilderIr {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key == other.semantic_key
    }
}

impl Eq for LitexToLeanSetBuilderIr {}

impl std::fmt::Debug for LitexToLeanSetBuilderIr {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("LitexToLeanSetBuilderIr")
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexToLeanAnonymousFunctionIr {
    pub source_occurrence_id: Option<SourceObjectOccurrenceId>,
    /// Structural identity used only after occurrence selection to detect a
    /// retargeted IR node; it is never a certificate-selection key.
    pub semantic_key: String,
    pub function: LitexToLeanFunctionTypeIr,
    pub body: Box<LitexToLeanObjectIr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanConstantObjectIr {
    ImaginaryUnit,
    EulerNumber,
    Pi,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LitexToLeanStandardSetIr {
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
pub enum LitexToLeanBuiltinObjectOperatorIr {
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
pub enum LitexToLeanCollectionObjectIr {
    ListSet,
}

impl LitexToLeanObjectIr {
    pub fn lower(obj: &Obj) -> Result<Self, String> {
        match obj {
            Obj::Atom(atom) => lower_atom(atom),
            Obj::Number(number) => Ok(LitexToLeanObjectIr::Number {
                normalized_value: number.normalized_value.clone(),
            }),
            Obj::ImaginaryUnit(_) => Ok(LitexToLeanObjectIr::Constant(
                LitexToLeanConstantObjectIr::ImaginaryUnit,
            )),
            Obj::EulerNumber(_) => Ok(LitexToLeanObjectIr::Constant(
                LitexToLeanConstantObjectIr::EulerNumber,
            )),
            Obj::Pi(_) => Ok(LitexToLeanObjectIr::Constant(
                LitexToLeanConstantObjectIr::Pi,
            )),
            Obj::StandardSet(set) => Ok(LitexToLeanObjectIr::StandardSet(set.into())),
            Obj::FnSet(function_set) => Ok(LitexToLeanObjectIr::FunctionSet {
                function: Box::new(LitexToLeanFunctionTypeIr::lower(function_set)?),
            }),
            Obj::SetBuilder(set_builder) => {
                let set = LitexToLeanObjectIr::lower(set_builder.param_set.as_ref())?;
                Ok(LitexToLeanObjectIr::SetBuilder(Box::new(
                    LitexToLeanSetBuilderIr {
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
            Obj::AnonymousFn(function) => Ok(LitexToLeanObjectIr::AnonymousFunction(Box::new(
                LitexToLeanAnonymousFunctionIr {
                    source_occurrence_id: function.source_occurrence_id,
                    semantic_key: obj_equality_key(obj),
                    function: LitexToLeanFunctionTypeIr::lower_anonymous(function)?,
                    body: Box::new(LitexToLeanObjectIr::lower(function.equal_to.as_ref())?),
                },
            ))),
            Obj::FnObj(application) => lower_function_application(application),
            Obj::ClosedRange(range) => Ok(LitexToLeanObjectIr::ClosedRange {
                start: Box::new(LitexToLeanObjectIr::lower(range.start.as_ref())?),
                end: Box::new(LitexToLeanObjectIr::lower(range.end.as_ref())?),
            }),
            Obj::TupleDim(dimension) => Ok(LitexToLeanObjectIr::TupleDimension(Box::new(
                LitexToLeanObjectIr::lower(dimension.arg.as_ref())?,
            ))),
            Obj::ObjAtIndex(access) => Ok(LitexToLeanObjectIr::IndexedAccess {
                object: Box::new(LitexToLeanObjectIr::lower(access.obj.as_ref())?),
                index: Box::new(LitexToLeanObjectIr::lower(access.index.as_ref())?),
            }),
            Obj::Add(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Add,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Sub(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Sub,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mul(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Mul,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Div(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Div,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mod(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Mod,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Gcd(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Gcd,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Lcm(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Lcm,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Floor(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Floor,
                value.arg.as_ref(),
            ),
            Obj::Ceil(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Ceil,
                value.arg.as_ref(),
            ),
            Obj::Min(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Min,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Max(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Max,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Exp(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Exp,
                value.arg.as_ref(),
            ),
            Obj::Ln(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Ln,
                value.arg.as_ref(),
            ),
            Obj::Sign(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Sign,
                value.arg.as_ref(),
            ),
            Obj::Factorial(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Factorial,
                value.arg.as_ref(),
            ),
            Obj::Pow(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Pow,
                value.base.as_ref(),
                value.exponent.as_ref(),
            ),
            Obj::Abs(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Abs,
                value.arg.as_ref(),
            ),
            Obj::Sin(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Sin,
                value.arg.as_ref(),
            ),
            Obj::Cos(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Cos,
                value.arg.as_ref(),
            ),
            Obj::Tan(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Tan,
                value.arg.as_ref(),
            ),
            Obj::Cot(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Cot,
                value.arg.as_ref(),
            ),
            Obj::RealPart(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::RealPart,
                value.arg.as_ref(),
            ),
            Obj::ImaginaryPart(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::ImaginaryPart,
                value.arg.as_ref(),
            ),
            Obj::ComplexAbs(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::ComplexAbs,
                value.arg.as_ref(),
            ),
            Obj::Sqrt(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Sqrt,
                value.arg.as_ref(),
            ),
            Obj::Log(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Log,
                value.base.as_ref(),
                value.arg.as_ref(),
            ),
            Obj::Union(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Union,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Intersect(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::Intersect,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::SetMinus(value) => binary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::SetMinus,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::BigUnion(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::BigUnion,
                value.left.as_ref(),
            ),
            Obj::BigIntersect(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::BigIntersect,
                value.left.as_ref(),
            ),
            Obj::PowerSet(value) => unary(
                obj,
                LitexToLeanBuiltinObjectOperatorIr::PowerSet,
                value.set.as_ref(),
            ),
            Obj::ListSet(value) => Ok(LitexToLeanObjectIr::Collection {
                source_occurrence_id: value.source_occurrence_id,
                semantic_key: obj_equality_key(obj),
                constructor: LitexToLeanCollectionObjectIr::ListSet,
                items: value
                    .list
                    .iter()
                    .map(|item| LitexToLeanObjectIr::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Err(format!(
                "Litex-to-Lean Obj IR does not support {:?} object `{}`",
                other.kind(),
                other
            )),
        }
    }
}

fn lower_function_application(application: &FnObj) -> Result<LitexToLeanObjectIr, String> {
    let source_occurrence_id = application.source_occurrence_id.ok_or_else(|| {
        format!(
            "Litex-to-Lean requires parser-owned occurrence identity for application `{}`",
            application
        )
    })?;
    let head_obj: Obj = (*application.head).clone().into();
    let head = LitexToLeanObjectIr::lower(&head_obj)?;
    let argument_layers = application
        .body
        .iter()
        .map(|layer| {
            layer
                .iter()
                .map(|argument| LitexToLeanObjectIr::lower(argument.as_ref()))
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
    Ok(LitexToLeanObjectIr::FunctionApplication(
        LitexToLeanFunctionApplicationIr {
            head: Box::new(head),
            source_occurrence_id,
            source_application: application.clone().into(),
            argument_layers,
            source_argument_layers,
        },
    ))
}

fn lower_atom(atom: &AtomObj) -> Result<LitexToLeanObjectIr, String> {
    let Some(symbol) = atom.symbol_ref() else {
        return Err(format!(
            "Litex-to-Lean Obj IR requires a resolved SymbolId for atom `{}`",
            atom
        ));
    };
    Ok(LitexToLeanObjectIr::Symbol {
        symbol_id: symbol.id(),
        name: symbol.display_name().to_string(),
    })
}

fn unary(
    source: &Obj,
    operator: LitexToLeanBuiltinObjectOperatorIr,
    argument: &Obj,
) -> Result<LitexToLeanObjectIr, String> {
    Ok(LitexToLeanObjectIr::BuiltinApp {
        source_occurrence_id: source.source_occurrence_id(),
        semantic_key: obj_equality_key(source),
        operator,
        arguments: vec![LitexToLeanObjectIr::lower(argument)?],
    })
}

fn binary(
    source: &Obj,
    operator: LitexToLeanBuiltinObjectOperatorIr,
    left: &Obj,
    right: &Obj,
) -> Result<LitexToLeanObjectIr, String> {
    Ok(LitexToLeanObjectIr::BuiltinApp {
        source_occurrence_id: source.source_occurrence_id(),
        semantic_key: obj_equality_key(source),
        operator,
        arguments: vec![
            LitexToLeanObjectIr::lower(left)?,
            LitexToLeanObjectIr::lower(right)?,
        ],
    })
}

impl From<&StandardSet> for LitexToLeanStandardSetIr {
    fn from(value: &StandardSet) -> Self {
        match value {
            StandardSet::NPos => LitexToLeanStandardSetIr::PositiveNatural,
            StandardSet::N => LitexToLeanStandardSetIr::Natural,
            StandardSet::Q => LitexToLeanStandardSetIr::Rational,
            StandardSet::Z => LitexToLeanStandardSetIr::Integer,
            StandardSet::R => LitexToLeanStandardSetIr::Real,
            StandardSet::C => LitexToLeanStandardSetIr::Complex,
            StandardSet::QPos => LitexToLeanStandardSetIr::PositiveRational,
            StandardSet::RPos => LitexToLeanStandardSetIr::PositiveReal,
            StandardSet::QNeg => LitexToLeanStandardSetIr::NegativeRational,
            StandardSet::ZNeg => LitexToLeanStandardSetIr::NegativeInteger,
            StandardSet::RNeg => LitexToLeanStandardSetIr::NegativeReal,
            StandardSet::QStar => LitexToLeanStandardSetIr::NonzeroRational,
            StandardSet::ZStar => LitexToLeanStandardSetIr::NonzeroInteger,
            StandardSet::RStar => LitexToLeanStandardSetIr::NonzeroReal,
            StandardSet::CStar => LitexToLeanStandardSetIr::NonzeroComplex,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_set_constructors_preserve_identity_and_order() {
        let left_binding =
            SymbolBinding::new(SymbolId::new(11), "left".to_string(), "left".to_string());
        let right_binding =
            SymbolBinding::new(SymbolId::new(12), "right".to_string(), "right".to_string());
        let left: Obj = Identifier::new_bound("left".to_string(), left_binding.as_ref()).into();
        let right: Obj = Identifier::new_bound("right".to_string(), right_binding.as_ref()).into();

        let union: Obj = Union::new(left.clone(), right.clone()).into();
        assert_eq!(
            LitexToLeanObjectIr::lower(&union).unwrap(),
            LitexToLeanObjectIr::BuiltinApp {
                source_occurrence_id: None,
                semantic_key: obj_equality_key(&union),
                operator: LitexToLeanBuiltinObjectOperatorIr::Union,
                arguments: vec![
                    LitexToLeanObjectIr::Symbol {
                        symbol_id: left_binding.id(),
                        name: "left".to_string(),
                    },
                    LitexToLeanObjectIr::Symbol {
                        symbol_id: right_binding.id(),
                        name: "right".to_string(),
                    },
                ],
            }
        );

        let list: Obj = ListSet::new(vec![right, left]).into();
        assert_eq!(
            LitexToLeanObjectIr::lower(&list).unwrap(),
            LitexToLeanObjectIr::Collection {
                source_occurrence_id: None,
                semantic_key: obj_equality_key(&list),
                constructor: LitexToLeanCollectionObjectIr::ListSet,
                items: vec![
                    LitexToLeanObjectIr::Symbol {
                        symbol_id: right_binding.id(),
                        name: "right".to_string(),
                    },
                    LitexToLeanObjectIr::Symbol {
                        symbol_id: left_binding.id(),
                        name: "left".to_string(),
                    },
                ],
            }
        );
    }

    #[test]
    fn unresolved_symbol_is_rejected() {
        let left: Obj = Identifier::new("left".to_string()).into();
        let right: Obj = Identifier::new("right".to_string()).into();
        let unresolved: Obj = Union::new(left, right).into();

        let error = LitexToLeanObjectIr::lower(&unresolved).unwrap_err();
        assert!(error.contains("resolved SymbolId"));
    }

    #[test]
    fn set_builder_is_an_explicit_binder_boundary() {
        let binding = SymbolBinding::new(SymbolId::new(7), "x".to_string(), "x".to_string());
        let parameter: Obj = SetBuilderFreeParamObj::new(binding.as_ref()).into();
        let builder: Obj = SetBuilder::new(
            binding.clone(),
            StandardSet::R.into(),
            vec![EqualFact::new(parameter.clone(), parameter, default_line_file()).into()],
        )
        .expect("test set-builder should be well formed")
        .into();

        let lowered = LitexToLeanObjectIr::lower(&builder)
            .expect("a set-builder has no target carrier to resolve");
        let LitexToLeanObjectIr::SetBuilder(lowered) = lowered else {
            panic!("expected an explicit set-builder IR node")
        };
        assert_eq!(lowered.symbol_id, binding.id());
        assert_eq!(lowered.name, "x");
        assert_eq!(
            lowered.set.as_ref(),
            &LitexToLeanObjectIr::StandardSet(LitexToLeanStandardSetIr::Real)
        );
        assert_eq!(lowered.facts.len(), 1);
        assert_eq!(lowered.facts[0].to_string(), "#7#x = #7#x");
    }
}
