use crate::prelude::*;

/// A structural compiler representation of one Litex object.
///
/// The tree preserves source object syntax and symbol identity. Its native Lean
/// carrier is supplied separately by `LeanCarrierToLeanIR` constraints, so the
/// same numeral or arithmetic tree can elaborate in `ℕ`, `ℤ`, `ℚ`, `ℝ`, or
/// `ℂ` without attaching a guessed type to the object itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObjToLeanIR {
    Symbol {
        symbol_id: SymbolId,
        name: String,
    },
    Number {
        normalized_value: String,
    },
    Constant(ConstantObjToLeanIR),
    StandardSet(StandardSetToLeanIR),
    BuiltinApp {
        operator: BuiltinObjOperatorToLeanIR,
        arguments: Vec<ObjToLeanIR>,
    },
    Collection {
        constructor: CollectionObjToLeanIR,
        items: Vec<ObjToLeanIR>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstantObjToLeanIR {
    ImaginaryUnit,
    EulerNumber,
    Pi,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StandardSetToLeanIR {
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
pub enum BuiltinObjOperatorToLeanIR {
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
pub enum CollectionObjToLeanIR {
    ListSet,
}

impl ObjToLeanIR {
    pub fn lower(obj: &Obj) -> Result<Self, String> {
        match obj {
            Obj::Atom(atom) => lower_atom(atom),
            Obj::Number(number) => Ok(ObjToLeanIR::Number {
                normalized_value: number.normalized_value.clone(),
            }),
            Obj::ImaginaryUnit(_) => Ok(ObjToLeanIR::Constant(ConstantObjToLeanIR::ImaginaryUnit)),
            Obj::EulerNumber(_) => Ok(ObjToLeanIR::Constant(ConstantObjToLeanIR::EulerNumber)),
            Obj::Pi(_) => Ok(ObjToLeanIR::Constant(ConstantObjToLeanIR::Pi)),
            Obj::StandardSet(set) => Ok(ObjToLeanIR::StandardSet(set.into())),
            Obj::Add(value) => binary(
                BuiltinObjOperatorToLeanIR::Add,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Sub(value) => binary(
                BuiltinObjOperatorToLeanIR::Sub,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mul(value) => binary(
                BuiltinObjOperatorToLeanIR::Mul,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Div(value) => binary(
                BuiltinObjOperatorToLeanIR::Div,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Mod(value) => binary(
                BuiltinObjOperatorToLeanIR::Mod,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Gcd(value) => binary(
                BuiltinObjOperatorToLeanIR::Gcd,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Lcm(value) => binary(
                BuiltinObjOperatorToLeanIR::Lcm,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Floor(value) => unary(BuiltinObjOperatorToLeanIR::Floor, value.arg.as_ref()),
            Obj::Ceil(value) => unary(BuiltinObjOperatorToLeanIR::Ceil, value.arg.as_ref()),
            Obj::Min(value) => binary(
                BuiltinObjOperatorToLeanIR::Min,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Max(value) => binary(
                BuiltinObjOperatorToLeanIR::Max,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Exp(value) => unary(BuiltinObjOperatorToLeanIR::Exp, value.arg.as_ref()),
            Obj::Ln(value) => unary(BuiltinObjOperatorToLeanIR::Ln, value.arg.as_ref()),
            Obj::Sign(value) => unary(BuiltinObjOperatorToLeanIR::Sign, value.arg.as_ref()),
            Obj::Factorial(value) => {
                unary(BuiltinObjOperatorToLeanIR::Factorial, value.arg.as_ref())
            }
            Obj::Pow(value) => binary(
                BuiltinObjOperatorToLeanIR::Pow,
                value.base.as_ref(),
                value.exponent.as_ref(),
            ),
            Obj::Abs(value) => unary(BuiltinObjOperatorToLeanIR::Abs, value.arg.as_ref()),
            Obj::Sin(value) => unary(BuiltinObjOperatorToLeanIR::Sin, value.arg.as_ref()),
            Obj::Cos(value) => unary(BuiltinObjOperatorToLeanIR::Cos, value.arg.as_ref()),
            Obj::Tan(value) => unary(BuiltinObjOperatorToLeanIR::Tan, value.arg.as_ref()),
            Obj::Cot(value) => unary(BuiltinObjOperatorToLeanIR::Cot, value.arg.as_ref()),
            Obj::RealPart(value) => unary(BuiltinObjOperatorToLeanIR::RealPart, value.arg.as_ref()),
            Obj::ImaginaryPart(value) => unary(
                BuiltinObjOperatorToLeanIR::ImaginaryPart,
                value.arg.as_ref(),
            ),
            Obj::ComplexAbs(value) => {
                unary(BuiltinObjOperatorToLeanIR::ComplexAbs, value.arg.as_ref())
            }
            Obj::Sqrt(value) => unary(BuiltinObjOperatorToLeanIR::Sqrt, value.arg.as_ref()),
            Obj::Log(value) => binary(
                BuiltinObjOperatorToLeanIR::Log,
                value.base.as_ref(),
                value.arg.as_ref(),
            ),
            Obj::Union(value) => binary(
                BuiltinObjOperatorToLeanIR::Union,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::Intersect(value) => binary(
                BuiltinObjOperatorToLeanIR::Intersect,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::SetMinus(value) => binary(
                BuiltinObjOperatorToLeanIR::SetMinus,
                value.left.as_ref(),
                value.right.as_ref(),
            ),
            Obj::BigUnion(value) => {
                unary(BuiltinObjOperatorToLeanIR::BigUnion, value.left.as_ref())
            }
            Obj::BigIntersect(value) => unary(
                BuiltinObjOperatorToLeanIR::BigIntersect,
                value.left.as_ref(),
            ),
            Obj::PowerSet(value) => unary(BuiltinObjOperatorToLeanIR::PowerSet, value.set.as_ref()),
            Obj::ListSet(value) => Ok(ObjToLeanIR::Collection {
                constructor: CollectionObjToLeanIR::ListSet,
                items: value
                    .list
                    .iter()
                    .map(|item| ObjToLeanIR::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            other => Err(format!(
                "To-Lean Obj IR does not support {:?} object `{}`",
                other.kind(),
                other
            )),
        }
    }
}

fn lower_atom(atom: &AtomObj) -> Result<ObjToLeanIR, String> {
    let Some(symbol) = atom.symbol_ref() else {
        return Err(format!(
            "To-Lean Obj IR requires a resolved SymbolId for atom `{}`",
            atom
        ));
    };
    Ok(ObjToLeanIR::Symbol {
        symbol_id: symbol.id(),
        name: symbol.display_name().to_string(),
    })
}

fn unary(operator: BuiltinObjOperatorToLeanIR, argument: &Obj) -> Result<ObjToLeanIR, String> {
    Ok(ObjToLeanIR::BuiltinApp {
        operator,
        arguments: vec![ObjToLeanIR::lower(argument)?],
    })
}

fn binary(
    operator: BuiltinObjOperatorToLeanIR,
    left: &Obj,
    right: &Obj,
) -> Result<ObjToLeanIR, String> {
    Ok(ObjToLeanIR::BuiltinApp {
        operator,
        arguments: vec![ObjToLeanIR::lower(left)?, ObjToLeanIR::lower(right)?],
    })
}

impl From<&StandardSet> for StandardSetToLeanIR {
    fn from(value: &StandardSet) -> Self {
        match value {
            StandardSet::NPos => StandardSetToLeanIR::PositiveNatural,
            StandardSet::N => StandardSetToLeanIR::Natural,
            StandardSet::Q => StandardSetToLeanIR::Rational,
            StandardSet::Z => StandardSetToLeanIR::Integer,
            StandardSet::R => StandardSetToLeanIR::Real,
            StandardSet::C => StandardSetToLeanIR::Complex,
            StandardSet::QPos => StandardSetToLeanIR::PositiveRational,
            StandardSet::RPos => StandardSetToLeanIR::PositiveReal,
            StandardSet::QNeg => StandardSetToLeanIR::NegativeRational,
            StandardSet::ZNeg => StandardSetToLeanIR::NegativeInteger,
            StandardSet::RNeg => StandardSetToLeanIR::NegativeReal,
            StandardSet::QStar => StandardSetToLeanIR::NonzeroRational,
            StandardSet::ZStar => StandardSetToLeanIR::NonzeroInteger,
            StandardSet::RStar => StandardSetToLeanIR::NonzeroReal,
            StandardSet::CStar => StandardSetToLeanIR::NonzeroComplex,
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
            ObjToLeanIR::lower(&union).unwrap(),
            ObjToLeanIR::BuiltinApp {
                operator: BuiltinObjOperatorToLeanIR::Union,
                arguments: vec![
                    ObjToLeanIR::Symbol {
                        symbol_id: left_binding.id(),
                        name: "left".to_string(),
                    },
                    ObjToLeanIR::Symbol {
                        symbol_id: right_binding.id(),
                        name: "right".to_string(),
                    },
                ],
            }
        );

        let list: Obj = ListSet::new(vec![right, left]).into();
        assert_eq!(
            ObjToLeanIR::lower(&list).unwrap(),
            ObjToLeanIR::Collection {
                constructor: CollectionObjToLeanIR::ListSet,
                items: vec![
                    ObjToLeanIR::Symbol {
                        symbol_id: right_binding.id(),
                        name: "right".to_string(),
                    },
                    ObjToLeanIR::Symbol {
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

        let error = ObjToLeanIR::lower(&unresolved).unwrap_err();
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

        let error = ObjToLeanIR::lower(&builder).unwrap_err();
        assert!(error.contains("SetBuilder"));
    }
}
