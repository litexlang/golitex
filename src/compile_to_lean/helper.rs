use super::LeanCompileError;
use crate::ast::stmt::{ReleaseAndExpandStmt, WitnessStmt};
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::VerifyNotExistFactResult;
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn finite_vector_proof(proofs: &[String]) -> String {
    let tail = "(fun i => Fin.elim0 i)".to_string();
    if proofs.is_empty() {
        return tail;
    }
    let mut bindings = proofs
        .iter()
        .enumerate()
        .map(|(index, proof)| {
            format!(
                "have _finiteProof_{index} := ({})",
                proof.replace('\n', "\n  ")
            )
        })
        .collect::<Vec<_>>();
    let cases = proofs
        .iter()
        .enumerate()
        .rev()
        .fold(tail, |tail, (index, _)| {
            format!("(Fin.cases _finiteProof_{index} {tail})")
        });
    bindings.push(format!("exact {cases}"));
    format!("(by\n  {}\n)", bindings.join("\n  "))
}

#[derive(Clone, Copy)]
pub(super) enum BinaryArithmetic {
    Add,
    Sub,
    Mul,
    Div,
}

impl BinaryArithmetic {
    pub(super) fn names(self) -> (&'static str, &'static str, &'static str) {
        match self {
            Self::Add => ("add", "+", "Add"),
            Self::Sub => ("sub", "-", "Sub"),
            Self::Mul => ("mul", "*", "Mul"),
            Self::Div => ("div", "/", "Div"),
        }
    }
}

pub(super) fn ensure_nonzero_subject(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(x)) if x.left.ir() == object.ir() && is_zero(&x.right) => Ok(()),
        _ => Err(LeanCompileError::new("Arithmetic/NonzeroSubject", "The requirement must be this exact object's inequality with zero, in source orientation.")),
    }
}

pub(super) fn membership_subject(
    fact: &Fact,
    object: &Obj,
) -> Result<StandardSet, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(x)) if x.element.ir() == object.ir() => match &x.set {
            Obj::StandardSet(set) => Ok(set.clone()),
            _ => Err(LeanCompileError::unsupported(
                "Arithmetic/NonstandardDomain",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Arithmetic/MembershipSubject",
            "Membership evidence describes another operand.",
        )),
    }
}

pub(super) fn closed_integer(object: &Obj) -> Option<i128> {
    EvalRational::from_obj(object)?.to_i128_if_integer()
}

pub(super) fn validate_arithmetic_expression(object: &Obj) -> Result<(), LeanCompileError> {
    match object {
        Obj::Identifier(IdentifierObj::Plain { .. }) => Ok(()),
        Obj::Literal(Literal::Number(n)) => number_literal(n, "ℂ").map(|_| ()),
        Obj::FnObj(call)
            if call.body.len() == 1 && (1..=2).contains(&call.body[0].len()) =>
        {
            // This original call is an opaque scalar leaf. Its constructor
            // WD and numeric return evidence are consumed by the observer;
            // argument domains are not polynomial normalization obligations.
            Ok(())
        }
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)) => {
            // Rational normalization treats the original square root as one
            // scalar leaf. Its observer consumes the argument WD, real
            // membership and nonnegativity; it does not normalize the radicand.
            Ok(())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => {
            validate_arithmetic_expression(&x.arg)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
            validate_arithmetic_expression(&x.base)?;
            validate_arithmetic_expression(&x.exponent)?;
            closed_integer(&x.exponent)
                .ok_or_else(|| LeanCompileError::unsupported("Rational/NonClosedIntegerPower"))?;
            Ok(())
        }
        _ => Err(LeanCompileError::new(
            "Rational/ExpressionDomain",
            &format!(
                "The selected rational normalization does not support the original source expression `{}`.",
                object.ir()
            ),
        )),
    }
}

pub(super) fn normalization_nonzero_subjects(
    left: &Obj,
    right: &Obj,
) -> Result<Vec<Obj>, LeanCompileError> {
    fn collect(object: &Obj, subjects: &mut Vec<Obj>) -> Result<(), LeanCompileError> {
        match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
                if !subjects.iter().any(|o| o.ir() == x.right.ir()) {
                    subjects.push(x.right.as_ref().clone());
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => collect(&x.arg, subjects)?,
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
                collect(&x.base, subjects)?;
                collect(&x.exponent, subjects)?;
                let value = evaluate_obj_to_normalized_decimal_number(&x.exponent)
                    .and_then(|n| n.normalized_value.parse::<i128>().ok());
                if closed_integer(&x.exponent).is_some_and(|z| z < 0) && value.is_none() {
                    return Err(LeanCompileError::unsupported(
                        "Rational/NegativePowerGuardProfile",
                    ));
                }
                if value.is_some_and(|z| z < 0) && !subjects.iter().any(|o| o.ir() == x.base.ir()) {
                    subjects.push(x.base.as_ref().clone());
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn factors(object: &Obj, result: &mut Vec<Obj>) {
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) = object {
            factors(&x.left, result);
            factors(&x.right, result);
        } else if !result.iter().any(|o| o.ir() == object.ir()) {
            result.push(object.clone());
        }
    }
    let mut subjects = Vec::new();
    collect(left, &mut subjects)?;
    collect(right, &mut subjects)?;
    let mut result = Vec::new();
    for subject in subjects {
        factors(&subject, &mut result);
    }
    Ok(result)
}

pub(super) fn exact_rational_literal(
    value: &EvalRational,
    ty: &str,
) -> Result<String, LeanCompileError> {
    match value.to_obj() {
        Obj::Literal(Literal::Number(n)) => number_literal(&n, ty),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => match (*x.left, *x.right) {
            (Obj::Literal(Literal::Number(a)), Obj::Literal(Literal::Number(b))) => Ok(format!(
                "({} / {})",
                number_literal(&a, ty)?,
                number_literal(&b, ty)?
            )),
            _ => Err(LeanCompileError::new(
                "Number/ExactRational",
                "The exact scalar has an unexpected canonical shape.",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Number/ExactRational",
            "The exact scalar has an unexpected canonical shape.",
        )),
    }
}

pub(super) fn scalar_decimal(value: &str) -> Result<EvalRational, LeanCompileError> {
    let number = Number::new(value.to_string());
    number_literal(&number, "ℂ")?;
    EvalRational::from_obj(&Obj::Literal(Literal::Number(number)))
        .ok_or_else(|| LeanCompileError::unsupported("Number/ExactEvaluationBound"))
}

pub(super) fn number_literal(number: &Number, ty: &str) -> Result<String, LeanCompileError> {
    let value = &number.normalized_value;
    let unsigned = value.strip_prefix('-').unwrap_or(value);
    let mut parts = unsigned.split('.');
    let whole = parts.next().unwrap_or("");
    let fractional = parts.next();
    if whole.is_empty()
        || !whole.bytes().all(|b| b.is_ascii_digit())
        || fractional.is_some_and(|s| s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()))
        || parts.next().is_some()
    {
        return Err(LeanCompileError::unsupported("Number/FiniteDecimalLiteral"));
    }
    Ok(format!("({value} : {ty})"))
}

pub(super) fn ensure_object(
    object: &Obj,
    proof: &ObjWellDefinedProof,
) -> Result<(), LeanCompileError> {
    if object.ir() != proof.obj().ir() {
        return Err(LeanCompileError::new(
            "WD/Subject",
            "Object WD describes a different subject.",
        ));
    }
    Ok(())
}

pub(super) fn ensure_complex_member(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact))
            if fact.element.ir() == object.ir() && fact.set == Obj::StandardSet(StandardSet::C) =>
        {
            Ok(())
        }
        _ => Err(LeanCompileError::new(
            "WD/ArithmeticDomain",
            "An operand requirement is not membership of this operand in C.",
        )),
    }
}

pub(super) fn same_atomic_family(left: &AtomicFact, right: &AtomicFact) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
        && left.prop_name() == right.prop_name()
        && atomic_fact_has_positive_polarity(left) == atomic_fact_has_positive_polarity(right)
        && atomic_fact_args_ref(left).len() == atomic_fact_args_ref(right).len()
}

pub(super) fn is_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(number)) if number.normalized_value == "0")
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum SourceOrderKind {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
}

pub(super) fn source_order_parts(
    fact: &AtomicFact,
) -> Result<(SourceOrderKind, &Obj, &Obj), LeanCompileError> {
    match fact {
        AtomicFact::LessFact(f) => Ok((SourceOrderKind::Less, &f.left, &f.right)),
        AtomicFact::GreaterFact(f) => Ok((SourceOrderKind::Greater, &f.left, &f.right)),
        AtomicFact::LessEqualFact(f) => Ok((SourceOrderKind::LessEqual, &f.left, &f.right)),
        AtomicFact::GreaterEqualFact(f) => Ok((SourceOrderKind::GreaterEqual, &f.left, &f.right)),
        _ => Err(LeanCompileError::unsupported("Order/PredicateFamily")),
    }
}

pub(super) fn source_order_oriented(
    fact: &AtomicFact,
) -> Result<(&Obj, &Obj, bool), LeanCompileError> {
    let (kind, left, right) = source_order_parts(fact)?;
    match kind {
        SourceOrderKind::Less => Ok((left, right, true)),
        SourceOrderKind::Greater => Ok((right, left, true)),
        SourceOrderKind::LessEqual => Ok((left, right, false)),
        SourceOrderKind::GreaterEqual => Ok((right, left, false)),
    }
}

pub(super) fn arithmetic_constructor_pairs<'a>(
    left: &'a Obj,
    right: &'a Obj,
) -> Option<(&'static str, Vec<(&'a Obj, &'a Obj)>)> {
    use ArithmeticOperator::*;
    match (left, right) {
        (Obj::ArithmeticOperator(Add(a)), Obj::ArithmeticOperator(Add(b))) => {
            Some(("addValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Sub(a)), Obj::ArithmeticOperator(Sub(b))) => {
            Some(("subValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Mul(a)), Obj::ArithmeticOperator(Mul(b))) => {
            Some(("mulValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Div(a)), Obj::ArithmeticOperator(Div(b))) => {
            Some(("divValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Pow(a)), Obj::ArithmeticOperator(Pow(b))) => Some((
            "powValue",
            vec![(&a.base, &b.base), (&a.exponent, &b.exponent)],
        )),
        (Obj::ArithmeticOperator(Neg(a)), Obj::ArithmeticOperator(Neg(b))) => {
            Some(("negValue", vec![(&a.arg, &b.arg)]))
        }
        (Obj::ArithmeticOperator(Abs(a)), Obj::ArithmeticOperator(Abs(b))) => {
            Some(("absValue", vec![(&a.arg, &b.arg)]))
        }
        (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(b)),
        ) => Some(("sqrtValue", vec![(&a.arg, &b.arg)])),
        _ => None,
    }
}

pub(super) fn arithmetic_operation_term(operation: &str) -> String {
    if matches!(operation, "absValue" | "sqrtValue") {
        format!("(Litex.{operation} (M := M))")
    } else {
        format!("M.{operation}")
    }
}

pub(super) fn is_exact_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(number)) if number.normalized_value == "0")
}

pub(super) fn standard_value_constructor(
    set: &StandardSet,
) -> Result<&'static str, LeanCompileError> {
    Ok(match set {
        StandardSet::N => "natural",
        StandardSet::Z => "integer",
        StandardSet::Q => "rational",
        StandardSet::R => "real",
        StandardSet::C => "complex",
        _ => return Err(LeanCompileError::unsupported("Standard/NumericCarrier")),
    })
}

pub(super) fn standard_term(set: &StandardSet) -> Result<String, LeanCompileError> {
    let name = match set {
        StandardSet::N => "N",
        StandardSet::Z => "Z",
        StandardSet::Q => "Q",
        StandardSet::R => "R",
        StandardSet::C => "C",
        StandardSet::RPos => "RPos",
        StandardSet::NPos
        | StandardSet::QPos
        | StandardSet::QNeg
        | StandardSet::ZNeg
        | StandardSet::RNeg
        | StandardSet::QStar
        | StandardSet::ZStar
        | StandardSet::RStar
        | StandardSet::CStar => {
            return Err(LeanCompileError::unsupported("StandardSet/SignedOrNonzero"))
        }
    };
    Ok(format!("(Litex.{name} (M := M))"))
}

pub(super) fn unsupported_wd_definition(proof: &ObjWellDefinedProofByDef) -> LeanCompileError {
    match proof {
        ObjWellDefinedProofByDef::LimitOperator(_) => {
            LeanCompileError::unsupported("WD/LimitOperator")
        }
        ObjWellDefinedProofByDef::Identifier(_) => {
            LeanCompileError::unsupported("WD/IdentifierShape")
        }
        ObjWellDefinedProofByDef::Literal(_) => LeanCompileError::unsupported("WD/Literal"),
        ObjWellDefinedProofByDef::StandardSet(_) => LeanCompileError::new(
            "WD/StandardSet",
            "Definition evidence has another object family.",
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(_) => {
            LeanCompileError::unsupported("WD/ArithmeticOperator")
        }
        ObjWellDefinedProofByDef::FnObj(_) => LeanCompileError::unsupported("WD/FnObj"),
        ObjWellDefinedProofByDef::IntegerOperator(_) => {
            LeanCompileError::unsupported("WD/IntegerOperator")
        }
        ObjWellDefinedProofByDef::HyperbolicOperator(_) => {
            LeanCompileError::unsupported("WD/HyperbolicOperator")
        }
        ObjWellDefinedProofByDef::TrigOperator(_) => {
            LeanCompileError::unsupported("WD/TrigOperator")
        }
        ObjWellDefinedProofByDef::ExpLogOperator(_) => {
            LeanCompileError::unsupported("WD/ExpLogOperator")
        }
        ObjWellDefinedProofByDef::ComplexOperator(_) => {
            LeanCompileError::unsupported("WD/ComplexOperator")
        }
        ObjWellDefinedProofByDef::SetOperator(_) => LeanCompileError::unsupported("WD/SetOperator"),
        ObjWellDefinedProofByDef::SetFormer(_) => LeanCompileError::unsupported("WD/SetFormer"),
        ObjWellDefinedProofByDef::ProductShape(_) => {
            LeanCompileError::unsupported("WD/ProductShape")
        }
        ObjWellDefinedProofByDef::FunctionSpace(
            FunctionSpaceObjWellDefinedProofByDef::Composition(_),
        ) => LeanCompileError::unsupported("WD/FunctionSpace/Composition"),
        ObjWellDefinedProofByDef::FunctionSpace(_) => {
            LeanCompileError::unsupported("WD/FunctionSpace")
        }
        ObjWellDefinedProofByDef::IteratedOperator(_) => {
            LeanCompileError::unsupported("WD/IteratedOperator")
        }
        ObjWellDefinedProofByDef::FiniteSetStat(_) => {
            LeanCompileError::unsupported("WD/FiniteSetStat")
        }
        ObjWellDefinedProofByDef::Structish(_) => LeanCompileError::unsupported("WD/Structish"),
        ObjWellDefinedProofByDef::InstantiatedTemplateObj(_) => {
            LeanCompileError::unsupported("WD/InstantiatedTemplateObj")
        }
    }
}

pub(super) fn unsupported_atomic_builtin(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> LeanCompileError {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(_) => {
            LeanCompileError::unsupported("Atomic/DvdBuiltin")
        }

        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(_) => LeanCompileError::new(
            "Builtin/IsSet",
            "Sethood certificate does not match its subject.",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact(_) => {
            LeanCompileError::unsupported("Atomic/BuiltinRule")
        }
    }
}

pub(super) fn success_object_wd<'a>(
    result: &'a VerifyObjWellDefinedResult,
    expected: &Obj,
) -> Result<&'a ObjWellDefinedProof, LeanCompileError> {
    match result {
        VerifyObjWellDefinedResult::Success(wd) => {
            ensure_object(expected, wd)?;
            Ok(wd)
        }
        VerifyObjWellDefinedResult::Failed { .. } => Err(LeanCompileError::new(
            "Declaration/WD",
            "A successful declaration has failed value WD.",
        )),
    }
}

pub(super) fn alias_equality_subject<'a>(
    fact: &'a Fact,
    parameter: &BoundName,
    value: &Obj,
) -> Result<&'a Obj, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(equal)) if equal.right.ir() == value.ir() => {
            match &equal.left {
                Obj::Identifier(IdentifierObj::Plain { id, name })
                    if *id == parameter.id && name == &parameter.name =>
                {
                    Ok(&equal.left)
                }
                _ => Err(LeanCompileError::new(
                    "Declaration/StoreSubject",
                    "The stored equality names another declaration.",
                )),
            }
        }
        _ => Err(LeanCompileError::new(
            "Declaration/StoreSubject",
            "The stored equality has another value or orientation.",
        )),
    }
}

pub(super) fn source_subject(result: &VerifyFactResult) -> Result<Fact, LeanCompileError> {
    verified_subject(result).ok_or_else(|| LeanCompileError::unsupported("Verify/SourceSubject"))
}

pub(super) fn verified_subject(result: &VerifyFactResult) -> Option<Fact> {
    match result {
        VerifyFactResult::Equality(result) => match result.as_ref() {
            VerifyEqualityResult::Success(proof) => {
                Some(Fact::AtomicFact(AtomicFact::EqualFact(proof.fact.clone())))
            }
            _ => None,
        },
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => {
                Some(Fact::AtomicFact(proof.fact.clone()))
            }
            _ => None,
        },
        VerifyFactResult::ForallFact(result) => match result.as_ref() {
            VerifyForallFactResult::Success(proof) => Some(Fact::ForallFact(proof.fact().clone())),
            _ => None,
        },
        VerifyFactResult::AndFact(result) => match result.as_ref() {
            crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult::Success(proof) => {
                Some(Fact::AndFact(proof.fact.clone()))
            }
            _ => None,
        },
        VerifyFactResult::ChainFact(result) => match result.as_ref() {
            crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult::Success(proof) => {
                Some(Fact::ChainFact(proof.fact.clone()))
            }
            _ => None,
        },
        VerifyFactResult::OrFact(result) => match result.as_ref() {
            crate::execute::execute_fact_stmt::verify_or_fact::VerifyOrFactResult::Success(proof) => Some(Fact::OrFact(proof.fact.clone())),
            _ => None,
        },
        VerifyFactResult::ExistShapedFact(result) => match result.as_ref() {
            VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(proof)) => Some(crate::ast::fact::exist_shaped_fact_to_fact(&proof.fact)),
            VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(proof)) => Some(crate::ast::fact::exist_shaped_fact_to_fact(&proof.fact)),
            VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(proof)) => Some(crate::ast::fact::exist_shaped_fact_to_fact(&proof.fact)),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn validate_statement_capture(
    source: &Stmt,
    result: &ExecStmtResult,
) -> Result<(), LeanCompileError> {
    let matches = match (source, result) {
        (
            Stmt::Witness(WitnessStmt::WitnessExistFact(source)),
            ExecStmtResult::Witness(
                crate::execute::execute_witness_stmt::ExecWitnessStmtResult::WitnessExistFact(
                    crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtResult::Success(
                        proof,
                    ),
                ),
            ),
        ) => source == &proof.statement,
        (Stmt::Fact(fact), ExecStmtResult::Fact(ExecFactStmtResult::Success(proof))) => {
            verified_subject(&proof.verify_result).as_ref() == Some(fact)
        }
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromAtomicFact(
                stmt,
            ))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                    crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(proof),
                ),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromExistFact(
                stmt,
            ))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::ObtainObjFromExistFact(
                    crate::execute::ExecObtainObjFromExistFactStmtResult::Success(proof),
                ),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::LetObjStmt(stmt))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjInNonemptySetStmt(
                stmt,
            ))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjInNonemptySet(
                    ExecHaveObjInNonemptySetStmtResult::Success(proof),
                ),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjEqualStmt(stmt))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::By(ByStmt::ByDefStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))),
        ) => verified_subject(&proof.proof).as_ref() == Some(&Fact::AtomicFact(stmt.fact.clone())),
        (
            Stmt::By(ByStmt::ByThmStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))),
        ) => {
            stmt.call == proof.call
                && verified_subject(&proof.selected_proof).as_ref()
                    == Some(&Fact::AtomicFact(stmt.selected_fact.clone()))
        }
        (
            Stmt::By(ByStmt::ByContraStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Contra(
                crate::execute::execute_by_stmt::ExecByContraStmtResult::Success(proof),
            )),
        ) => {
            stmt.to_prove == proof.goal
                && stmt.impossible_fact == proof.closing.impossible_fact
                && verified_subject(&proof.closing.impossible).as_ref()
                    == Some(&stmt.impossible_fact)
                && stored_capture_matches(&proof.stored.store, &stmt.to_prove)
                && validate_captured_steps(&stmt.proof, &proof.proof_steps)?
        }
        (
            Stmt::By(ByStmt::ByCasesStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Cases(
                crate::execute::execute_by_stmt::ExecByCasesStmtResult::Success(proof),
            )),
        ) => {
            if stmt.cases.is_empty()
                || stmt.then_facts.is_empty()
                || stmt.cases.len() != proof.branches.len()
                || stmt.proofs.len() != stmt.cases.len()
                || stmt.impossible_facts.len() != stmt.cases.len()
                || stmt.then_facts.len() != proof.then_facts_wd.len()
                || stmt.then_facts.len() != proof.stored_wd.len()
                || stmt.then_facts.len() != proof.stored.len()
                || !matches!(verified_subject(&proof.coverage), Some(Fact::OrFact(coverage)) if coverage.facts == stmt.cases)
            {
                false
            } else {
                let mut matches = stmt
                    .then_facts
                    .iter()
                    .zip(&proof.stored)
                    .all(|(source, stored)| stored_capture_matches(&stored.store, source));
                for (index, branch) in proof.branches.iter().enumerate() {
                    matches &= branch.assumption == stmt.cases[index]
                        && validate_captured_steps(&stmt.proofs[index], &branch.proof_steps)?;
                    matches &= match (&stmt.impossible_facts[index], &branch.closing) {
                        (Some(impossible), crate::execute::execute_by_stmt::ByCasesBranchClosingSuccess::Impossible(closing)) => {
                            let impossible = Fact::AtomicFact(impossible.clone());
                            closing.impossible_fact == impossible
                                && verified_subject(&closing.impossible).as_ref() == Some(&impossible)
                        }
                        (None, crate::execute::execute_by_stmt::ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts }) => {
                            proved_then_facts.len() == stmt.then_facts.len()
                                && proved_then_facts.iter().zip(&stmt.then_facts).all(|(proved, source)|
                                    verified_subject(&proved.verify_result).as_ref() == Some(source)
                                        && stored_capture_matches(&proved.store_and_infer.store, source))
                        }
                        _ => false,
                    };
                }
                matches
            }
        }
        (
            Stmt::ReleaseAndExpand(ReleaseAndExpandStmt::ReleaseThmStmt(stmt)),
            ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::Thm(
                crate::execute::execute_by_stmt::ExecReleaseThmStmtResult::Success(proof),
            )),
        ) => stmt.call == proof.call,
        (
            Stmt::By(ByStmt::ByInducStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Induc(
                crate::execute::execute_by_stmt::ExecByInducStmtResult::Success(proof),
            )),
        ) => {
            let expected: Vec<Fact> = stmt.to_prove.iter().cloned().map(Fact::from).collect();
            if stmt.param_binding != proof.parameter.name
                || stmt.induc_from != proof.induc_from
                || expected != proof.goals
            {
                false
            } else {
                let (base, step) = match &proof.body {
                    crate::execute::execute_by_stmt::ByInducBodySuccess::Structured {
                        base,
                        step,
                    } => {
                        if stmt.base_proof.is_none()
                            || stmt.step_proof.is_none()
                            || !stmt.proof.is_empty()
                        {
                            return Err(LeanCompileError::unsupported("Induction/BodyShape"));
                        }
                        (base, step)
                    }
                    crate::execute::execute_by_stmt::ByInducBodySuccess::Unstructured {
                        base,
                        step,
                    } => {
                        if stmt.base_proof.is_some() || stmt.step_proof.is_some() {
                            return Err(LeanCompileError::unsupported("Induction/BodyShape"));
                        }
                        (base, step)
                    }
                };
                let base_source = stmt.base_proof.as_deref().unwrap_or(&stmt.proof);
                let step_source = stmt.step_proof.as_deref().unwrap_or(&stmt.proof);
                if base_source.len() != base.proof_steps.len()
                    || step_source.len() != step.proof_steps.len()
                {
                    false
                } else {
                    for (source, result) in base_source
                        .iter()
                        .zip(&base.proof_steps)
                        .chain(step_source.iter().zip(&step.proof_steps))
                    {
                        validate_statement_capture(source, result)?;
                    }
                    true
                }
            }
        }
        _ => return Err(LeanCompileError::unsupported("Theorem/ProofStepCapture")),
    };
    if matches {
        Ok(())
    } else {
        Err(LeanCompileError::new(
            "Theorem/ProofStepCapture",
            "The executed statement differs from this source proof step.",
        ))
    }
}

fn validate_captured_steps(
    source: &[Stmt],
    captured: &[ExecStmtResult],
) -> Result<bool, LeanCompileError> {
    if source.len() != captured.len() {
        return Ok(false);
    }
    for (source, captured) in source.iter().zip(captured) {
        validate_statement_capture(source, captured)?;
    }
    Ok(true)
}

fn stored_capture_matches(store: &StoreFactResult, expected: &Fact) -> bool {
    let fact = match store {
        StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
        StoreFactResult::AndFact(stored) => Fact::AndFact(stored.fact.clone()),
        StoreFactResult::ChainFact(stored) => Fact::ChainFact(stored.fact.clone()),
        StoreFactResult::OrFact(stored) => Fact::OrFact(stored.fact.clone()),
        StoreFactResult::ForallFact(stored) => Fact::ForallFact(stored.fact.clone()),
        StoreFactResult::ExistShapedFact(stored) => {
            crate::ast::fact::exist_shaped_fact_to_fact(&stored.fact)
        }
        StoreFactResult::NotForallFact(stored) => Fact::NotForall(stored.fact.clone()),
        StoreFactResult::ForallFactWithIff(stored) => Fact::ForallFactWithIff(stored.fact.clone()),
    };
    fact == *expected && store.primary_fact_id() == expected.fact_id()
}

// Validate substitution against captured objects only. This neither creates
// fresh source IDs nor invokes Runtime instantiation or verification.
pub(super) fn instantiated_object_matches(
    expected: &Obj,
    actual: &Obj,
    substitution: &HashMap<IdentifierId, Obj>,
) -> bool {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = expected {
        if let Some(argument) = substitution.get(id) {
            return argument.ir() == actual.ir();
        }
    }
    match (expected, actual) {
        (Obj::ProductShape(expected), Obj::ProductShape(actual)) => {
            let (expected, actual) = match (expected, actual) {
                (ProductShape::Tuple(expected), ProductShape::Tuple(actual)) => {
                    (&expected.args, &actual.args)
                }
                (ProductShape::Cart(expected), ProductShape::Cart(actual)) => {
                    (&expected.args, &actual.args)
                }
                _ => return false,
            };
            expected.len() == actual.len()
                && expected.iter().zip(actual).all(|(expected, actual)| {
                    instantiated_object_matches(expected, actual, substitution)
                })
        }
        (Obj::FnObj(expected), Obj::FnObj(actual)) => {
            // Substituting p := F(a) into p(x) preserves the inserted prefix
            // F(a) and substitutes only the original argument groups.
            let inserted = match expected.head.as_ref() {
                FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) => {
                    match substitution.get(id) {
                        Some(Obj::FnObj(call)) => Some(call),
                        _ => None,
                    }
                }
                _ => None,
            };
            let prefix = inserted.map_or(0, |call| call.body.len());
            let head_matches = if let Some(call) = inserted {
                call.head == actual.head
                    && actual.body.len() >= prefix
                    && call
                        .body
                        .iter()
                        .zip(&actual.body)
                        .all(|(expected, actual)| {
                            expected.len() == actual.len()
                                && expected
                                    .iter()
                                    .zip(actual)
                                    .all(|(expected, actual)| expected.ir() == actual.ir())
                        })
            } else {
                instantiated_object_matches(
                    &function_head_object_for_match(&expected.head),
                    &function_head_object_for_match(&actual.head),
                    substitution,
                )
            };
            head_matches
                && expected.body.len() + prefix == actual.body.len()
                && expected
                    .body
                    .iter()
                    .zip(actual.body.iter().skip(prefix))
                    .all(|(expected, actual)| {
                        expected.len() == actual.len()
                            && expected.iter().zip(actual).all(|(expected, actual)| {
                                instantiated_object_matches(expected, actual, substitution)
                            })
                    })
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
        ) => {
            instantiated_object_matches(&a.base, &b.base, substitution)
                && instantiated_object_matches(&a.exponent, &b.exponent, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(b)),
        ) => instantiated_object_matches(&a.arg, &b.arg, substitution),
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(b)),
        ) => instantiated_object_matches(&a.arg, &b.arg, substitution),
        (
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)),
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(b)),
        ) => instantiated_object_matches(&a.arg, &b.arg, substitution),
        _ => expected.ir() == actual.ir(),
    }
}

fn function_head_object_for_match(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(value) => Obj::Identifier(value.clone()),
        FnObjHead::Object(value) => value.as_ref().clone(),
        FnObjHead::AnonymousFnLiteral(value) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(value.as_ref().clone()))
        }
        FnObjHead::FieldAccess(value) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(value.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(value) => Obj::InstantiatedTemplateObj(value.clone()),
    }
}

pub(super) fn instantiated_fact_matches(
    expected: &Fact,
    actual: &Fact,
    substitution: &HashMap<IdentifierId, Obj>,
) -> bool {
    match (expected, actual) {
        (Fact::AtomicFact(expected), Fact::AtomicFact(actual))
            if expected.prop_name() == actual.prop_name()
                && atomic_fact_has_positive_polarity(expected)
                    == atomic_fact_has_positive_polarity(actual) =>
        {
            let left = atomic_fact_args_ref(expected);
            let right = atomic_fact_args_ref(actual);
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(a, b)| instantiated_object_matches(a, b, substitution))
        }
        (Fact::AndFact(expected), Fact::AndFact(actual)) => {
            expected.facts.len() == actual.facts.len()
                && expected
                    .facts
                    .iter()
                    .zip(&actual.facts)
                    .all(|(expected, actual)| {
                        instantiated_fact_matches(
                            &Fact::AtomicFact(expected.clone()),
                            &Fact::AtomicFact(actual.clone()),
                            substitution,
                        )
                    })
        }
        (Fact::OrFact(expected), Fact::OrFact(actual)) => {
            expected.facts.len() == actual.facts.len()
                && expected
                    .facts
                    .iter()
                    .zip(&actual.facts)
                    .all(|(expected, actual)| {
                        instantiated_fact_matches(
                            &crate::ast::fact::and_chain_as_fact(expected),
                            &crate::ast::fact::and_chain_as_fact(actual),
                            substitution,
                        )
                    })
        }
        (Fact::ExistFact(expected), Fact::ExistFact(actual)) => {
            if expected.typed_parameters.groups.len() != actual.typed_parameters.groups.len()
                || expected.facts.len() != actual.facts.len()
            {
                return false;
            }
            let mut scoped = substitution.clone();
            for id in expected.typed_parameters.ordered_param_ids() {
                scoped.remove(&id);
            }
            expected
                .typed_parameters
                .groups
                .iter()
                .zip(&actual.typed_parameters.groups)
                .all(|(left, right)| {
                    left.params
                        .iter()
                        .map(|p| p.id)
                        .eq(right.params.iter().map(|p| p.id))
                        && match (&left.param_type, &right.param_type) {
                            (ParamType::Obj(left), ParamType::Obj(right)) => {
                                instantiated_object_matches(left, right, &scoped)
                            }
                            (ParamType::Set(_), ParamType::Set(_)) => true,
                            _ => false,
                        }
                })
                && expected
                    .facts
                    .iter()
                    .zip(&actual.facts)
                    .all(|(left, right)| {
                        instantiated_fact_matches(
                            &crate::instantiate::quantifier_free_fact_to_fact(left.clone()),
                            &crate::instantiate::quantifier_free_fact_to_fact(right.clone()),
                            &scoped,
                        )
                    })
        }
        (Fact::ChainFact(expected), Fact::ChainFact(actual)) => {
            expected.prop_names == actual.prop_names
                && expected.objs.len() == actual.objs.len()
                && expected
                    .objs
                    .iter()
                    .zip(&actual.objs)
                    .all(|(expected, actual)| {
                        instantiated_object_matches(expected, actual, substitution)
                    })
        }
        _ => false,
    }
}

pub(super) fn conjunction_proposition(
    propositions: Vec<String>,
) -> Result<String, LeanCompileError> {
    let mut propositions = propositions.into_iter().rev();
    let Some(mut proposition) = propositions.next() else {
        return Err(LeanCompileError::unsupported("Compound/EmptyConjunction"));
    };
    for left in propositions {
        proposition = format!("(({left}) ∧ ({proposition}))");
    }
    Ok(proposition)
}

pub(super) fn conjunction_projection(proof: &str, index: usize, count: usize) -> String {
    let mut proof = proof.to_string();
    for _ in 0..index {
        proof = format!("(And.right {proof})");
    }
    if index + 1 < count {
        proof = format!("(And.left {proof})");
    }
    proof
}

pub(super) fn validate_namespace(value: &str) -> Result<(), LeanCompileError> {
    let mut bytes = value.bytes();
    let valid_start = bytes
        .next()
        .map(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        .unwrap_or(false);
    let reserved = [
        "_",
        "axiom",
        "by",
        "class",
        "def",
        "do",
        "else",
        "end",
        "example",
        "export",
        "false",
        "forall",
        "from",
        "fun",
        "if",
        "import",
        "in",
        "inductive",
        "instance",
        "let",
        "macro",
        "match",
        "mutual",
        "namespace",
        "noncomputable",
        "opaque",
        "open",
        "partial",
        "private",
        "protected",
        "section",
        "set_option",
        "structure",
        "syntax",
        "then",
        "theorem",
        "true",
        "universe",
        "unsafe",
        "variable",
        "where",
        "with",
    ];
    if !valid_start
        || !bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        || reserved.contains(&value)
    {
        return Err(LeanCompileError::new(
            "artifact_namespace",
            "The artifact namespace must be a simple nonreserved ASCII Lean identifier.",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod function_substitution_tests {
    use super::*;

    fn runtime() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        })
    }

    fn name(runtime: &mut Runtime, text: &str) -> (IdentifierId, Obj) {
        let id = runtime.global_ids.allocate_identifier_id();
        (id, Obj::Identifier(IdentifierObj::plain(id, text.into())))
    }

    fn call(head: Obj, arguments: Vec<Obj>) -> Obj {
        Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::from_obj(head)),
            body: vec![arguments.into_iter().map(Box::new).collect()],
        })
    }

    #[test]
    fn source_function_parameter_substitutes_in_coordinate_head_by_id() {
        let mut runtime = runtime();
        let (p_id, p) = name(&mut runtime, "u");
        let (_, argument) = name(&mut runtime, "u");
        let (_, wrong) = name(&mut runtime, "u");
        let one = Obj::Literal(Literal::Number(Number::new("1".into())));
        let expected = call(p, vec![one.clone()]);
        let substitution = HashMap::from([(p_id, argument.clone())]);
        assert!(instantiated_object_matches(
            &expected,
            &call(argument, vec![one.clone()]),
            &substitution
        ));
        assert!(!instantiated_object_matches(
            &expected,
            &call(wrong, vec![one]),
            &substitution
        ));
    }

    #[test]
    fn inserted_application_prefix_retains_its_simultaneous_bindings() {
        let mut runtime = runtime();
        let (p_id, p) = name(&mut runtime, "p");
        let (a_id, a) = name(&mut runtime, "a");
        let (_, f) = name(&mut runtime, "F");
        let seven = Obj::Literal(Literal::Number(Number::new("7".into())));
        let expected = call(p, vec![a.clone()]);
        let replacement = call(f.clone(), vec![a.clone()]);
        let substitution = HashMap::from([(p_id, replacement.clone()), (a_id, seven.clone())]);
        let Obj::FnObj(mut actual) = replacement else {
            unreachable!()
        };
        actual.body.push(vec![Box::new(seven.clone())]);
        assert!(instantiated_object_matches(
            &expected,
            &Obj::FnObj(actual.clone()),
            &substitution
        ));
        actual.body[0][0] = Box::new(seven);
        assert!(!instantiated_object_matches(
            &expected,
            &Obj::FnObj(actual),
            &substitution
        ));
    }
}
