use super::LeanCompileError;
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::prelude::*;
use std::collections::HashMap;

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
        _ => Err(LeanCompileError::unsupported("Rational/ExpressionDomain")),
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
        _ => None,
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
        StandardSet::NPos
        | StandardSet::QPos
        | StandardSet::RPos
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
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(_)
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
        _ => None,
    }
}

pub(super) fn validate_statement_capture(
    source: &Stmt,
    result: &ExecStmtResult,
) -> Result<(), LeanCompileError> {
    let matches = match (source, result) {
        (Stmt::Fact(fact), ExecStmtResult::Fact(ExecFactStmtResult::Success(proof))) => {
            verified_subject(&proof.verify_result).as_ref() == Some(fact)
        }
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
        (Obj::FnObj(expected), Obj::FnObj(actual)) => {
            expected.head == actual.head
                && expected.body.len() == actual.body.len()
                && expected
                    .body
                    .iter()
                    .zip(&actual.body)
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
        _ => expected.ir() == actual.ir(),
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
        proposition = format!("({left} ∧ {proposition})");
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
