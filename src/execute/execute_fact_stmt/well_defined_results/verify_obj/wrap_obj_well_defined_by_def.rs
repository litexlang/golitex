use super::fail_to_verify_obj_well_defined::*;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::*;
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::ast::obj::{
    ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FunctionSpace,
    IntegerOperator, IteratedOperator, Literal, Obj, ProductShape, SetFormer, SetOperator,
    StructAndFieldAccessObj, TrigOperator,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

// Pack CommonStages into the Obj-mirrored ByDef proof, or the mirrored fail.
pub(super) fn finish_by_def(
    obj: &Obj,
    stages: ObjWellDefinedByDefCommonStages,
) -> Result<ObjWellDefinedProofByDef, FailToVerifyObjWellDefinedResult> {
    if !stages.is_fully_known() {
        return Err(wrap_common_fail(obj, stages.into_common_fail(obj)));
    }
    Ok(pack_success_by_def(obj, stages))
}

fn expect_success_obj_proof(result: VerifyObjWellDefinedResult) -> Box<ObjWellDefinedProof> {
    match result {
        VerifyObjWellDefinedResult::Success(proof) => Box::new(proof),
        VerifyObjWellDefinedResult::Failed { .. } => {
            unreachable!("finish_by_def only packs fully-known stages")
        }
    }
}

fn take_child_proofs(
    stages: &mut ObjWellDefinedByDefCommonStages,
    n: usize,
) -> Vec<Box<ObjWellDefinedProof>> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let result = stages.child_obj_well_defined.remove(0);
        out.push(expect_success_obj_proof(result));
    }
    out
}

fn take_requirements(
    stages: &mut ObjWellDefinedByDefCommonStages,
    n: usize,
) -> Vec<VerifyFactResult> {
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(stages.requirement_fact_verified.remove(0));
    }
    out
}

fn pack_success_by_def(
    obj: &Obj,
    mut stages: ObjWellDefinedByDefCommonStages,
) -> ObjWellDefinedProofByDef {
    match obj {
        Obj::Identifier(_) | Obj::Literal(Literal::Number(_)) | Obj::Literal(Literal::ImaginaryUnit(_)) | Obj::Literal(Literal::EulerNumber(_)) | Obj::Literal(Literal::Pi(_)) | Obj::StandardSet(_) => {
            let _ = stages;
            match obj {
                Obj::Identifier(_) => ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new()),
                Obj::Literal(Literal::Number(_)) => ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(NumberObjWellDefinedProof::new())),
                Obj::Literal(Literal::ImaginaryUnit(_)) => ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::ImaginaryUnit(ImaginaryUnitObjWellDefinedProof::new())),
                Obj::Literal(Literal::EulerNumber(_)) => ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::EulerNumber(EulerNumberObjWellDefinedProof::new())),
                Obj::Literal(Literal::Pi(_)) => ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Pi(PiObjWellDefinedProof::new())),
                Obj::StandardSet(_) => ObjWellDefinedProofByDef::StandardSet(StandardSetObjWellDefinedProof::new()),
                _ => unreachable!("leaf Obj arm"),
            }
        }
        Obj::FnObj(_) => ObjWellDefinedProofByDef::FnObj(FnObjObjWellDefinedProof::from_stages(stages)),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Add(AddObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Sub(SubObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Neg(NegObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Mul(MulObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Div(DivObjWellDefinedProof::from_stages(stages))),
        Obj::IntegerOperator(IntegerOperator::Mod(_)) => ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Mod(ModObjWellDefinedProof::from_stages(stages))),
        Obj::IntegerOperator(IntegerOperator::Quot(_)) => ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Quot(QuotObjWellDefinedProof::from_stages(stages))),
        Obj::IntegerOperator(IntegerOperator::Gcd(_)) => ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Gcd(GcdObjWellDefinedProof::from_stages(stages))),
        Obj::IntegerOperator(IntegerOperator::Lcm(_)) => ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Lcm(LcmObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Floor(FloorObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Ceil(CeilObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Min(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Min(MinObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Max(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Max(MaxObjWellDefinedProof::from_stages(stages))),
        Obj::ExpLogOperator(ExpLogOperator::Exp(_)) => ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Exp(ExpObjWellDefinedProof::from_stages(stages))),
        Obj::ExpLogOperator(ExpLogOperator::Ln(_)) => ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Ln(LnObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Sign(SignObjWellDefinedProof::from_stages(stages))),
        Obj::IntegerOperator(IntegerOperator::Factorial(_)) => ObjWellDefinedProofByDef::IntegerOperator(IntegerOperatorObjWellDefinedProofByDef::Factorial(FactorialObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Pow(PowObjWellDefinedProof::from_stages(stages))),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)) => ObjWellDefinedProofByDef::ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef::Abs(AbsObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Sin(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Sin(SinObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Arcsin(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arcsin(ArcsinObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Arccos(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccos(ArccosObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Arctan(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arctan(ArctanObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Arccot(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Arccot(ArccotObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Cos(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cos(CosObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Tan(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Tan(TanObjWellDefinedProof::from_stages(stages))),
        Obj::TrigOperator(TrigOperator::Cot(_)) => ObjWellDefinedProofByDef::TrigOperator(TrigOperatorObjWellDefinedProofByDef::Cot(CotObjWellDefinedProof::from_stages(stages))),
        Obj::ComplexOperator(ComplexOperator::RealPart(_)) => ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::RealPart(RealPartObjWellDefinedProof::from_stages(stages))),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)) => ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::ImaginaryPart(ImaginaryPartObjWellDefinedProof::from_stages(stages))),
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(_)) => ObjWellDefinedProofByDef::ComplexOperator(ComplexOperatorObjWellDefinedProofByDef::ComplexAbs(ComplexAbsObjWellDefinedProof::from_stages(stages))),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)) => ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(SqrtObjWellDefinedProof::from_stages(stages))),
        Obj::ExpLogOperator(ExpLogOperator::Log(_)) => ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Log(LogObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::Union(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::Union(UnionObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::Intersect(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::Intersect(IntersectObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::SetMinus(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::SetMinus(SetMinusObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::FamilyUnion(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::FamilyUnion(FamilyUnionObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::FamilyIntersect(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::FamilyIntersect(FamilyIntersectObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::IndexUnion(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexUnion(IndexUnionObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::IndexIntersect(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexIntersect(IndexIntersectObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::PowerSet(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::PowerSet(PowerSetObjWellDefinedProof::from_stages(stages))),
        Obj::SetOperator(SetOperator::IndexCart(_)) => ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexCart(IndexCartObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::ListSet(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ListSet(ListSetObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::SetBuilder(_)) | Obj::FunctionSpace(FunctionSpace::FnSet(_)) | Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) => {
            unreachable!("binder object WD must use dedicated binder pipelines, not CommonStages")
        }
        Obj::ProductShape(ProductShape::Cart(_)) => ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Cart(CartObjWellDefinedProof::from_stages(stages))),
        Obj::ProductShape(ProductShape::CartDim(_)) => {
            let mut children = take_child_proofs(&mut stages, 1);
            let mut reqs = take_requirements(&mut stages, 1);
            ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::CartDim(CartDimObjWellDefinedProof {
                set_well_defined: children.remove(0),
                set_is_cart: reqs.remove(0),
            }))
        }
        Obj::ProductShape(ProductShape::Proj(_)) => {
            let mut children = take_child_proofs(&mut stages, 2);
            let mut reqs = take_requirements(&mut stages, 3);
            ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Proj(ProjObjWellDefinedProof {
                set_well_defined: children.remove(0),
                dim_well_defined: children.remove(0),
                dim_in_npos: reqs.remove(0),
                set_is_cart: reqs.remove(0),
                dim_le_cart_dim: reqs.remove(0),
            }))
        }
        Obj::ProductShape(ProductShape::TupleDim(_)) => {
            let mut children = take_child_proofs(&mut stages, 1);
            let mut reqs = take_requirements(&mut stages, 1);
            ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::TupleDim(TupleDimObjWellDefinedProof {
                arg_well_defined: children.remove(0),
                arg_is_tuple: reqs.remove(0),
            }))
        }
        Obj::ProductShape(ProductShape::Tuple(_)) => ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Tuple(TupleObjWellDefinedProof::from_stages(stages))),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) => ObjWellDefinedProofByDef::FiniteSetStat(FiniteSetStatObjWellDefinedProofByDef::FiniteSetSize(FiniteSetSizeObjWellDefinedProof::from_stages(stages))),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_)) => ObjWellDefinedProofByDef::FiniteSetStat(FiniteSetStatObjWellDefinedProofByDef::FiniteSetMax(FiniteSetMaxObjWellDefinedProof::from_stages(stages))),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_)) => ObjWellDefinedProofByDef::FiniteSetStat(FiniteSetStatObjWellDefinedProofByDef::FiniteSetMin(FiniteSetMinObjWellDefinedProof::from_stages(stages))),
        Obj::FunctionSpace(FunctionSpace::FnRange(_)) => ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnRange(FnRangeObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::Sum(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::Sum(SumObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::SumOfFiniteSet(SumOfFiniteSetObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::Product(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::Product(ProductObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::ProductOfFiniteSet(ProductOfFiniteSetObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::Reduce(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::Reduce(ReduceObjWellDefinedProof::from_stages(stages))),
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(_)) => ObjWellDefinedProofByDef::IteratedOperator(IteratedOperatorObjWellDefinedProofByDef::FiniteSetReduce(FiniteSetReduceObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::Range(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::Range(RangeObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::ClosedRange(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::ClosedRange(ClosedRangeObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::FiniteSeqSet(FiniteSeqSetObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::SeqSet(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::SeqSet(SeqSetObjWellDefinedProof::from_stages(stages))),
        Obj::ProductShape(ProductShape::ObjAtIndex(_)) => {
            let mut children = take_child_proofs(&mut stages, 2);
            let mut reqs = take_requirements(&mut stages, 3);
            ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::ObjAtIndex(ObjAtIndexObjWellDefinedProof {
                obj_well_defined: children.remove(0),
                index_well_defined: children.remove(0),
                index_in_npos: reqs.remove(0),
                obj_is_tuple: reqs.remove(0),
                index_le_tuple_dim: reqs.remove(0),
            }))
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_)) => ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(StructObjObjWellDefinedProof::from_stages(stages))),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_)) => ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::FieldAccess(FieldAccessObjWellDefinedProof::from_stages(stages))),
        Obj::InstantiatedTemplateObj(_) => ObjWellDefinedProofByDef::InstantiatedTemplateObj(InstantiatedTemplateObjObjWellDefinedProof::from_stages(stages)),
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(OneSideInfinityIntervalObjObjWellDefinedProof::from_stages(stages))),
        Obj::SetFormer(SetFormer::IntervalObj(_)) => ObjWellDefinedProofByDef::SetFormer(SetFormerObjWellDefinedProofByDef::IntervalObj(IntervalObjObjWellDefinedProof::from_stages(stages))),
    }
}

pub(super) fn wrap_common_fail(
    obj: &Obj,
    common: FailToVerifyObjWellDefinedByDefCommon,
) -> FailToVerifyObjWellDefinedResult {
    match obj {
        Obj::Identifier(_) => FailToVerifyObjWellDefinedResult::Identifier(
            FailToVerifyIdentifierObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "identifier well-definedness failed".to_string(),
            }),
        ),
        Obj::FnObj(_) => FailToVerifyObjWellDefinedResult::FnObj(
            FailToVerifyFnObjObjWellDefined::Domain(common),
        ),
        Obj::Literal(Literal::Number(_)) => FailToVerifyObjWellDefinedResult::Literal(FailToVerifyLiteralObjWellDefinedResult::Number(
            FailToVerifyNumberObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "Number well-definedness failed".to_string(),
            }),
        )),
        Obj::Literal(Literal::ImaginaryUnit(_)) => FailToVerifyObjWellDefinedResult::Literal(FailToVerifyLiteralObjWellDefinedResult::ImaginaryUnit(
            FailToVerifyImaginaryUnitObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "ImaginaryUnit well-definedness failed".to_string(),
            }),
        )),
        Obj::Literal(Literal::EulerNumber(_)) => FailToVerifyObjWellDefinedResult::Literal(FailToVerifyLiteralObjWellDefinedResult::EulerNumber(
            FailToVerifyEulerNumberObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "EulerNumber well-definedness failed".to_string(),
            }),
        )),
        Obj::Literal(Literal::Pi(_)) => FailToVerifyObjWellDefinedResult::Literal(FailToVerifyLiteralObjWellDefinedResult::Pi(
            FailToVerifyPiObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "Pi well-definedness failed".to_string(),
            }),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Add(
            FailToVerifyAddObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Sub(
            FailToVerifySubObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Neg(
            FailToVerifyNegObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Mul(
            FailToVerifyMulObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Div(
            FailToVerifyDivObjWellDefined(common),
        )),
        Obj::IntegerOperator(IntegerOperator::Mod(_)) => FailToVerifyObjWellDefinedResult::IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult::Mod(
            FailToVerifyModObjWellDefined(common),
        )),
        Obj::IntegerOperator(IntegerOperator::Quot(_)) => FailToVerifyObjWellDefinedResult::IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult::Quot(
            FailToVerifyQuotObjWellDefined(common),
        )),
        Obj::IntegerOperator(IntegerOperator::Gcd(_)) => FailToVerifyObjWellDefinedResult::IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult::Gcd(
            FailToVerifyGcdObjWellDefined(common),
        )),
        Obj::IntegerOperator(IntegerOperator::Lcm(_)) => FailToVerifyObjWellDefinedResult::IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult::Lcm(
            FailToVerifyLcmObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Floor(
            FailToVerifyFloorObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Ceil(
            FailToVerifyCeilObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Min(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Min(
            FailToVerifyMinObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Max(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Max(
            FailToVerifyMaxObjWellDefined(common),
        )),
        Obj::ExpLogOperator(ExpLogOperator::Exp(_)) => FailToVerifyObjWellDefinedResult::ExpLogOperator(FailToVerifyExpLogOperatorObjWellDefinedResult::Exp(
            FailToVerifyExpObjWellDefined(common),
        )),
        Obj::ExpLogOperator(ExpLogOperator::Ln(_)) => FailToVerifyObjWellDefinedResult::ExpLogOperator(FailToVerifyExpLogOperatorObjWellDefinedResult::Ln(
            FailToVerifyLnObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Sign(
            FailToVerifySignObjWellDefined(common),
        )),
        Obj::IntegerOperator(IntegerOperator::Factorial(_)) => FailToVerifyObjWellDefinedResult::IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult::Factorial(
            FailToVerifyFactorialObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Pow(
            FailToVerifyPowObjWellDefined(common),
        )),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)) => FailToVerifyObjWellDefinedResult::ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult::Abs(
            FailToVerifyAbsObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Sin(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Sin(
            FailToVerifySinObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Arcsin(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Arcsin(
            FailToVerifyArcsinObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Arccos(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Arccos(
            FailToVerifyArccosObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Arctan(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Arctan(
            FailToVerifyArctanObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Arccot(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Arccot(
            FailToVerifyArccotObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Cos(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Cos(
            FailToVerifyCosObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Tan(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Tan(
            FailToVerifyTanObjWellDefined(common),
        )),
        Obj::TrigOperator(TrigOperator::Cot(_)) => FailToVerifyObjWellDefinedResult::TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult::Cot(
            FailToVerifyCotObjWellDefined(common),
        )),
        Obj::ComplexOperator(ComplexOperator::RealPart(_)) => FailToVerifyObjWellDefinedResult::ComplexOperator(FailToVerifyComplexOperatorObjWellDefinedResult::RealPart(
            FailToVerifyRealPartObjWellDefined(common),
        )),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)) => FailToVerifyObjWellDefinedResult::ComplexOperator(FailToVerifyComplexOperatorObjWellDefinedResult::ImaginaryPart(
            FailToVerifyImaginaryPartObjWellDefined(common),
        )),
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(_)) => FailToVerifyObjWellDefinedResult::ComplexOperator(FailToVerifyComplexOperatorObjWellDefinedResult::ComplexAbs(
            FailToVerifyComplexAbsObjWellDefined(common),
        )),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)) => FailToVerifyObjWellDefinedResult::ExpLogOperator(FailToVerifyExpLogOperatorObjWellDefinedResult::Sqrt(
            FailToVerifySqrtObjWellDefined(common),
        )),
        Obj::ExpLogOperator(ExpLogOperator::Log(_)) => FailToVerifyObjWellDefinedResult::ExpLogOperator(FailToVerifyExpLogOperatorObjWellDefinedResult::Log(
            FailToVerifyLogObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::Union(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::Union(
            FailToVerifyUnionObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::Intersect(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::Intersect(
            FailToVerifyIntersectObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::SetMinus(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::SetMinus(
            FailToVerifySetMinusObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::FamilyUnion(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::FamilyUnion(
            FailToVerifyFamilyUnionObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::FamilyIntersect(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::FamilyIntersect(
            FailToVerifyFamilyIntersectObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::IndexUnion(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexUnion(
            FailToVerifyIndexUnionObjWellDefined::Domain(common),
        )),
        Obj::SetOperator(SetOperator::IndexIntersect(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexIntersect(
            FailToVerifyIndexIntersectObjWellDefined::Domain(common),
        )),
        Obj::SetOperator(SetOperator::PowerSet(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::PowerSet(
            FailToVerifyPowerSetObjWellDefined(common),
        )),
        Obj::SetOperator(SetOperator::IndexCart(_)) => FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexCart(
            FailToVerifyIndexCartObjWellDefined::Domain(common),
        )),
        Obj::SetFormer(SetFormer::ListSet(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::ListSet(
            FailToVerifyListSetObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::SetBuilder(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::SetBuilder(
            FailToVerifySetBuilderObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "SetBuilder well-definedness failed".to_string(),
            }),
        )),
        Obj::FunctionSpace(FunctionSpace::FnSet(_)) => FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::FnSet(
            FailToVerifyFnSetObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "FnSet well-definedness failed".to_string(),
            }),
        )),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(_)) => FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::AnonymousFn(
            FailToVerifyAnonymousFnObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "AnonymousFn well-definedness failed".to_string(),
            }),
        )),
        Obj::ProductShape(ProductShape::Cart(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::Cart(
            FailToVerifyCartObjWellDefined(common),
        )),
        Obj::ProductShape(ProductShape::CartDim(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::CartDim(
            FailToVerifyCartDimObjWellDefined(common),
        )),
        Obj::ProductShape(ProductShape::Proj(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::Proj(
            FailToVerifyProjObjWellDefined(common),
        )),
        Obj::ProductShape(ProductShape::TupleDim(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::TupleDim(
            FailToVerifyTupleDimObjWellDefined(common),
        )),
        Obj::ProductShape(ProductShape::Tuple(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::Tuple(
            FailToVerifyTupleObjWellDefined(common),
        )),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_)) => FailToVerifyObjWellDefinedResult::FiniteSetStat(FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetSize(
            FailToVerifyFiniteSetSizeObjWellDefined(common),
        )),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_)) => FailToVerifyObjWellDefinedResult::FiniteSetStat(FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetMax(
            FailToVerifyFiniteSetMaxObjWellDefined(common),
        )),
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_)) => FailToVerifyObjWellDefinedResult::FiniteSetStat(FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetMin(
            FailToVerifyFiniteSetMinObjWellDefined(common),
        )),
        Obj::FunctionSpace(FunctionSpace::FnRange(_)) => FailToVerifyObjWellDefinedResult::FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult::FnRange(
            FailToVerifyFnRangeObjWellDefined::Domain(common),
        )),
        Obj::IteratedOperator(IteratedOperator::Sum(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::Sum(
            FailToVerifySumObjWellDefined(common),
        )),
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::SumOfFiniteSet(
            FailToVerifySumOfFiniteSetObjWellDefined(common),
        )),
        Obj::IteratedOperator(IteratedOperator::Product(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::Product(
            FailToVerifyProductObjWellDefined(common),
        )),
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::ProductOfFiniteSet(
            FailToVerifyProductOfFiniteSetObjWellDefined(common),
        )),
        Obj::IteratedOperator(IteratedOperator::Reduce(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::Reduce(
            FailToVerifyReduceObjWellDefined(common),
        )),
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(_)) => FailToVerifyObjWellDefinedResult::IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult::FiniteSetReduce(
            FailToVerifyFiniteSetReduceObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::Range(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::Range(
            FailToVerifyRangeObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::ClosedRange(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::ClosedRange(
            FailToVerifyClosedRangeObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::FiniteSeqSet(
            FailToVerifyFiniteSeqSetObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::SeqSet(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::SeqSet(
            FailToVerifySeqSetObjWellDefined(common),
        )),
        Obj::ProductShape(ProductShape::ObjAtIndex(_)) => FailToVerifyObjWellDefinedResult::ProductShape(FailToVerifyProductShapeObjWellDefinedResult::ObjAtIndex(
            FailToVerifyObjAtIndexObjWellDefined(common),
        )),
        Obj::StandardSet(_) => FailToVerifyObjWellDefinedResult::StandardSet(
            FailToVerifyStandardSetObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "StandardSet well-definedness failed".to_string(),
            }),
        ),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_)) => FailToVerifyObjWellDefinedResult::Structish(FailToVerifyStructishObjWellDefinedResult::StructObj(
            FailToVerifyStructObjObjWellDefined(common),
        )),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(_)) => FailToVerifyObjWellDefinedResult::Structish(FailToVerifyStructishObjWellDefinedResult::FieldAccess(
            FailToVerifyFieldAccessObjWellDefined(common),
        )),
        Obj::InstantiatedTemplateObj(_) => FailToVerifyObjWellDefinedResult::InstantiatedTemplateObj(
            FailToVerifyInstantiatedTemplateObjObjWellDefined(common),
        ),
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::OneSideInfinityIntervalObj(
            FailToVerifyOneSideInfinityIntervalObjObjWellDefined(common),
        )),
        Obj::SetFormer(SetFormer::IntervalObj(_)) => FailToVerifyObjWellDefinedResult::SetFormer(FailToVerifySetFormerObjWellDefinedResult::IntervalObj(
            FailToVerifyIntervalObjObjWellDefined(common),
        )),
    }
}

