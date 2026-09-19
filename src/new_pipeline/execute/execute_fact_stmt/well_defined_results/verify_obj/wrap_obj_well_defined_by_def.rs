use super::fail_to_verify_obj_well_defined::*;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::*;
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

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
        VerifyObjWellDefinedResult::Failed(_) => {
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
        let (_obj, result) = stages.child_obj_well_defined.remove(0);
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
        Obj::Identifier(_) | Obj::Number(_) | Obj::ImaginaryUnit(_) | Obj::EulerNumber(_) | Obj::Pi(_) | Obj::StandardSet(_) => {
            let _ = stages;
            match obj {
                Obj::Identifier(_) => ObjWellDefinedProofByDef::Identifier(IdentifierObjWellDefinedProof::new()),
                Obj::Number(_) => ObjWellDefinedProofByDef::Number(NumberObjWellDefinedProof::new()),
                Obj::ImaginaryUnit(_) => ObjWellDefinedProofByDef::ImaginaryUnit(ImaginaryUnitObjWellDefinedProof::new()),
                Obj::EulerNumber(_) => ObjWellDefinedProofByDef::EulerNumber(EulerNumberObjWellDefinedProof::new()),
                Obj::Pi(_) => ObjWellDefinedProofByDef::Pi(PiObjWellDefinedProof::new()),
                Obj::StandardSet(_) => ObjWellDefinedProofByDef::StandardSet(StandardSetObjWellDefinedProof::new()),
                _ => unreachable!("leaf Obj arm"),
            }
        }
        Obj::FnObj(_) => ObjWellDefinedProofByDef::FnObj(FnObjObjWellDefinedProof::from_stages(stages)),
        Obj::Add(_) => ObjWellDefinedProofByDef::Add(AddObjWellDefinedProof::from_stages(stages)),
        Obj::Sub(_) => ObjWellDefinedProofByDef::Sub(SubObjWellDefinedProof::from_stages(stages)),
        Obj::Mul(_) => ObjWellDefinedProofByDef::Mul(MulObjWellDefinedProof::from_stages(stages)),
        Obj::Div(_) => ObjWellDefinedProofByDef::Div(DivObjWellDefinedProof::from_stages(stages)),
        Obj::Mod(_) => ObjWellDefinedProofByDef::Mod(ModObjWellDefinedProof::from_stages(stages)),
        Obj::Quot(_) => ObjWellDefinedProofByDef::Quot(QuotObjWellDefinedProof::from_stages(stages)),
        Obj::Gcd(_) => ObjWellDefinedProofByDef::Gcd(GcdObjWellDefinedProof::from_stages(stages)),
        Obj::Lcm(_) => ObjWellDefinedProofByDef::Lcm(LcmObjWellDefinedProof::from_stages(stages)),
        Obj::Floor(_) => ObjWellDefinedProofByDef::Floor(FloorObjWellDefinedProof::from_stages(stages)),
        Obj::Ceil(_) => ObjWellDefinedProofByDef::Ceil(CeilObjWellDefinedProof::from_stages(stages)),
        Obj::Min(_) => ObjWellDefinedProofByDef::Min(MinObjWellDefinedProof::from_stages(stages)),
        Obj::Max(_) => ObjWellDefinedProofByDef::Max(MaxObjWellDefinedProof::from_stages(stages)),
        Obj::Exp(_) => ObjWellDefinedProofByDef::Exp(ExpObjWellDefinedProof::from_stages(stages)),
        Obj::Ln(_) => ObjWellDefinedProofByDef::Ln(LnObjWellDefinedProof::from_stages(stages)),
        Obj::Sign(_) => ObjWellDefinedProofByDef::Sign(SignObjWellDefinedProof::from_stages(stages)),
        Obj::Factorial(_) => ObjWellDefinedProofByDef::Factorial(FactorialObjWellDefinedProof::from_stages(stages)),
        Obj::Pow(_) => ObjWellDefinedProofByDef::Pow(PowObjWellDefinedProof::from_stages(stages)),
        Obj::Abs(_) => ObjWellDefinedProofByDef::Abs(AbsObjWellDefinedProof::from_stages(stages)),
        Obj::Sin(_) => ObjWellDefinedProofByDef::Sin(SinObjWellDefinedProof::from_stages(stages)),
        Obj::Arcsin(_) => ObjWellDefinedProofByDef::Arcsin(ArcsinObjWellDefinedProof::from_stages(stages)),
        Obj::Cos(_) => ObjWellDefinedProofByDef::Cos(CosObjWellDefinedProof::from_stages(stages)),
        Obj::Tan(_) => ObjWellDefinedProofByDef::Tan(TanObjWellDefinedProof::from_stages(stages)),
        Obj::Cot(_) => ObjWellDefinedProofByDef::Cot(CotObjWellDefinedProof::from_stages(stages)),
        Obj::RealPart(_) => ObjWellDefinedProofByDef::RealPart(RealPartObjWellDefinedProof::from_stages(stages)),
        Obj::ImaginaryPart(_) => ObjWellDefinedProofByDef::ImaginaryPart(ImaginaryPartObjWellDefinedProof::from_stages(stages)),
        Obj::ComplexAbs(_) => ObjWellDefinedProofByDef::ComplexAbs(ComplexAbsObjWellDefinedProof::from_stages(stages)),
        Obj::Sqrt(_) => ObjWellDefinedProofByDef::Sqrt(SqrtObjWellDefinedProof::from_stages(stages)),
        Obj::Log(_) => ObjWellDefinedProofByDef::Log(LogObjWellDefinedProof::from_stages(stages)),
        Obj::Union(_) => ObjWellDefinedProofByDef::Union(UnionObjWellDefinedProof::from_stages(stages)),
        Obj::Intersect(_) => ObjWellDefinedProofByDef::Intersect(IntersectObjWellDefinedProof::from_stages(stages)),
        Obj::SetMinus(_) => ObjWellDefinedProofByDef::SetMinus(SetMinusObjWellDefinedProof::from_stages(stages)),
        Obj::BigUnion(_) => ObjWellDefinedProofByDef::BigUnion(BigUnionObjWellDefinedProof::from_stages(stages)),
        Obj::BigIntersect(_) => ObjWellDefinedProofByDef::BigIntersect(BigIntersectObjWellDefinedProof::from_stages(stages)),
        Obj::IndexUnion(_) => ObjWellDefinedProofByDef::IndexUnion(IndexUnionObjWellDefinedProof::from_stages(stages)),
        Obj::IndexIntersect(_) => ObjWellDefinedProofByDef::IndexIntersect(IndexIntersectObjWellDefinedProof::from_stages(stages)),
        Obj::PowerSet(_) => ObjWellDefinedProofByDef::PowerSet(PowerSetObjWellDefinedProof::from_stages(stages)),
        Obj::GeneralCart(_) => ObjWellDefinedProofByDef::GeneralCart(GeneralCartObjWellDefinedProof::from_stages(stages)),
        Obj::ListSet(_) => ObjWellDefinedProofByDef::ListSet(ListSetObjWellDefinedProof::from_stages(stages)),
        Obj::SetBuilder(_) | Obj::FnSet(_) | Obj::AnonymousFn(_) => {
            unreachable!("binder object WD must use dedicated binder pipelines, not CommonStages")
        }
        Obj::Cart(_) => ObjWellDefinedProofByDef::Cart(CartObjWellDefinedProof::from_stages(stages)),
        Obj::CartDim(_) => {
            let mut children = take_child_proofs(&mut stages, 1);
            let mut reqs = take_requirements(&mut stages, 1);
            ObjWellDefinedProofByDef::CartDim(CartDimObjWellDefinedProof {
                set_well_defined: children.remove(0),
                set_is_cart: reqs.remove(0),
            })
        }
        Obj::Proj(_) => {
            let mut children = take_child_proofs(&mut stages, 2);
            let mut reqs = take_requirements(&mut stages, 3);
            ObjWellDefinedProofByDef::Proj(ProjObjWellDefinedProof {
                set_well_defined: children.remove(0),
                dim_well_defined: children.remove(0),
                dim_in_npos: reqs.remove(0),
                set_is_cart: reqs.remove(0),
                dim_le_cart_dim: reqs.remove(0),
            })
        }
        Obj::TupleDim(_) => {
            let mut children = take_child_proofs(&mut stages, 1);
            let mut reqs = take_requirements(&mut stages, 1);
            ObjWellDefinedProofByDef::TupleDim(TupleDimObjWellDefinedProof {
                arg_well_defined: children.remove(0),
                arg_is_tuple: reqs.remove(0),
            })
        }
        Obj::Tuple(_) => ObjWellDefinedProofByDef::Tuple(TupleObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSetSize(_) => ObjWellDefinedProofByDef::FiniteSetSize(FiniteSetSizeObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSetMax(_) => ObjWellDefinedProofByDef::FiniteSetMax(FiniteSetMaxObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSetMin(_) => ObjWellDefinedProofByDef::FiniteSetMin(FiniteSetMinObjWellDefinedProof::from_stages(stages)),
        Obj::FnRange(_) => ObjWellDefinedProofByDef::FnRange(FnRangeObjWellDefinedProof::from_stages(stages)),
        Obj::Replacement(_) => ObjWellDefinedProofByDef::Replacement(ReplacementObjWellDefinedProof::from_stages(stages)),
        Obj::Sum(_) => ObjWellDefinedProofByDef::Sum(SumObjWellDefinedProof::from_stages(stages)),
        Obj::SumOfFiniteSet(_) => ObjWellDefinedProofByDef::SumOfFiniteSet(SumOfFiniteSetObjWellDefinedProof::from_stages(stages)),
        Obj::Product(_) => ObjWellDefinedProofByDef::Product(ProductObjWellDefinedProof::from_stages(stages)),
        Obj::ProductOfFiniteSet(_) => ObjWellDefinedProofByDef::ProductOfFiniteSet(ProductOfFiniteSetObjWellDefinedProof::from_stages(stages)),
        Obj::Reduce(_) => ObjWellDefinedProofByDef::Reduce(ReduceObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSetReduce(_) => ObjWellDefinedProofByDef::FiniteSetReduce(FiniteSetReduceObjWellDefinedProof::from_stages(stages)),
        Obj::Range(_) => ObjWellDefinedProofByDef::Range(RangeObjWellDefinedProof::from_stages(stages)),
        Obj::ClosedRange(_) => ObjWellDefinedProofByDef::ClosedRange(ClosedRangeObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSeqSet(_) => ObjWellDefinedProofByDef::FiniteSeqSet(FiniteSeqSetObjWellDefinedProof::from_stages(stages)),
        Obj::SeqSet(_) => ObjWellDefinedProofByDef::SeqSet(SeqSetObjWellDefinedProof::from_stages(stages)),
        Obj::FiniteSeqListObj(_) => ObjWellDefinedProofByDef::FiniteSeqListObj(FiniteSeqListObjObjWellDefinedProof::from_stages(stages)),
        Obj::ObjAtIndex(_) => {
            let mut children = take_child_proofs(&mut stages, 2);
            let mut reqs = take_requirements(&mut stages, 3);
            ObjWellDefinedProofByDef::ObjAtIndex(ObjAtIndexObjWellDefinedProof {
                obj_well_defined: children.remove(0),
                index_well_defined: children.remove(0),
                index_in_npos: reqs.remove(0),
                obj_is_tuple: reqs.remove(0),
                index_le_tuple_dim: reqs.remove(0),
            })
        }
        Obj::StructObj(_) => ObjWellDefinedProofByDef::StructObj(StructObjObjWellDefinedProof::from_stages(stages)),
        Obj::ObjAsStructInstanceWithFieldAccess(_) => ObjWellDefinedProofByDef::ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccessObjWellDefinedProof::from_stages(stages)),
        Obj::InstantiatedTemplateObj(_) => ObjWellDefinedProofByDef::InstantiatedTemplateObj(InstantiatedTemplateObjObjWellDefinedProof::from_stages(stages)),
        Obj::OneSideInfinityIntervalObj(_) => ObjWellDefinedProofByDef::OneSideInfinityIntervalObj(OneSideInfinityIntervalObjObjWellDefinedProof::from_stages(stages)),
        Obj::IntervalObj(_) => ObjWellDefinedProofByDef::IntervalObj(IntervalObjObjWellDefinedProof::from_stages(stages)),
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
        Obj::Number(_) => FailToVerifyObjWellDefinedResult::Number(
            FailToVerifyNumberObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "Number well-definedness failed".to_string(),
            }),
        ),
        Obj::ImaginaryUnit(_) => FailToVerifyObjWellDefinedResult::ImaginaryUnit(
            FailToVerifyImaginaryUnitObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "ImaginaryUnit well-definedness failed".to_string(),
            }),
        ),
        Obj::EulerNumber(_) => FailToVerifyObjWellDefinedResult::EulerNumber(
            FailToVerifyEulerNumberObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "EulerNumber well-definedness failed".to_string(),
            }),
        ),
        Obj::Pi(_) => FailToVerifyObjWellDefinedResult::Pi(
            FailToVerifyPiObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "Pi well-definedness failed".to_string(),
            }),
        ),
        Obj::Add(_) => FailToVerifyObjWellDefinedResult::Add(
            FailToVerifyAddObjWellDefined(common),
        ),
        Obj::Sub(_) => FailToVerifyObjWellDefinedResult::Sub(
            FailToVerifySubObjWellDefined(common),
        ),
        Obj::Mul(_) => FailToVerifyObjWellDefinedResult::Mul(
            FailToVerifyMulObjWellDefined(common),
        ),
        Obj::Div(_) => FailToVerifyObjWellDefinedResult::Div(
            FailToVerifyDivObjWellDefined(common),
        ),
        Obj::Mod(_) => FailToVerifyObjWellDefinedResult::Mod(
            FailToVerifyModObjWellDefined(common),
        ),
        Obj::Quot(_) => FailToVerifyObjWellDefinedResult::Quot(
            FailToVerifyQuotObjWellDefined(common),
        ),
        Obj::Gcd(_) => FailToVerifyObjWellDefinedResult::Gcd(
            FailToVerifyGcdObjWellDefined(common),
        ),
        Obj::Lcm(_) => FailToVerifyObjWellDefinedResult::Lcm(
            FailToVerifyLcmObjWellDefined(common),
        ),
        Obj::Floor(_) => FailToVerifyObjWellDefinedResult::Floor(
            FailToVerifyFloorObjWellDefined(common),
        ),
        Obj::Ceil(_) => FailToVerifyObjWellDefinedResult::Ceil(
            FailToVerifyCeilObjWellDefined(common),
        ),
        Obj::Min(_) => FailToVerifyObjWellDefinedResult::Min(
            FailToVerifyMinObjWellDefined(common),
        ),
        Obj::Max(_) => FailToVerifyObjWellDefinedResult::Max(
            FailToVerifyMaxObjWellDefined(common),
        ),
        Obj::Exp(_) => FailToVerifyObjWellDefinedResult::Exp(
            FailToVerifyExpObjWellDefined(common),
        ),
        Obj::Ln(_) => FailToVerifyObjWellDefinedResult::Ln(
            FailToVerifyLnObjWellDefined(common),
        ),
        Obj::Sign(_) => FailToVerifyObjWellDefinedResult::Sign(
            FailToVerifySignObjWellDefined(common),
        ),
        Obj::Factorial(_) => FailToVerifyObjWellDefinedResult::Factorial(
            FailToVerifyFactorialObjWellDefined(common),
        ),
        Obj::Pow(_) => FailToVerifyObjWellDefinedResult::Pow(
            FailToVerifyPowObjWellDefined(common),
        ),
        Obj::Abs(_) => FailToVerifyObjWellDefinedResult::Abs(
            FailToVerifyAbsObjWellDefined(common),
        ),
        Obj::Sin(_) => FailToVerifyObjWellDefinedResult::Sin(
            FailToVerifySinObjWellDefined(common),
        ),
        Obj::Arcsin(_) => FailToVerifyObjWellDefinedResult::Arcsin(
            FailToVerifyArcsinObjWellDefined(common),
        ),
        Obj::Cos(_) => FailToVerifyObjWellDefinedResult::Cos(
            FailToVerifyCosObjWellDefined(common),
        ),
        Obj::Tan(_) => FailToVerifyObjWellDefinedResult::Tan(
            FailToVerifyTanObjWellDefined(common),
        ),
        Obj::Cot(_) => FailToVerifyObjWellDefinedResult::Cot(
            FailToVerifyCotObjWellDefined(common),
        ),
        Obj::RealPart(_) => FailToVerifyObjWellDefinedResult::RealPart(
            FailToVerifyRealPartObjWellDefined(common),
        ),
        Obj::ImaginaryPart(_) => FailToVerifyObjWellDefinedResult::ImaginaryPart(
            FailToVerifyImaginaryPartObjWellDefined(common),
        ),
        Obj::ComplexAbs(_) => FailToVerifyObjWellDefinedResult::ComplexAbs(
            FailToVerifyComplexAbsObjWellDefined(common),
        ),
        Obj::Sqrt(_) => FailToVerifyObjWellDefinedResult::Sqrt(
            FailToVerifySqrtObjWellDefined(common),
        ),
        Obj::Log(_) => FailToVerifyObjWellDefinedResult::Log(
            FailToVerifyLogObjWellDefined(common),
        ),
        Obj::Union(_) => FailToVerifyObjWellDefinedResult::Union(
            FailToVerifyUnionObjWellDefined(common),
        ),
        Obj::Intersect(_) => FailToVerifyObjWellDefinedResult::Intersect(
            FailToVerifyIntersectObjWellDefined(common),
        ),
        Obj::SetMinus(_) => FailToVerifyObjWellDefinedResult::SetMinus(
            FailToVerifySetMinusObjWellDefined(common),
        ),
        Obj::BigUnion(_) => FailToVerifyObjWellDefinedResult::BigUnion(
            FailToVerifyBigUnionObjWellDefined(common),
        ),
        Obj::BigIntersect(_) => FailToVerifyObjWellDefinedResult::BigIntersect(
            FailToVerifyBigIntersectObjWellDefined(common),
        ),
        Obj::IndexUnion(_) => FailToVerifyObjWellDefinedResult::IndexUnion(
            FailToVerifyIndexUnionObjWellDefined(common),
        ),
        Obj::IndexIntersect(_) => FailToVerifyObjWellDefinedResult::IndexIntersect(
            FailToVerifyIndexIntersectObjWellDefined(common),
        ),
        Obj::PowerSet(_) => FailToVerifyObjWellDefinedResult::PowerSet(
            FailToVerifyPowerSetObjWellDefined(common),
        ),
        Obj::GeneralCart(_) => FailToVerifyObjWellDefinedResult::GeneralCart(
            FailToVerifyGeneralCartObjWellDefined(common),
        ),
        Obj::ListSet(_) => FailToVerifyObjWellDefinedResult::ListSet(
            FailToVerifyListSetObjWellDefined(common),
        ),
        Obj::SetBuilder(_) => FailToVerifyObjWellDefinedResult::SetBuilder(
            FailToVerifySetBuilderObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "SetBuilder well-definedness failed".to_string(),
            }),
        ),
        Obj::FnSet(_) => FailToVerifyObjWellDefinedResult::FnSet(
            FailToVerifyFnSetObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "FnSet well-definedness failed".to_string(),
            }),
        ),
        Obj::AnonymousFn(_) => FailToVerifyObjWellDefinedResult::AnonymousFn(
            FailToVerifyAnonymousFnObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "AnonymousFn well-definedness failed".to_string(),
            }),
        ),
        Obj::Cart(_) => FailToVerifyObjWellDefinedResult::Cart(
            FailToVerifyCartObjWellDefined(common),
        ),
        Obj::CartDim(_) => FailToVerifyObjWellDefinedResult::CartDim(
            FailToVerifyCartDimObjWellDefined(common),
        ),
        Obj::Proj(_) => FailToVerifyObjWellDefinedResult::Proj(
            FailToVerifyProjObjWellDefined(common),
        ),
        Obj::TupleDim(_) => FailToVerifyObjWellDefinedResult::TupleDim(
            FailToVerifyTupleDimObjWellDefined(common),
        ),
        Obj::Tuple(_) => FailToVerifyObjWellDefinedResult::Tuple(
            FailToVerifyTupleObjWellDefined(common),
        ),
        Obj::FiniteSetSize(_) => FailToVerifyObjWellDefinedResult::FiniteSetSize(
            FailToVerifyFiniteSetSizeObjWellDefined(common),
        ),
        Obj::FiniteSetMax(_) => FailToVerifyObjWellDefinedResult::FiniteSetMax(
            FailToVerifyFiniteSetMaxObjWellDefined(common),
        ),
        Obj::FiniteSetMin(_) => FailToVerifyObjWellDefinedResult::FiniteSetMin(
            FailToVerifyFiniteSetMinObjWellDefined(common),
        ),
        Obj::FnRange(_) => FailToVerifyObjWellDefinedResult::FnRange(
            FailToVerifyFnRangeObjWellDefined(common),
        ),
        Obj::Replacement(_) => FailToVerifyObjWellDefinedResult::Replacement(
            FailToVerifyReplacementObjWellDefined(common),
        ),
        Obj::Sum(_) => FailToVerifyObjWellDefinedResult::Sum(
            FailToVerifySumObjWellDefined(common),
        ),
        Obj::SumOfFiniteSet(_) => FailToVerifyObjWellDefinedResult::SumOfFiniteSet(
            FailToVerifySumOfFiniteSetObjWellDefined(common),
        ),
        Obj::Product(_) => FailToVerifyObjWellDefinedResult::Product(
            FailToVerifyProductObjWellDefined(common),
        ),
        Obj::ProductOfFiniteSet(_) => FailToVerifyObjWellDefinedResult::ProductOfFiniteSet(
            FailToVerifyProductOfFiniteSetObjWellDefined(common),
        ),
        Obj::Reduce(_) => FailToVerifyObjWellDefinedResult::Reduce(
            FailToVerifyReduceObjWellDefined(common),
        ),
        Obj::FiniteSetReduce(_) => FailToVerifyObjWellDefinedResult::FiniteSetReduce(
            FailToVerifyFiniteSetReduceObjWellDefined(common),
        ),
        Obj::Range(_) => FailToVerifyObjWellDefinedResult::Range(
            FailToVerifyRangeObjWellDefined(common),
        ),
        Obj::ClosedRange(_) => FailToVerifyObjWellDefinedResult::ClosedRange(
            FailToVerifyClosedRangeObjWellDefined(common),
        ),
        Obj::FiniteSeqSet(_) => FailToVerifyObjWellDefinedResult::FiniteSeqSet(
            FailToVerifyFiniteSeqSetObjWellDefined(common),
        ),
        Obj::SeqSet(_) => FailToVerifyObjWellDefinedResult::SeqSet(
            FailToVerifySeqSetObjWellDefined(common),
        ),
        Obj::FiniteSeqListObj(_) => FailToVerifyObjWellDefinedResult::FiniteSeqListObj(
            FailToVerifyFiniteSeqListObjObjWellDefined(common),
        ),
        Obj::ObjAtIndex(_) => FailToVerifyObjWellDefinedResult::ObjAtIndex(
            FailToVerifyObjAtIndexObjWellDefined(common),
        ),
        Obj::StandardSet(_) => FailToVerifyObjWellDefinedResult::StandardSet(
            FailToVerifyStandardSetObjWellDefined::Others(match common {
                FailToVerifyObjWellDefinedByDefCommon::Others(s) => s,
                _ => "StandardSet well-definedness failed".to_string(),
            }),
        ),
        Obj::StructObj(_) => FailToVerifyObjWellDefinedResult::StructObj(
            FailToVerifyStructObjObjWellDefined(common),
        ),
        Obj::ObjAsStructInstanceWithFieldAccess(_) => FailToVerifyObjWellDefinedResult::ObjAsStructInstanceWithFieldAccess(
            FailToVerifyObjAsStructInstanceWithFieldAccessObjWellDefined(common),
        ),
        Obj::InstantiatedTemplateObj(_) => FailToVerifyObjWellDefinedResult::InstantiatedTemplateObj(
            FailToVerifyInstantiatedTemplateObjObjWellDefined(common),
        ),
        Obj::OneSideInfinityIntervalObj(_) => FailToVerifyObjWellDefinedResult::OneSideInfinityIntervalObj(
            FailToVerifyOneSideInfinityIntervalObjObjWellDefined(common),
        ),
        Obj::IntervalObj(_) => FailToVerifyObjWellDefinedResult::IntervalObj(
            FailToVerifyIntervalObjObjWellDefined(common),
        ),
    }
}

