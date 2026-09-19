// FailToVerifyObjWellDefinedResult mirrors Obj.
// Non-leaf failures wrap the shared Child/Requirement/Others reason.

use super::entry::ObjWellDefinedProof;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult,
};

pub enum FailToVerifyObjWellDefinedResult {
    Identifier(FailToVerifyIdentifierObjWellDefined),
    FnObj(FailToVerifyFnObjObjWellDefined),
    Number(FailToVerifyNumberObjWellDefined),
    ImaginaryUnit(FailToVerifyImaginaryUnitObjWellDefined),
    EulerNumber(FailToVerifyEulerNumberObjWellDefined),
    Pi(FailToVerifyPiObjWellDefined),
    Add(FailToVerifyAddObjWellDefined),
    Sub(FailToVerifySubObjWellDefined),
    Mul(FailToVerifyMulObjWellDefined),
    Div(FailToVerifyDivObjWellDefined),
    Mod(FailToVerifyModObjWellDefined),
    Quot(FailToVerifyQuotObjWellDefined),
    Gcd(FailToVerifyGcdObjWellDefined),
    Lcm(FailToVerifyLcmObjWellDefined),
    Floor(FailToVerifyFloorObjWellDefined),
    Ceil(FailToVerifyCeilObjWellDefined),
    Min(FailToVerifyMinObjWellDefined),
    Max(FailToVerifyMaxObjWellDefined),
    Exp(FailToVerifyExpObjWellDefined),
    Ln(FailToVerifyLnObjWellDefined),
    Sign(FailToVerifySignObjWellDefined),
    Factorial(FailToVerifyFactorialObjWellDefined),
    Pow(FailToVerifyPowObjWellDefined),
    Abs(FailToVerifyAbsObjWellDefined),
    Sin(FailToVerifySinObjWellDefined),
    Arcsin(FailToVerifyArcsinObjWellDefined),
    Cos(FailToVerifyCosObjWellDefined),
    Tan(FailToVerifyTanObjWellDefined),
    Cot(FailToVerifyCotObjWellDefined),
    RealPart(FailToVerifyRealPartObjWellDefined),
    ImaginaryPart(FailToVerifyImaginaryPartObjWellDefined),
    ComplexAbs(FailToVerifyComplexAbsObjWellDefined),
    Sqrt(FailToVerifySqrtObjWellDefined),
    Log(FailToVerifyLogObjWellDefined),
    Union(FailToVerifyUnionObjWellDefined),
    Intersect(FailToVerifyIntersectObjWellDefined),
    SetMinus(FailToVerifySetMinusObjWellDefined),
    BigUnion(FailToVerifyBigUnionObjWellDefined),
    BigIntersect(FailToVerifyBigIntersectObjWellDefined),
    IndexUnion(FailToVerifyIndexUnionObjWellDefined),
    IndexIntersect(FailToVerifyIndexIntersectObjWellDefined),
    PowerSet(FailToVerifyPowerSetObjWellDefined),
    GeneralCart(FailToVerifyGeneralCartObjWellDefined),
    ListSet(FailToVerifyListSetObjWellDefined),
    SetBuilder(FailToVerifySetBuilderObjWellDefined),
    FnSet(FailToVerifyFnSetObjWellDefined),
    AnonymousFn(FailToVerifyAnonymousFnObjWellDefined),
    Cart(FailToVerifyCartObjWellDefined),
    CartDim(FailToVerifyCartDimObjWellDefined),
    Proj(FailToVerifyProjObjWellDefined),
    TupleDim(FailToVerifyTupleDimObjWellDefined),
    Tuple(FailToVerifyTupleObjWellDefined),
    FiniteSetSize(FailToVerifyFiniteSetSizeObjWellDefined),
    FiniteSetMax(FailToVerifyFiniteSetMaxObjWellDefined),
    FiniteSetMin(FailToVerifyFiniteSetMinObjWellDefined),
    FnRange(FailToVerifyFnRangeObjWellDefined),
    Replacement(FailToVerifyReplacementObjWellDefined),
    Sum(FailToVerifySumObjWellDefined),
    SumOfFiniteSet(FailToVerifySumOfFiniteSetObjWellDefined),
    Product(FailToVerifyProductObjWellDefined),
    ProductOfFiniteSet(FailToVerifyProductOfFiniteSetObjWellDefined),
    Reduce(FailToVerifyReduceObjWellDefined),
    FiniteSetReduce(FailToVerifyFiniteSetReduceObjWellDefined),
    Range(FailToVerifyRangeObjWellDefined),
    ClosedRange(FailToVerifyClosedRangeObjWellDefined),
    FiniteSeqSet(FailToVerifyFiniteSeqSetObjWellDefined),
    SeqSet(FailToVerifySeqSetObjWellDefined),
    FiniteSeqListObj(FailToVerifyFiniteSeqListObjObjWellDefined),
    ObjAtIndex(FailToVerifyObjAtIndexObjWellDefined),
    StandardSet(FailToVerifyStandardSetObjWellDefined),
    StructObj(FailToVerifyStructObjObjWellDefined),
    ObjAsStructInstanceWithFieldAccess(FailToVerifyObjAsStructInstanceWithFieldAccessObjWellDefined),
    InstantiatedTemplateObj(FailToVerifyInstantiatedTemplateObjObjWellDefined),
    OneSideInfinityIntervalObj(FailToVerifyOneSideInfinityIntervalObjObjWellDefined),
    IntervalObj(FailToVerifyIntervalObjObjWellDefined),
}

pub enum FailToVerifyObjWellDefinedByDefCommon {
    Child {
        obj: Obj,
        child: Box<FailToVerifyObjWellDefinedResult>,
    },
    Requirement {
        obj: Obj,
        result: VerifyFactResult,
    },
    Others(String),
}

pub enum FailToVerifyIdentifierObjWellDefined {
    Undefined { obj: Obj },
    Others(String),
}

// Catch-all soft fail when no Obj subject is available to mirror.
pub fn fail_to_verify_obj_well_defined_others(message: String) -> FailToVerifyObjWellDefinedResult {
    FailToVerifyObjWellDefinedResult::Identifier(FailToVerifyIdentifierObjWellDefined::Others(
        message,
    ))
}

pub enum FailToVerifyFnObjObjWellDefined {
    // No InFunctionSet (or equality-neighbor) candidate for the applied head.
    NotInFunctionSet,
    Domain(FailToVerifyObjWellDefinedByDefCommon),
}

pub enum FailToVerifyNumberObjWellDefined {
    Others(String),
}

pub enum FailToVerifyImaginaryUnitObjWellDefined {
    Others(String),
}

pub enum FailToVerifyEulerNumberObjWellDefined {
    Others(String),
}

pub enum FailToVerifyPiObjWellDefined {
    Others(String),
}

pub struct FailToVerifyAddObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySubObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyMulObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyDivObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyModObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyQuotObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyGcdObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyLcmObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFloorObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyCeilObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyMinObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyMaxObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyExpObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyLnObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySignObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFactorialObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyPowObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyAbsObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySinObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyArcsinObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyCosObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyTanObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyCotObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyRealPartObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyImaginaryPartObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyComplexAbsObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySqrtObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyLogObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyUnionObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyIntersectObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySetMinusObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyBigUnionObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyBigIntersectObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyIndexUnionObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyIndexIntersectObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyPowerSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyGeneralCartObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyListSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifySetBuilderObjWellDefined {
    ParamSet(Box<FailToVerifyObjWellDefinedResult>),
    Fact {
        failed_index: usize,
        param_set_well_defined: Box<ObjWellDefinedProof>,
        succeeded: Vec<FactWellDefinedProof>,
        failed: Box<FailToVerifyFactWellDefinedResult>,
    },
    Others(String),
}

pub enum FailToVerifyFnSetObjWellDefined {
    ParamType {
        failed_index: usize,
        succeeded: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    DomFact {
        failed_index: usize,
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    RetSet {
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    Others(String),
}

pub enum FailToVerifyAnonymousFnObjWellDefined {
    ParamType {
        failed_index: usize,
        succeeded: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    DomFact {
        failed_index: usize,
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    RetSet {
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    Body {
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        ret_set_well_defined: Box<ObjWellDefinedProof>,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    BodyInRetSet {
        param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        ret_set_well_defined: Box<ObjWellDefinedProof>,
        body_well_defined: Box<ObjWellDefinedProof>,
        failed: VerifyFactResult,
    },
    Others(String),
}

pub struct FailToVerifyCartObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyCartDimObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyProjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyTupleDimObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyTupleObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetSizeObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetMaxObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetMinObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFnRangeObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyReplacementObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySumObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySumOfFiniteSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyProductObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyProductOfFiniteSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyReduceObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetReduceObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyRangeObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyClosedRangeObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSeqSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifySeqSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSeqListObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyObjAtIndexObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifyStandardSetObjWellDefined {
    Others(String),
}

pub struct FailToVerifyStructObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyObjAsStructInstanceWithFieldAccessObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyInstantiatedTemplateObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyOneSideInfinityIntervalObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyIntervalObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

