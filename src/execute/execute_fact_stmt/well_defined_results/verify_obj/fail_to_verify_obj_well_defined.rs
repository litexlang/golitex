// FailToVerifyObjWellDefinedResult mirrors Obj family nesting.
// Family sub-enums wrap existing per-leaf FailToVerify*ObjWellDefined structs.
// Non-leaf failures wrap the shared Child/Requirement/Others reason.

use super::entry::ObjWellDefinedProof;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::well_defined_result::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult,
};

pub enum FailToVerifyObjWellDefinedResult {
    Identifier(FailToVerifyIdentifierObjWellDefined),
    FnObj(FailToVerifyFnObjObjWellDefined),
    Literal(FailToVerifyLiteralObjWellDefinedResult),
    StandardSet(FailToVerifyStandardSetObjWellDefined),
    ArithmeticOperator(FailToVerifyArithmeticOperatorObjWellDefinedResult),
    IntegerOperator(FailToVerifyIntegerOperatorObjWellDefinedResult),
    TrigOperator(FailToVerifyTrigOperatorObjWellDefinedResult),
    ExpLogOperator(FailToVerifyExpLogOperatorObjWellDefinedResult),
    ComplexOperator(FailToVerifyComplexOperatorObjWellDefinedResult),
    SetOperator(FailToVerifySetOperatorObjWellDefinedResult),
    SetFormer(FailToVerifySetFormerObjWellDefinedResult),
    ProductShape(FailToVerifyProductShapeObjWellDefinedResult),
    FunctionSpace(FailToVerifyFunctionSpaceObjWellDefinedResult),
    IteratedOperator(FailToVerifyIteratedOperatorObjWellDefinedResult),
    FiniteSetStat(FailToVerifyFiniteSetStatObjWellDefinedResult),
    Structish(FailToVerifyStructishObjWellDefinedResult),
    InstantiatedTemplateObj(FailToVerifyInstantiatedTemplateObjObjWellDefined),
}

pub enum FailToVerifyLiteralObjWellDefinedResult {
    Number(FailToVerifyNumberObjWellDefined),
    ImaginaryUnit(FailToVerifyImaginaryUnitObjWellDefined),
    EulerNumber(FailToVerifyEulerNumberObjWellDefined),
    Pi(FailToVerifyPiObjWellDefined),
}

pub enum FailToVerifyArithmeticOperatorObjWellDefinedResult {
    Add(FailToVerifyAddObjWellDefined),
    Sub(FailToVerifySubObjWellDefined),
    Neg(FailToVerifyNegObjWellDefined),
    Mul(FailToVerifyMulObjWellDefined),
    Div(FailToVerifyDivObjWellDefined),
    Pow(FailToVerifyPowObjWellDefined),
    Abs(FailToVerifyAbsObjWellDefined),
    Min(FailToVerifyMinObjWellDefined),
    Max(FailToVerifyMaxObjWellDefined),
    Floor(FailToVerifyFloorObjWellDefined),
    Ceil(FailToVerifyCeilObjWellDefined),
    Sign(FailToVerifySignObjWellDefined),
}

pub enum FailToVerifyIntegerOperatorObjWellDefinedResult {
    Mod(FailToVerifyModObjWellDefined),
    Quot(FailToVerifyQuotObjWellDefined),
    Gcd(FailToVerifyGcdObjWellDefined),
    Lcm(FailToVerifyLcmObjWellDefined),
    Factorial(FailToVerifyFactorialObjWellDefined),
}

pub enum FailToVerifyTrigOperatorObjWellDefinedResult {
    Sin(FailToVerifySinObjWellDefined),
    Cos(FailToVerifyCosObjWellDefined),
    Tan(FailToVerifyTanObjWellDefined),
    Cot(FailToVerifyCotObjWellDefined),
    Arcsin(FailToVerifyArcsinObjWellDefined),
    Arccos(FailToVerifyArccosObjWellDefined),
    Arctan(FailToVerifyArctanObjWellDefined),
    Arccot(FailToVerifyArccotObjWellDefined),
}

pub enum FailToVerifyExpLogOperatorObjWellDefinedResult {
    Exp(FailToVerifyExpObjWellDefined),
    Ln(FailToVerifyLnObjWellDefined),
    Log(FailToVerifyLogObjWellDefined),
    Sqrt(FailToVerifySqrtObjWellDefined),
}

pub enum FailToVerifyComplexOperatorObjWellDefinedResult {
    RealPart(FailToVerifyRealPartObjWellDefined),
    ImaginaryPart(FailToVerifyImaginaryPartObjWellDefined),
    ComplexAbs(FailToVerifyComplexAbsObjWellDefined),
}

pub enum FailToVerifySetOperatorObjWellDefinedResult {
    Union(FailToVerifyUnionObjWellDefined),
    Intersect(FailToVerifyIntersectObjWellDefined),
    SetMinus(FailToVerifySetMinusObjWellDefined),
    FamilyUnion(FailToVerifyFamilyUnionObjWellDefined),
    FamilyIntersect(FailToVerifyFamilyIntersectObjWellDefined),
    IndexUnion(FailToVerifyIndexUnionObjWellDefined),
    IndexIntersect(FailToVerifyIndexIntersectObjWellDefined),
    PowerSet(FailToVerifyPowerSetObjWellDefined),
    IndexCart(FailToVerifyIndexCartObjWellDefined),
}

pub enum FailToVerifySetFormerObjWellDefinedResult {
    ListSet(FailToVerifyListSetObjWellDefined),
    SetBuilder(FailToVerifySetBuilderObjWellDefined),
    Range(FailToVerifyRangeObjWellDefined),
    ClosedRange(FailToVerifyClosedRangeObjWellDefined),
    FiniteSeqSet(FailToVerifyFiniteSeqSetObjWellDefined),
    SeqSet(FailToVerifySeqSetObjWellDefined),
    OneSideInfinityIntervalObj(FailToVerifyOneSideInfinityIntervalObjObjWellDefined),
    IntervalObj(FailToVerifyIntervalObjObjWellDefined),
}

pub enum FailToVerifyProductShapeObjWellDefinedResult {
    Cart(FailToVerifyCartObjWellDefined),
    Tuple(FailToVerifyTupleObjWellDefined),




}

pub enum FailToVerifyFunctionSpaceObjWellDefinedResult {
    FnSet(FailToVerifyFnSetObjWellDefined),
    AnonymousFn(FailToVerifyAnonymousFnObjWellDefined),
    FnRange(FailToVerifyFnRangeObjWellDefined),
    Preimage(FailToVerifyPreimageObjWellDefined),
    PreimageSet(FailToVerifyPreimageSetObjWellDefined),
}

pub enum FailToVerifyIteratedOperatorObjWellDefinedResult {
    Sum(FailToVerifySumObjWellDefined),
    SumOfFiniteSet(FailToVerifySumOfFiniteSetObjWellDefined),
    Product(FailToVerifyProductObjWellDefined),
    ProductOfFiniteSet(FailToVerifyProductOfFiniteSetObjWellDefined),
    Reduce(FailToVerifyReduceObjWellDefined),
    FiniteSetReduce(FailToVerifyFiniteSetReduceObjWellDefined),
}

pub enum FailToVerifyFiniteSetStatObjWellDefinedResult {
    FiniteSetSize(FailToVerifyFiniteSetSizeObjWellDefined),
    FiniteSetMax(FailToVerifyFiniteSetMaxObjWellDefined),
    FiniteSetMin(FailToVerifyFiniteSetMinObjWellDefined),
}

pub enum FailToVerifyStructishObjWellDefinedResult {
    StructObj(FailToVerifyStructObjObjWellDefined),
    FieldAccess(FailToVerifyFieldAccessObjWellDefined),
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

pub struct FailToVerifyNegObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

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

pub struct FailToVerifyArccosObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyArctanObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyArccotObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

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

pub struct FailToVerifyFamilyUnionObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFamilyIntersectObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifyIndexUnionObjWellDefined {
    NotInFunctionSet,
    Domain(FailToVerifyObjWellDefinedByDefCommon),
}

pub enum FailToVerifyIndexIntersectObjWellDefined {
    NotInFunctionSet,
    Domain(FailToVerifyObjWellDefinedByDefCommon),
}

pub struct FailToVerifyPowerSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifyIndexCartObjWellDefined {
    NotInFunctionSet,
    Domain(FailToVerifyObjWellDefinedByDefCommon),
}

pub struct FailToVerifyListSetObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifySetBuilderObjWellDefined {
    ParamSet {
        obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    Fact {
        failed_index: usize,
        param_set_well_defined: Box<ObjWellDefinedProof>,
        succeeded: Vec<FactWellDefinedProof>,
        failed: Box<FailToVerifyFactWellDefinedResult>,
    },
    Others(String),
}

pub enum FailToVerifyFnSetObjWellDefined {
    // Obj carrier cites an earlier binder, e.g. `fn(x R, y S(x))`.
    // Forbidden here: function domains must be fixed sets. Allowed elsewhere:
    // `forall S set, x S` (kind telescope on TypedParameterList, not FnSet).
    ParamTypeCitesEarlierBinder {
        failed_index: usize,
    },
    ParamType {
        failed_index: usize,
        succeeded: Vec<Box<ObjWellDefinedProof>>,
        failed_obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    DomFact {
        failed_index: usize,
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    RetSet {
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        failed_obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    Others(String),
}

pub enum FailToVerifyAnonymousFnObjWellDefined {
    // Same closed-carrier rule as FnSet (not the forall kind-telescope rule).
    ParamTypeCitesEarlierBinder {
        failed_index: usize,
    },
    ParamType {
        failed_index: usize,
        succeeded: Vec<Box<ObjWellDefinedProof>>,
        failed_obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    DomFact {
        failed_index: usize,
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        succeeded_dom: Vec<FactWellDefinedProof>,
        failed_dom: Box<FailToVerifyFactWellDefinedResult>,
    },
    RetSet {
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        failed_obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    Body {
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        ret_set_well_defined: Box<ObjWellDefinedProof>,
        failed_obj: Obj,
        failed: Box<FailToVerifyObjWellDefinedResult>,
    },
    BodyInRetSet {
        param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
        dom_fact_well_defined: Vec<FactWellDefinedProof>,
        ret_set_well_defined: Box<ObjWellDefinedProof>,
        body_well_defined: Box<ObjWellDefinedProof>,
        failed: VerifyFactResult,
    },
    Others(String),
}

pub struct FailToVerifyCartObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);


pub struct FailToVerifyTupleObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetSizeObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetMaxObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFiniteSetMinObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub enum FailToVerifyFnRangeObjWellDefined {
    // Function argument has no visible InFunctionSet registration.
    NotInFunctionSet,
    Domain(FailToVerifyObjWellDefinedByDefCommon),
}


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


pub enum FailToVerifyStandardSetObjWellDefined {
    Others(String),
}

pub struct FailToVerifyStructObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyFieldAccessObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyInstantiatedTemplateObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyOneSideInfinityIntervalObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);

pub struct FailToVerifyIntervalObjObjWellDefined(pub FailToVerifyObjWellDefinedByDefCommon);



pub enum FailToVerifyPreimageObjWellDefined {
    Domain(FailToVerifyObjWellDefinedByDefCommon),
    Construction(crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionFailure),
}

pub enum FailToVerifyPreimageSetObjWellDefined {
    Domain(FailToVerifyObjWellDefinedByDefCommon),
    Construction(crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionFailure),
}
