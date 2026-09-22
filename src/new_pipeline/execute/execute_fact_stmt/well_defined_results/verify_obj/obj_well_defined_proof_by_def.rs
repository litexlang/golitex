// ObjWellDefinedProofByDef mirrors Obj family nesting.
// Family sub-enums wrap the existing per-leaf proof structs.
// Transition: non-leaf proofs share CommonStages fields; specialize later per family.

use super::entry::ObjWellDefinedProof;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::new_pipeline::ast::obj::{FnSet, Obj};
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::well_defined_result::FactWellDefinedProof;
use crate::new_pipeline::runtime::FactId;

pub enum ObjWellDefinedProofByDef {
    Identifier(IdentifierObjWellDefinedProof),
    FnObj(FnObjObjWellDefinedProof),
    Literal(LiteralObjWellDefinedProofByDef),
    StandardSet(StandardSetObjWellDefinedProof),
    ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef),
    IntegerOperator(IntegerOperatorObjWellDefinedProofByDef),
    TrigOperator(TrigOperatorObjWellDefinedProofByDef),
    ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef),
    ComplexOperator(ComplexOperatorObjWellDefinedProofByDef),
    SetOperator(SetOperatorObjWellDefinedProofByDef),
    SetFormer(SetFormerObjWellDefinedProofByDef),
    ProductShape(ProductShapeObjWellDefinedProofByDef),
    FunctionSpace(FunctionSpaceObjWellDefinedProofByDef),
    IteratedOperator(IteratedOperatorObjWellDefinedProofByDef),
    FiniteSetStat(FiniteSetStatObjWellDefinedProofByDef),
    Structish(StructishObjWellDefinedProofByDef),
    InstantiatedTemplateObj(InstantiatedTemplateObjObjWellDefinedProof),
}

pub enum LiteralObjWellDefinedProofByDef {
    Number(NumberObjWellDefinedProof),
    ImaginaryUnit(ImaginaryUnitObjWellDefinedProof),
    EulerNumber(EulerNumberObjWellDefinedProof),
    Pi(PiObjWellDefinedProof),
}

pub enum ArithmeticOperatorObjWellDefinedProofByDef {
    Add(AddObjWellDefinedProof),
    Sub(SubObjWellDefinedProof),
    Mul(MulObjWellDefinedProof),
    Div(DivObjWellDefinedProof),
    Pow(PowObjWellDefinedProof),
    Abs(AbsObjWellDefinedProof),
    Min(MinObjWellDefinedProof),
    Max(MaxObjWellDefinedProof),
    Floor(FloorObjWellDefinedProof),
    Ceil(CeilObjWellDefinedProof),
    Sign(SignObjWellDefinedProof),
}

pub enum IntegerOperatorObjWellDefinedProofByDef {
    Mod(ModObjWellDefinedProof),
    Quot(QuotObjWellDefinedProof),
    Gcd(GcdObjWellDefinedProof),
    Lcm(LcmObjWellDefinedProof),
    Factorial(FactorialObjWellDefinedProof),
}

pub enum TrigOperatorObjWellDefinedProofByDef {
    Sin(SinObjWellDefinedProof),
    Cos(CosObjWellDefinedProof),
    Tan(TanObjWellDefinedProof),
    Cot(CotObjWellDefinedProof),
    Arcsin(ArcsinObjWellDefinedProof),
    Arccos(ArccosObjWellDefinedProof),
    Arctan(ArctanObjWellDefinedProof),
    Arccot(ArccotObjWellDefinedProof),
}

pub enum ExpLogOperatorObjWellDefinedProofByDef {
    Exp(ExpObjWellDefinedProof),
    Ln(LnObjWellDefinedProof),
    Log(LogObjWellDefinedProof),
    Sqrt(SqrtObjWellDefinedProof),
}

pub enum ComplexOperatorObjWellDefinedProofByDef {
    RealPart(RealPartObjWellDefinedProof),
    ImaginaryPart(ImaginaryPartObjWellDefinedProof),
    ComplexAbs(ComplexAbsObjWellDefinedProof),
}

pub enum SetOperatorObjWellDefinedProofByDef {
    Union(UnionObjWellDefinedProof),
    Intersect(IntersectObjWellDefinedProof),
    SetMinus(SetMinusObjWellDefinedProof),
    FamilyUnion(FamilyUnionObjWellDefinedProof),
    FamilyIntersect(FamilyIntersectObjWellDefinedProof),
    IndexUnion(IndexUnionObjWellDefinedProof),
    IndexIntersect(IndexIntersectObjWellDefinedProof),
    PowerSet(PowerSetObjWellDefinedProof),
    IndexCart(IndexCartObjWellDefinedProof),
}

pub enum SetFormerObjWellDefinedProofByDef {
    ListSet(ListSetObjWellDefinedProof),
    SetBuilder(SetBuilderObjWellDefinedProof),
    Range(RangeObjWellDefinedProof),
    ClosedRange(ClosedRangeObjWellDefinedProof),
    FiniteSeqSet(FiniteSeqSetObjWellDefinedProof),
    SeqSet(SeqSetObjWellDefinedProof),
    OneSideInfinityIntervalObj(OneSideInfinityIntervalObjObjWellDefinedProof),
    IntervalObj(IntervalObjObjWellDefinedProof),
}

pub enum ProductShapeObjWellDefinedProofByDef {
    Cart(CartObjWellDefinedProof),
    Tuple(TupleObjWellDefinedProof),
    CartDim(CartDimObjWellDefinedProof),
    TupleDim(TupleDimObjWellDefinedProof),
    Proj(ProjObjWellDefinedProof),
    ObjAtIndex(ObjAtIndexObjWellDefinedProof),
}

pub enum FunctionSpaceObjWellDefinedProofByDef {
    FnSet(FnSetObjWellDefinedProof),
    AnonymousFn(AnonymousFnObjWellDefinedProof),
    FnRange(FnRangeObjWellDefinedProof),
}

pub enum IteratedOperatorObjWellDefinedProofByDef {
    Sum(SumObjWellDefinedProof),
    SumOfFiniteSet(SumOfFiniteSetObjWellDefinedProof),
    Product(ProductObjWellDefinedProof),
    ProductOfFiniteSet(ProductOfFiniteSetObjWellDefinedProof),
    Reduce(ReduceObjWellDefinedProof),
    FiniteSetReduce(FiniteSetReduceObjWellDefinedProof),
}

pub enum FiniteSetStatObjWellDefinedProofByDef {
    FiniteSetSize(FiniteSetSizeObjWellDefinedProof),
    FiniteSetMax(FiniteSetMaxObjWellDefinedProof),
    FiniteSetMin(FiniteSetMinObjWellDefinedProof),
}

pub enum StructishObjWellDefinedProofByDef {
    StructObj(StructObjObjWellDefinedProof),
    FieldAccess(FieldAccessObjWellDefinedProof),
}
pub struct IdentifierObjWellDefinedProof {}

impl IdentifierObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

// Which FnSet supplied the domain check for a successful FnObj application.
// Identifier / template heads cite an InFunctionSet store; anonymous literals
// carry their own `body` FnSet and have no registration FactId.
pub enum FnObjDomainFnSetEvidence {
    InFunctionSet {
        fn_set: FnSet,
        fact_id: FactId,
    },
    AnonymousLiteral {
        fn_set: FnSet,
    },
}

pub struct FnObjObjWellDefinedProof {
    // Domain-check space for this application (see FnObjDomainFnSetEvidence).
    // None only on incomplete/from_stages packing, not on a successful literal apply.
    pub domain_fn_set: Option<FnObjDomainFnSetEvidence>,
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FnObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            domain_fn_set: None,
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct NumberObjWellDefinedProof {}

impl NumberObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

pub struct ImaginaryUnitObjWellDefinedProof {}

impl ImaginaryUnitObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

pub struct EulerNumberObjWellDefinedProof {}

impl EulerNumberObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

pub struct PiObjWellDefinedProof {}

impl PiObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

pub struct AddObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl AddObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SubObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SubObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct MulObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MulObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct DivObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl DivObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ModObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ModObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct QuotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl QuotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct GcdObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl GcdObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct LcmObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LcmObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FloorObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FloorObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct CeilObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CeilObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct MinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct MaxObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MaxObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ExpObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ExpObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct LnObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LnObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SignObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SignObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FactorialObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FactorialObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct PowObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl PowObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct AbsObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl AbsObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ArcsinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArcsinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ArccosObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArccosObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ArctanObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArctanObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ArccotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArccotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct CosObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CosObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct TanObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl TanObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct CotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct RealPartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl RealPartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ImaginaryPartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ImaginaryPartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ComplexAbsObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ComplexAbsObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SqrtObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SqrtObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct LogObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LogObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct UnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl UnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct IntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SetMinusObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SetMinusObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FamilyUnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FamilyUnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FamilyIntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FamilyIntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct IndexUnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexUnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct IndexIntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexIntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct PowerSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl PowerSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct IndexCartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexCartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ListSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ListSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SetBuilderObjWellDefinedProof {
    pub param_set_well_defined: Box<ObjWellDefinedProof>,
    pub fact_well_defined: Vec<FactWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub struct FnSetObjWellDefinedProof {
    pub param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
    pub dom_fact_well_defined: Vec<FactWellDefinedProof>,
    pub ret_set_well_defined: Box<ObjWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub struct AnonymousFnObjWellDefinedProof {
    pub param_type_well_defined: Vec<(Obj, Box<ObjWellDefinedProof>)>,
    pub dom_fact_well_defined: Vec<FactWellDefinedProof>,
    pub ret_set_well_defined: Box<ObjWellDefinedProof>,
    pub body_well_defined: Box<ObjWellDefinedProof>,
    pub body_in_ret_set: Option<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub struct CartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

// cart_dim(S): set WD, then `$is_cart(S)`.
pub struct CartDimObjWellDefinedProof {
    pub set_well_defined: Box<ObjWellDefinedProof>,
    pub set_is_cart: VerifyFactResult,
}

// proj(S, i): set/dim WD, then `i $in N+`, `$is_cart(S)`, `i <= cart_dim(S)`.
pub struct ProjObjWellDefinedProof {
    pub set_well_defined: Box<ObjWellDefinedProof>,
    pub dim_well_defined: Box<ObjWellDefinedProof>,
    pub dim_in_npos: VerifyFactResult,
    pub set_is_cart: VerifyFactResult,
    pub dim_le_cart_dim: VerifyFactResult,
}

// tuple_dim(t): arg WD, then `$is_tuple(t)`.
pub struct TupleDimObjWellDefinedProof {
    pub arg_well_defined: Box<ObjWellDefinedProof>,
    pub arg_is_tuple: VerifyFactResult,
}

pub struct TupleObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl TupleObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FiniteSetSizeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetSizeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FiniteSetMaxObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetMaxObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FiniteSetMinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetMinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FnRangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FnRangeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SumObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SumObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SumOfFiniteSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SumOfFiniteSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ProductObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ProductObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ProductOfFiniteSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ProductOfFiniteSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ReduceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ReduceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FiniteSetReduceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetReduceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct RangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl RangeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct ClosedRangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ClosedRangeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FiniteSeqSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSeqSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct SeqSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SeqSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

// t[i]: obj/index WD, then `i $in N+`, `$is_tuple(t)`, `i <= tuple_dim(t)`.
pub struct ObjAtIndexObjWellDefinedProof {
    pub obj_well_defined: Box<ObjWellDefinedProof>,
    pub index_well_defined: Box<ObjWellDefinedProof>,
    pub index_in_npos: VerifyFactResult,
    pub obj_is_tuple: VerifyFactResult,
    pub index_le_tuple_dim: VerifyFactResult,
}

pub struct StandardSetObjWellDefinedProof {}

impl StandardSetObjWellDefinedProof {
    pub fn new() -> Self { Self {} }
}

pub struct StructObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl StructObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct FieldAccessObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FieldAccessObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct InstantiatedTemplateObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl InstantiatedTemplateObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct OneSideInfinityIntervalObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl OneSideInfinityIntervalObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

pub struct IntervalObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<(Obj, VerifyObjWellDefinedResult)>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IntervalObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        Self {
            child_obj_well_defined: stages.child_obj_well_defined,
            requirement_fact_verified: stages.requirement_fact_verified,
        }
    }
}

