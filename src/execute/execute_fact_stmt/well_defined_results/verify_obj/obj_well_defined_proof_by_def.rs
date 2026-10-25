use super::fn_obj_domain_check_result::FnObjArgumentScope;
// ObjWellDefinedProofByDef mirrors Obj family nesting.
// Family sub-enums wrap the existing per-leaf proof structs.
// Transition: non-leaf proofs share CommonStages fields; specialize later per family.

use super::entry::ObjWellDefinedProof;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::obj::FnSet;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::prelude::*;
use crate::runtime::FactId;

pub enum ObjWellDefinedProofByDef {
    MatrixOperator(MatrixOperatorObjWellDefinedProofByDef),
    IntegralOperator(
        crate::execute::execute_fact_stmt::riemann_integral::IntegralOperatorWellDefinedProof,
    ),
    DerivativeOperator(
        crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof,
    ),
    BoundOperator(BoundOperatorObjWellDefinedProofByDef),
    LimitOperator(LimitOperatorObjWellDefinedProofByDef),
    Identifier(IdentifierObjWellDefinedProof),
    FnObj(FnObjObjWellDefinedProof),
    Literal(LiteralObjWellDefinedProofByDef),
    StandardSet(StandardSetObjWellDefinedProof),
    ArithmeticOperator(ArithmeticOperatorObjWellDefinedProofByDef),
    IntegerOperator(IntegerOperatorObjWellDefinedProofByDef),
    TrigOperator(TrigOperatorObjWellDefinedProofByDef),
    HyperbolicOperator(HyperbolicOperatorObjWellDefinedProofByDef),
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

pub enum BoundOperatorObjWellDefinedProofByDef {
    Supremum(SupremumObjWellDefinedProof),
    Infimum(InfimumObjWellDefinedProof),
}
pub struct SupremumObjWellDefinedProof {
    pub set_wd: Box<ObjWellDefinedProof>,
    pub real_set: Box<VerifyFactResult>,
    pub selection: Box<VerifyFactResult>,
}
pub struct InfimumObjWellDefinedProof {
    pub set_wd: Box<ObjWellDefinedProof>,
    pub real_set: Box<VerifyFactResult>,
    pub selection: Box<VerifyFactResult>,
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
    Neg(NegObjWellDefinedProof),
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
    Csc(CscObjWellDefinedProof),
    Sec(SecObjWellDefinedProof),
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
    Conjugate(ConjugateObjWellDefinedProof),
    RealPart(RealPartObjWellDefinedProof),
    ImaginaryPart(ImaginaryPartObjWellDefinedProof),
    ComplexAbs(ComplexAbsObjWellDefinedProof),
}

pub enum SetOperatorObjWellDefinedProofByDef {
    SymmetricDifference(SymmetricDifferenceObjWellDefinedProof),
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
    MatrixSet(MatrixSetObjWellDefinedProof),
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
}

pub enum FunctionSpaceObjWellDefinedProofByDef {
    FnSet(FnSetObjWellDefinedProof),
    AnonymousFn(AnonymousFnObjWellDefinedProof),
    FnRange(FnRangeObjWellDefinedProof),
    Composition(CompositionObjWellDefinedProof),
    Preimage(PreimageObjWellDefinedProof),
    PreimageSet(PreimageSetObjWellDefinedProof),
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
    pub fn new() -> Self {
        Self {}
    }
}

// Which FnSet supplied the domain check for a successful FnObj application.
// Identifiers cite a source fact and head equality. Anonymous literals carry
// their own body. Templates may read a checked declaration after instance WD,
// including nested checks where signature caching is disabled.
pub enum FnObjDomainFnSetEvidence {
    MultivariableSelector(
        Box<crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof>,
    ),
    Matrix(Box<crate::execute::execute_fact_stmt::native_matrix::MatrixCallableProof>),
    FiniteFunction(
        Box<crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof>,
    ),
    InFunctionSet {
        fn_set: FnSet,
        fact_id: FactId,
        function_equal: KnownEqualityPathProof,
    },
    Composition(Box<CompositionCallableProof>),
    AnonymousLiteral {
        fn_set: FnSet,
    },
    TemplateDefinition {
        fn_set: FnSet,
        function_equal: KnownEqualityPathProof,
    },
}

pub struct FnObjObjWellDefinedProof {
    // Domain-check space for this application (see FnObjDomainFnSetEvidence).
    // None only on incomplete/from_stages packing, not on a successful literal apply.
    pub domain_fn_set: Option<FnObjDomainFnSetEvidence>,
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub argument_scope: Option<FnObjArgumentScope>,
}

impl FnObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            argument_scope: None,
            domain_fn_set: None,
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct NumberObjWellDefinedProof {}

impl NumberObjWellDefinedProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct ImaginaryUnitObjWellDefinedProof {}

impl ImaginaryUnitObjWellDefinedProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct EulerNumberObjWellDefinedProof {}

impl EulerNumberObjWellDefinedProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct PiObjWellDefinedProof {}

impl PiObjWellDefinedProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct AddObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl AddObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SubObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SubObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct NegObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl NegObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MulObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MulObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct DivObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl DivObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ModObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ModObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct QuotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl QuotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct GcdObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl GcdObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct LcmObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LcmObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FloorObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FloorObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CeilObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CeilObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MaxObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl MaxObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ExpObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ExpObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct LnObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LnObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SignObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SignObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FactorialObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FactorialObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct PowObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl PowObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct AbsObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl AbsObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ArcsinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArcsinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ArccosObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArccosObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ArctanObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArctanObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ArccotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ArccotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CosObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CosObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct TanObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl TanObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CotObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CotObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct RealPartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl RealPartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ImaginaryPartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ImaginaryPartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ComplexAbsObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ComplexAbsObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SqrtObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SqrtObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct LogObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl LogObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct UnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl UnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SetMinusObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SetMinusObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FamilyUnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FamilyUnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FamilyIntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FamilyIntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IndexUnionObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexUnionObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IndexIntersectObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexIntersectObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct PowerSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl PowerSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IndexCartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IndexCartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ListSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ListSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SetBuilderObjWellDefinedProof {
    pub param_set_well_defined: Box<ObjWellDefinedProof>,
    pub defined_params: StoreHaveObjAndInferResult,
    pub assumed_facts: Vec<AssumeDomFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub struct FnSetObjWellDefinedProof {
    pub param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub defined_params: StoreHaveObjAndInferResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub ret_set_well_defined: Box<ObjWellDefinedProof>,
    pub local_env: Box<ExecEnv>,
}

pub struct AnonymousFnObjWellDefinedProof {
    pub param_type_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub defined_params: StoreHaveObjAndInferResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub ret_set_well_defined: Box<ObjWellDefinedProof>,
    pub body_well_defined: Box<ObjWellDefinedProof>,
    pub body_in_ret_set: AnonymousFnBodyInReturnSetProof,
    pub local_env: Box<ExecEnv>,
}

pub enum AnonymousFnBodyInReturnSetProof {
    CheckedMembership(VerifyFactResult),
    EmptyCompleteDomain(
        crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof,
    ),
}

pub struct CartObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CartObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct TupleObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl TupleObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FiniteSetSizeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetSizeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FiniteSetMaxObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetMaxObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FiniteSetMinObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetMinObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FnRangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub function_domains:
        Vec<crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof>,
}

impl FnRangeObjWellDefinedProof {
    pub fn from_checked_domains(
        stages: ObjWellDefinedByDefCommonStages,
        function_domains: Vec<
            crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
        >,
    ) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
            function_domains,
        }
    }
}

pub struct SumObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub signature_selection: Option<
        crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection,
    >,
}

impl SumObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
            signature_selection: None,
        }
    }
}

pub struct SumOfFiniteSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub signature_selection: Option<
        crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection,
    >,
}

impl SumOfFiniteSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
            signature_selection: None,
        }
    }
}

pub struct ProductObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub signature_selection: Option<
        crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection,
    >,
}

impl ProductObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
            signature_selection: None,
        }
    }
}

pub struct ProductOfFiniteSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub signature_selection: Option<
        crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection,
    >,
}

impl ProductOfFiniteSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
            signature_selection: None,
        }
    }
}

pub struct ReduceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ReduceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FiniteSetReduceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSetReduceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct RangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl RangeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ClosedRangeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ClosedRangeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FiniteSeqSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl FiniteSeqSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SeqSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SeqSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct StandardSetObjWellDefinedProof {}

impl StandardSetObjWellDefinedProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub struct StructObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl StructObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct FieldAccessObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub argument_scope: Option<FnObjArgumentScope>,
}

impl FieldAccessObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            argument_scope: None,
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct InstantiatedTemplateObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl InstantiatedTemplateObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct OneSideInfinityIntervalObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl OneSideInfinityIntervalObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IntervalObjObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl IntervalObjObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct PreimageObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub construction:
        crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof,
}

pub struct PreimageSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
    pub construction:
        crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof,
}

pub enum HyperbolicOperatorObjWellDefinedProofByDef {
    Sinh(SinhObjWellDefinedProof),
    Cosh(CoshObjWellDefinedProof),
    Tanh(TanhObjWellDefinedProof),
    Coth(CothObjWellDefinedProof),
    Sech(SechObjWellDefinedProof),
    Csch(CschObjWellDefinedProof),
}

pub struct SecObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SecObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CscObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CscObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ConjugateObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl ConjugateObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SinhObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SinhObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CoshObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CoshObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct TanhObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl TanhObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CothObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CothObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SechObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SechObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct CschObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl CschObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct SymmetricDifferenceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}

impl SymmetricDifferenceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub enum LimitOperatorObjWellDefinedProofByDef {
    MultivariableScalar(crate::execute::execute_fact_stmt::multivariable::selector::MultivariableScalarLimitWellDefinedProof),
    MultivariableVector(crate::execute::execute_fact_stmt::multivariable::selector::MultivariableVectorLimitWellDefinedProof),
    Function(FunctionLimitObjWellDefinedProof),
    Sequence(SequenceLimitObjWellDefinedProof),
    SequenceLimsup(SequenceLimsupObjWellDefinedProof),
    SequenceLiminf(SequenceLiminfObjWellDefinedProof),
}
pub struct SequenceLimitObjWellDefinedProof {
    pub sequence_wd: Box<ObjWellDefinedProof>,
    pub sequence_domain: crate::execute::execute_fact_stmt::sequence_limit::RealSequenceDomainProof,
    pub convergence: crate::execute::execute_fact_stmt::sequence_limit::SequenceConvergenceProof,
}

pub struct FunctionLimitObjWellDefinedProof {
    pub approach: crate::ast::obj::LimitApproach,
    pub function_wd: Box<ObjWellDefinedProof>,
    pub approach_wd: FunctionLimitApproachWellDefinedProof,
    pub function_domain:
        crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
    pub approach_real: crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof,
    pub convergence: crate::execute::execute_fact_stmt::function_limit::FunctionConvergenceProof,
}

/// Only finite approaches have a point, with its own checked WD and carrier.
pub enum FunctionLimitApproachWellDefinedProof {
    Finite { point_wd: Box<ObjWellDefinedProof> },
    AtPositiveInfinity,
    AtNegativeInfinity,
}

pub struct SequenceLimsupObjWellDefinedProof {
    pub sequence_wd: Box<ObjWellDefinedProof>,
    pub sequence_domain: crate::execute::execute_fact_stmt::sequence_limit::RealSequenceDomainProof,
    pub convergence: crate::execute::execute_fact_stmt::sequence_limit::SequenceConvergenceProof,
}
pub struct SequenceLiminfObjWellDefinedProof {
    pub sequence_wd: Box<ObjWellDefinedProof>,
    pub sequence_domain: crate::execute::execute_fact_stmt::sequence_limit::RealSequenceDomainProof,
    pub convergence: crate::execute::execute_fact_stmt::sequence_limit::SequenceConvergenceProof,
}

pub enum MatrixOperatorObjWellDefinedProofByDef {
    Determinant(DeterminantObjWellDefinedProof),
    ZeroMatrix(ZeroMatrixObjWellDefinedProof),
    IdentityMatrix(IdentityMatrixObjWellDefinedProof),
    Transpose(MatrixTransposeObjWellDefinedProof),
    ConjugateTranspose(MatrixConjugateTransposeObjWellDefinedProof),
    Trace(MatrixTraceObjWellDefinedProof),
    Add(MatrixAddObjWellDefinedProof),
    Subtract(MatrixSubtractObjWellDefinedProof),
    Scale(MatrixScaleObjWellDefinedProof),
    Multiply(MatrixMultiplyObjWellDefinedProof),
    Apply(MatrixApplyObjWellDefinedProof),
    Power(MatrixPowerObjWellDefinedProof),
    Inverse(MatrixInverseObjWellDefinedProof),
    Rank(MatrixRankObjWellDefinedProof),
    Minor(MatrixMinorObjWellDefinedProof),
    Cofactor(MatrixCofactorObjWellDefinedProof),
    Adjugate(MatrixAdjugateObjWellDefinedProof),
    Diagonal(MatrixDiagonalObjWellDefinedProof),
    OuterProduct(MatrixOuterProductObjWellDefinedProof),
    InnerProduct(FiniteInnerProductObjWellDefinedProof),
    EuclideanNorm(EuclideanNormObjWellDefinedProof),
    FrobeniusNorm(MatrixFrobeniusNormObjWellDefinedProof),
}

pub struct MatrixSetObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixSetObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct DeterminantObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl DeterminantObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct ZeroMatrixObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl ZeroMatrixObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct IdentityMatrixObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl IdentityMatrixObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MatrixTransposeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixTransposeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MatrixConjugateTransposeObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixConjugateTransposeObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MatrixTraceObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixTraceObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}

pub struct MatrixAddObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixAddObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixSubtractObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixSubtractObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixScaleObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixScaleObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixMultiplyObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixMultiplyObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixApplyObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixApplyObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixPowerObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixPowerObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixInverseObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixInverseObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixRankObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixRankObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixMinorObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixMinorObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixCofactorObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixCofactorObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixAdjugateObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixAdjugateObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixDiagonalObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixDiagonalObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixOuterProductObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixOuterProductObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct FiniteInnerProductObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl FiniteInnerProductObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct EuclideanNormObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl EuclideanNormObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
pub struct MatrixFrobeniusNormObjWellDefinedProof {
    pub child_obj_well_defined: Vec<Box<ObjWellDefinedProof>>,
    pub requirement_fact_verified: Vec<VerifyFactResult>,
}
impl MatrixFrobeniusNormObjWellDefinedProof {
    pub fn from_stages(stages: ObjWellDefinedByDefCommonStages) -> Self {
        let (child_obj_well_defined, requirement_fact_verified) =
            stages.into_success_child_proofs();
        Self {
            child_obj_well_defined,
            requirement_fact_verified,
        }
    }
}
