//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: definition / store-key names are PlainName; binder params use
//! BoundName / IdentifierId where wired (see `identifier_identity.md`).
//! FactId; LineFile.

use super::fact::{
    AndChainAtomicFact, AtomicFact, ExistFactFamily, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact,
    NormalAtomicFact, QuantifierFreeFact,
};
use super::line_file::LineFile;
use super::names::{AtomicName, PlainName};
use super::obj::{AnonymousFn, ClosedRange, IdentifierObj, ListSet, Obj, Range};
use super::param::{SetBoundParameterList, TypedParameterList};

// -----------------------------------------------------------------------------
// Stmt (file spine)
// -----------------------------------------------------------------------------

// Env-changing action: assert a Fact, define, prove by …, trust, … .
// Not a value (Obj) and not itself a proposition (Fact); a bare Fact stmt asserts one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    Definition(DefinitionStmt),
    ReleaseThmStmt(ReleaseThmStmt),
    ReleaseStructDefStmt(ReleaseStructDefStmt),
    ReleaseObjDefStmt(ReleaseObjDefStmt),
    By(ByStmt),
    Witness(WitnessStmt),
    ProofBlock(ProofBlockStmt),
    Command(CommandStmt),
}

// -----------------------------------------------------------------------------
// Fact — see fact.rs
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// UnsafeStmt
// -----------------------------------------------------------------------------

// Trust boundary: assert without proof search. Still requires WD; `-strict` rejects these.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnsafeStmt {
    TrustStmt(TrustStmt),
    TrustHaveStmt(TrustHaveStmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustStmt {
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustHaveStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// DefinitionStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionStmt {
    LetObjStmt(LetObjStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    ObtainObjFromThm(ObtainObjFromThm),
    HaveByPreimageStmt(HaveByPreimageStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    DefSettingStmt(DefSettingStmt),
    DefTemplateStmt(DefTemplateStmt),
    DefStructStmt(DefStructStmt),
    DefAlgoStmt(DefAlgoStmt),
    DefThmStmt(DefThmStmt),
    AxiomStmt(AxiomStmt),
    DefStrategyStmt(DefStrategyStmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetObjStmt {
    pub name: crate::new_pipeline::ast::names::BoundName,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: TypedParameterList,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjEqualStmt {
    pub param_def: TypedParameterList,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjByExistFactsStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromExistFact {
    pub equal_tos: Vec<PlainName>,
    pub fact: ExistFactFamily,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromAtomicFact {
    pub equal_tos: Vec<PlainName>,
    pub fact: NormalAtomicFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremCallArguments {
    Bare,
    Parenthesized(Vec<Obj>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremCall {
    pub name: AtomicName,
    pub arguments: TheoremCallArguments,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromThm {
    pub equal_tos: Vec<PlainName>,
    pub call: TheoremCall,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveByPreimageStmt {
    pub preimage_names: Vec<PlainName>,
    pub range_membership: InFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualStmt {
    pub name: PlainName,
    pub equal_to_anonymous_fn: AnonymousFn,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetClause {
    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    pub ret_set: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: PlainName,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveFnByInducCaseBody {
    EqualTo(Obj),
    NestedCases(Vec<HaveFnByInducCase>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducCase {
    pub case_fact: AndChainAtomicFact,
    pub body: HaveFnByInducCaseBody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducStmt {
    pub name: PlainName,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
    pub line_file: LineFile,
}

// `have fn f ... by exist!`: goal-only; must prove forall…exist! first.
// Stores `f ∈ FnSet` + property + uniqueness — not `f = AnonymousFn` (no unfold-as-formula).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByForallExistUniqueStmt {
    pub name: PlainName,
    pub forall: ForallFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefPropStmt {
    pub name: PlainName,
    pub typed_parameters: TypedParameterList,
    pub iff_facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAbstractPropStmt {
    pub name: PlainName,
    pub params: Vec<PlainName>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefSettingStmt {
    pub name: PlainName,
    pub param_def: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemplateDefEnum {
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    TrustHaveStmt(TrustHaveStmt),
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    ObtainObjFromThm(ObtainObjFromThm),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
}

// Uniform definition over binder kinds such as `A set`. Not a function domain:
// `fn(A set)` is forbidden; use `template<A set>:` when the def itself is set-parameterized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefTemplateStmt {
    pub template_name: PlainName,
    pub template_arg_def: TypedParameterList,
    pub template_arg_dom: Vec<QuantifierFreeFact>,
    pub template_def_stmt: TemplateDefEnum,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructFieldDef {
    /// Parse-allocated binder id; must match free refs in `<=>:` facts.
    pub binding: crate::new_pipeline::ast::names::BoundName,
    pub field_type: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStructStmt {
    pub name: PlainName,
    pub param_def_with_dom: Option<(TypedParameterList, Vec<QuantifierFreeFact>)>,
    pub fields: Vec<StructFieldDef>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoReturn {
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoCase {
    pub condition: AtomicFact, // Algo cases may be negated when building default-return coverage.
    pub return_stmt: AlgoReturn,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgoReturnOrAlgoCase {
    AlgoReturn(AlgoReturn),
    AlgoCase(AlgoCase),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoStmt {
    pub name: PlainName,
    pub param_bindings: Vec<String>,
    pub default_return: Option<AlgoReturn>,
    pub cases: Vec<AlgoCase>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefThmStmt {
    pub name: PlainName,
    pub fact: Fact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomStmt {
    pub name: PlainName,
    pub forall_fact: ForallFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStrategyStmt {
    pub name: PlainName,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// ReleaseThmStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseThmStmt {
    pub call: TheoremCall,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// ByStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByStmt {
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    ByInducStmt(ByInducStmt),
    ByStrongInducStmt(ByStrongInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByEnumerateRangeStmt(ByEnumerateRangeStmt),
    ByClosedRangeAsCasesStmt(ByClosedRangeAsCasesStmt),
    ByTransitivePropStmt(ByTransitivePropStmt),
    BySymmetricPropStmt(BySymmetricPropStmt),
    ByReflexivePropStmt(ByReflexivePropStmt),
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
    ByRegularityAxiomStmt(ByRegularityAxiomStmt),
    ByDefStmt(ByDefStmt),
    ByThmStmt(ByThmStmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByCasesStmt {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByContraStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateFiniteSetStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}



#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub base_proof: Option<Vec<Stmt>>,
    pub step_proof: Option<Vec<Stmt>>,
    pub param_binding: String,
    pub induc_from: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByStrongInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub base_proof: Option<Vec<Stmt>>,
    pub step_proof: Option<Vec<Stmt>>,
    pub param_binding: String,
    pub induc_from: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByForExpansion {
    Ranges {
        params: Vec<String>,
        ranges: Vec<ClosedRangeOrRange>,
    },
    CartOfListSets {
        param: String,
        factors: Vec<ListSet>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByForStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// Prove `left = right` from both `$subset` directions. In the pure-set model this is
// ordinary object equality, not a separate host-language Set equality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByExtensionStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateRangeStmt {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByClosedRangeAsCasesStmt {
    pub element: Obj,
    pub closed_range: ClosedRange,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByTransitivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BySymmetricPropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByReflexivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByZornLemmaStmt {
    pub set: Obj,
    pub prop_name: AtomicName,
    pub upper_bound_prop_name: AtomicName,
    pub maximal_prop_name: AtomicName,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByAxiomOfChoiceStmt {
    pub family: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByRegularityAxiomStmt {
    pub set: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByDefStmt {
    pub fact: AtomicFact,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseStructDefStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseObjDefStmt {
    pub name: IdentifierObj,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByThmStmt {
    pub call: TheoremCall,
    pub selected_fact: AtomicFact,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// WitnessStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessAtomicFact(WitnessAtomicFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessExistFact {
    pub equal_tos: Vec<Obj>,
    pub exist_fact_in_witness: ExistFactFamily,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessAtomicFact {
    pub atomic_fact: NormalAtomicFact,
    pub witnesses: Vec<Obj>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessNonemptySet {
    pub obj: Obj,
    pub set: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// ProofBlockStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    ExampleStmt(ExampleStmt),
    SketchStmt(SketchStmt),
    TryStmt(TryStmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExampleStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SketchStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TryStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// CommandStmt
// -----------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandStmt {
    EvalStmt(EvalStmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line_file: LineFile,
}
