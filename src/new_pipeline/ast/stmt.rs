//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names, FactId, LineFile; Identifier atoms carry IdentifierId.

use super::fact::{
    AndChainAtomicFact, AtomicFact, ExistFact, ExistOrAndChainAtomicFact, Fact, ForallFact,
    InFact, NormalAtomicFact, QuantifierFreeFact,
};
use super::names::AtomicName;
use super::obj::{
    AnonymousFn, ClosedRange, FiniteSeqSet, ListSet, Obj, Range, SeqSet,
};
use super::param::{SetBoundParameterList, TypedParameterList};
use super::line_file::LineFile;

// from statement/commands/evaluation.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalStmt {    pub obj_to_eval: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/algorithm.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoStmt {    pub name: String,
    pub param_bindings: Vec<String>,
    pub default_return: Option<AlgoReturn>,
    pub cases: Vec<AlgoCase>,
    pub line_file: LineFile,
}

// from statement/definitions/algorithm.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoReturn {    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/algorithm.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoCase {    pub condition: AtomicFact, // Algo cases may be negated when building default-return coverage.
    pub return_stmt: AlgoReturn,
    pub line_file: LineFile,
}

// from statement/definitions/algorithm.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgoReturnOrAlgoCase {
    AlgoReturn(AlgoReturn),
    AlgoCase(AlgoCase),
}

// from statement/definitions/axiom.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomStmt {    pub name: String,
    pub forall_fact: ForallFact,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducCase {    pub case_fact: AndChainAtomicFact,
    pub body: HaveFnByInducCaseBody,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveFnByInducCaseBody {
    EqualTo(Obj),
    NestedCases(Vec<HaveFnByInducCase>),
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducStmt {    pub name: String,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAbstractPropStmt {    pub name: String,
    pub params: Vec<crate::new_pipeline::ast::obj::Identifier>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetClause {    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    pub ret_set: Obj,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualCaseByCaseStmt {    pub name: String,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualStmt {    pub name: String,
    pub equal_to_anonymous_fn: AnonymousFn,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByForallExistUniqueStmt {    pub name: String,
    pub forall: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveTupleStmt {    pub name: String,
    pub index_name: String,
    pub dimension: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveCartStmt {    pub name: String,
    pub index_name: String,
    pub dimension: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveSeqStmt {    pub name: String,
    pub seq_set: SeqSet,
    pub index_name: String,
    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFiniteSeqStmt {    pub name: String,
    pub finite_seq_set: FiniteSeqSet,
    pub index_name: String,
    pub bound: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefTemplateStmt {    pub template_name: String,
    pub template_arg_def: TypedParameterList,
    pub template_arg_dom: Vec<QuantifierFreeFact>,
    pub template_def_stmt: TemplateDefEnum,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefSettingStmt {    pub name: String,
    pub param_def: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
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
    HaveTupleStmt(HaveTupleStmt),
    HaveCartStmt(HaveCartStmt),
    HaveSeqStmt(HaveSeqStmt),
    HaveFiniteSeqStmt(HaveFiniteSeqStmt),
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromExistFact {    pub equal_tos: Vec<String>,
    pub fact: ExistFact,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromAtomicFact {    pub equal_tos: Vec<String>,
    pub fact: NormalAtomicFact,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromThm {    pub equal_tos: Vec<String>,
    pub call: TheoremCall,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveByPreimageStmt {    pub preimage_names: Vec<String>,
    pub range_membership: InFact,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetObjStmt {
    pub name: String,
    pub identifier_id: crate::new_pipeline::runtime::IdentifierId,
    pub value: Obj,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjEqualStmt {    pub param_def: TypedParameterList,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {    pub param_def: TypedParameterList,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjByExistFactsStmt {    pub param_def: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustHaveStmt {    pub param_def: TypedParameterList,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

// from statement/definitions/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefPropStmt {    pub name: String,
    pub typed_parameters: TypedParameterList,
    pub iff_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// from statement/definitions/strategy.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStrategyStmt {    pub name: String,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/definitions/structure.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructFieldDef {    pub binding: String,
    pub field_type: Obj,
}

// from statement/definitions/structure.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStructStmt {    pub name: String,
    pub param_def_with_dom: Option<(TypedParameterList, Vec<QuantifierFreeFact>)>,
    pub fields: Vec<StructFieldDef>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// from statement/definitions/theorem.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefThmStmt {    pub name: String,
    pub fact: Fact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/claim.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimStmt {    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/example.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExampleStmt {    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/sketch.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SketchStmt {    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/trust.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustStmt {    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/try_block.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TryStmt {    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/witness.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessNonemptySet {    pub obj: Obj,
    pub set: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/witness.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessExistFact {    pub equal_tos: Vec<Obj>,
    pub exist_fact_in_witness: ExistFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_blocks/witness.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessAtomicFact {    pub atomic_fact: NormalAtomicFact,
    pub witnesses: Vec<Obj>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/antisymmetric_prop.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByAntisymmetricPropStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/axiom_of_choice.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByAxiomOfChoiceStmt {    pub family: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/cases.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByCasesStmt {    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: LineFile,
}

// from statement/proof_directives/contra.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByContraStmt {    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: LineFile,
}

// from statement/proof_directives/definition.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByDefStmt {    pub fact: AtomicFact,
    pub line_file: LineFile,
}

// from statement/proof_directives/enumerate.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateFiniteSetStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/extension.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByExtensionStmt {    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/finite_set_induc.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByFiniteSetInducStmt {    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub param_binding: String,
    pub carrier_set: Option<Obj>,
    pub element_param_binding: String,
    pub smaller_set_param_binding: String,
    pub base_proof: Vec<Stmt>,
    pub step_proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/for_stmt.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

// from statement/proof_directives/for_stmt.rs
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

// from statement/proof_directives/for_stmt.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByForStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/induc.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByInducStmt {    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub base_proof: Option<Vec<Stmt>>,
    pub step_proof: Option<Vec<Stmt>>,
    pub param_binding: String,
    pub induc_from: Obj,
    /// When true, the induction step uses `forall y` with `m <= y <= n` as the hypothesis band (strong / complete induction).
    pub strong: bool,
    pub line_file: LineFile,
}

// from statement/proof_directives/range.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByClosedRangeAsCasesStmt {    pub element: Obj,
    pub closed_range: ClosedRange,
    pub line_file: LineFile,
}

// from statement/proof_directives/range.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateRangeStmt {    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: LineFile,
}

// from statement/proof_directives/reflexive_prop.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByReflexivePropStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/regularity_axiom.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByRegularityAxiomStmt {    pub set: Obj,
    pub line_file: LineFile,
}

// from statement/proof_directives/struct_definition.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByStructDefStmt {    pub obj: Obj,
    pub line_file: LineFile,
}

// from statement/proof_directives/symmetric_prop.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BySymmetricPropStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/theorem_release.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseThmStmt {    pub call: TheoremCall,
    pub line_file: LineFile,
}

// from statement/proof_directives/theorem_selection.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByThmStmt {    pub call: TheoremCall,
    pub selected_fact: AtomicFact,
    pub line_file: LineFile,
}

// from statement/proof_directives/transitive_prop.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByTransitivePropStmt {    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/proof_directives/zorn_lemma.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByZornLemmaStmt {    pub set: Obj,
    pub prop_name: AtomicName,
    pub upper_bound_prop_name: AtomicName,
    pub maximal_prop_name: AtomicName,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    Definition(DefinitionStmt),
    ReleaseThmStmt(ReleaseThmStmt),
    By(ByStmt),
    Witness(WitnessStmt),
    ProofBlock(ProofBlockStmt),
    Command(CommandStmt),
}

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnsafeStmt {
    TrustStmt(TrustStmt),
    TrustHaveStmt(TrustHaveStmt),
}

// from statement/statement.rs
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
    HaveTupleStmt(HaveTupleStmt),
    HaveCartStmt(HaveCartStmt),
    HaveSeqStmt(HaveSeqStmt),
    HaveFiniteSeqStmt(HaveFiniteSeqStmt),
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

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByStmt {
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    ByFiniteSetInducStmt(ByFiniteSetInducStmt),
    ByInducStmt(ByInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByEnumerateRangeStmt(ByEnumerateRangeStmt),
    ByClosedRangeAsCasesStmt(ByClosedRangeAsCasesStmt),
    ByTransitivePropStmt(ByTransitivePropStmt),
    BySymmetricPropStmt(BySymmetricPropStmt),
    ByReflexivePropStmt(ByReflexivePropStmt),
    ByAntisymmetricPropStmt(ByAntisymmetricPropStmt),
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
    ByRegularityAxiomStmt(ByRegularityAxiomStmt),
    ByDefStmt(ByDefStmt),
    ByStructDefStmt(ByStructDefStmt),
    ByThmStmt(ByThmStmt),
}

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessAtomicFact(WitnessAtomicFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    ExampleStmt(ExampleStmt),
    SketchStmt(SketchStmt),
    TryStmt(TryStmt),
}

// from statement/statement.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandStmt {
    EvalStmt(EvalStmt),
}

// from statement/theorem_call.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremCallArguments {
    Bare,
    Parenthesized(Vec<Obj>),
}

// from statement/theorem_call.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremCall {    pub name: AtomicName,
    pub arguments: TheoremCallArguments,
}

