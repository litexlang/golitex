//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: definition / store-key names are PlainName; binder params use
//! BoundName / IdentifierId where wired (see `identifier_identity.md`).
//! FactId; LineFile.

use super::fact::{
    AndChainAtomicFact, AtomicFact, ExistShapedFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact,
    NormalAtomicFact, QuantifierFreeFact,
};
use super::line_file::LineFile;
use super::names::{AtomicName, BoundName, PlainName};
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

// Trust boundary: skip truth search; still requires WD; `-strict` rejects these.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnsafeStmt {
    TrustStmt(TrustStmt),
    TrustHaveStmt(TrustHaveStmt),
}

// What: assert facts without searching a proof.
// Surface: `trust: …`
// Stores: the listed facts (trusted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustStmt {
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

// What: introduce typed names and assert facts without searching a proof.
// Surface: `trust have x A: …`
// Stores: the names plus the listed facts (trusted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustHaveStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// DefinitionStmt
// -----------------------------------------------------------------------------

// What: introduce names / definitions into the environment
// (have, let, obtain, prop, thm, template, …).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionStmt {
    LetObjStmt(LetObjStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    // Name preimages from known image membership (see HaveByPreimageStmt).
    HaveByPreimageStmt(HaveByPreimageStmt),
    // Named set via ZF Replacement (no anonymous replacement_image Obj).
    HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt),
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

// What: bind a fresh name to a well-defined object (untyped equality def).
// Surface: `let a = expr`
// Stores: name `a` and `a = expr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetObjStmt {
    pub name: crate::new_pipeline::ast::names::BoundName,
    pub value: Obj,
    pub line_file: LineFile,
}

// What: introduce typed names from a nonempty set / param-type carrier.
// Surface: `have x A` / `have x, y A`
// Stores: the names, membership / param-type facts, and ordinary infer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: TypedParameterList,
    pub line_file: LineFile,
}

// What: introduce typed names defined equal to given objects.
// Surface: `have x A = expr`
// Stores: the names, carrier facts, and `x = expr` (plus ordinary infer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjEqualStmt {
    pub param_def: TypedParameterList,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

// What: introduce typed names that satisfy given quantifier-free facts.
// Surface: `have x A st {…}`
// Stores: the names, carrier facts, the body facts, and ordinary infer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjByExistFactsStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: LineFile,
}

// What: eliminate a known exist-shaped fact by naming its witnesses.
// Surface: `obtain a, b from exist …` / `exist! …`
// Stores: opaque witness names, their types, and the exist body facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromExistFact {
    pub equal_tos: Vec<PlainName>,
    pub fact: ExistShapedFact,
    pub line_file: LineFile,
}

// What: eliminate a known `$P(…)` whose concrete def is a single positive exist.
// Surface: `obtain a from $P(…)`
// Stores: opaque witness names after projecting the prop definition to exist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromAtomicFact {
    pub equal_tos: Vec<PlainName>,
    pub fact: NormalAtomicFact,
    pub line_file: LineFile,
}

// What: arguments of a theorem call — bare name or parenthesized objs.
// Surface: `thm_name` or `thm_name(args)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremCallArguments {
    Bare,
    Parenthesized(Vec<Obj>),
}

// What: a named theorem applied with optional arguments.
// Surface: `name` / `name(args)` (used by `release thm` / `by thm`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremCall {
    pub name: AtomicName,
    pub arguments: TheoremCallArguments,
}

// What: name opaque preimage witnesses from a known image-membership fact.
// Surface: `have by fn_preimage: a from square(2) $in fn_range(square)`
//
// Design: membership inference already exposes an existential preimage from
// `z $in fn_range(f)` (legacy also `y $in replacement(P, A)`). Multi-parameter
// `fn_range` makes that exist ugly to rewrite for `obtain`, so this statement
// takes the `$in` shape directly and introduces one fresh name per input
// coordinate (arity must match).
//
// Stores (so later `f(x, y)` is WD):
// - bind each name as a set-bound parameter of f's input carrier
// - `x $in Dom`, … (and f's extra domain facts, instantiated at those names)
// - `z = f(x, …)`
//
// Replacement images use `have by replacement_axiom: Img from prop P, set A`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveByPreimageStmt {
    pub preimage_names: Vec<PlainName>,
    // Must be `… $in fn_range(…)`.
    pub range_membership: InFact,
    pub line_file: LineFile,
}

// What: introduce a named set as the Replacement-axiom image of a binary prop.
// Surface: `have by replacement_axiom: Img from prop P, set A`
// (same `have by …: name from …` family as `have by fn_preimage`).
//
// Parenthesized Obj forms take objs only; putting a prop name in `(...)` would
// blur the prop/obj boundary, so this is a named statement rather than an Obj.
//
// Obligations: `prop_name` is a binary user prop/abstract_prop; `source_set` is
// WD; uniqueness of the prop on the source is already known:
//   forall x A, y, y2 set: $P(x,y) $P(x,y2) => y = y2
//
// Stores: `name` as a set, plus introduction/elimination:
//   forall x A, y set: $P(x,y) => y $in name
//   forall y name: exist x A st {$P(x,y)}
//
// Example:
//   abstract_prop image_rel(x, y)
//   trust:
//       forall x {1, 2}, y, y2 set:
//           $image_rel(x, y)
//           $image_rel(x, y2)
//           =>:
//               y = y2
//   have by replacement_axiom: Img from prop image_rel, set {1, 2}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveByReplacementAxiomStmt {
    pub name: BoundName,
    pub prop_name: AtomicName,
    pub source_set: Obj,
    pub line_file: LineFile,
}

// What: define a named function by an anonymous fn body.
// Surface: `have fn f(x A) B = expr`
// Stores: `f`, `f $in fn(…)`, and `f = anon_fn` (plus ordinary infer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualStmt {
    pub name: PlainName,
    pub equal_to_anonymous_fn: AnonymousFn,
    pub line_file: LineFile,
}

// What: shared `fn(params: dom) ret` shape for case-by-case / induction defs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetClause {
    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    pub ret_set: Obj,
}

// What: define a named function by exhaustive, pairwise-disjoint cases.
// Surface: `have fn f(…) B: case … = …`
// Stores: `f`, signature membership, and guarded case equations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: PlainName,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

// What: body of one induction case — a value, or nested subcases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveFnByInducCaseBody {
    EqualTo(Obj),
    NestedCases(Vec<HaveFnByInducCase>),
}

// What: one case arm in `have fn … by induc`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducCase {
    pub case_fact: AndChainAtomicFact,
    pub body: HaveFnByInducCaseBody,
}

// What: define a named function by induction on a decreasing measure.
// Surface: `have fn f(…) B by induc measure from lower: …`
// Stores: `f`, signature membership, and checked inductive case equations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByInducStmt {
    pub name: PlainName,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
    pub line_file: LineFile,
}

// What: define a named function from a proved `forall … exist!` goal (no formula body).
// Surface: `have fn f by exist!: forall …: exist! …`
// Stores: `f $in FnSet`, the property forall, and the uniqueness forall
// (`release obj def` re-stores the same three facts).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByForallExistUniqueStmt {
    pub name: PlainName,
    pub forall: ForallFact,
    pub line_file: LineFile,
}

// What: define a named concrete predicate with an iff body.
// Surface: `prop P(x A): <=>: …`
// Stores: foldable prop definition used by `by def` / `$P` verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefPropStmt {
    pub name: PlainName,
    pub typed_parameters: TypedParameterList,
    pub iff_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// What: declare a named abstract predicate (signature only, no body).
// Surface: `abstract_prop P(x, y)`
// Stores: an uninterpreted predicate interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAbstractPropStmt {
    pub name: PlainName,
    pub params: Vec<PlainName>,
    pub line_file: LineFile,
}

// What: named reusable parameter / domain bundle for later statements.
// Surface: `setting S(x A: …):`
// Stores: the setting definition for reuse as a binder prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefSettingStmt {
    pub name: PlainName,
    pub param_def: TypedParameterList,
    pub dom_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// What: bodies allowed inside a `template<…>:` definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemplateDefEnum {
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt),
    TrustHaveStmt(TrustHaveStmt),
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
}

// What: uniform definition over binder kinds such as `A set`.
// Surface: `template T<A set>: have …`
// Stores: a parameterized definition family; instances fill template args.
// `fn(A set)` is forbidden as a function domain — use template when the def
// itself is set-parameterized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefTemplateStmt {
    pub template_name: PlainName,
    pub template_arg_def: TypedParameterList,
    pub template_arg_dom: Vec<QuantifierFreeFact>,
    pub template_def_stmt: TemplateDefEnum,
    pub line_file: LineFile,
}

// What: one field of a struct definition — binder name + carrier set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructFieldDef {
    // Parse-allocated binder id; must match free refs in `<=>:` facts.
    pub binding: crate::new_pipeline::ast::names::BoundName,
    pub field_type: Obj,
}

// What: define a named struct carrier with fields and optional laws.
// Surface: `struct &Point: x R, y R`
// Stores: the struct def; field paths need `release struct def` to open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStructStmt {
    pub name: PlainName,
    pub param_def_with_dom: Option<(TypedParameterList, Vec<QuantifierFreeFact>)>,
    pub fields: Vec<StructFieldDef>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

// What: explicit return value inside an algo case / default.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoReturn {
    pub value: Obj,
    pub line_file: LineFile,
}

// What: one guarded return arm of an algorithm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgoCase {
    pub condition: AtomicFact, // may be negated when building default-return coverage
    pub return_stmt: AlgoReturn,
    pub line_file: LineFile,
}

// What: algo body entry — default return or a guarded case.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlgoReturnOrAlgoCase {
    AlgoReturn(AlgoReturn),
    AlgoCase(AlgoCase),
}

// What: define a named algorithm (computational case presentation).
// Surface: `algo f(x): …`
// Stores: an executable presentation; does not replace mathematical fn facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoStmt {
    pub name: PlainName,
    pub param_bindings: Vec<String>,
    pub default_return: Option<AlgoReturn>,
    pub cases: Vec<AlgoCase>,
    pub line_file: LineFile,
}

// What: define a named theorem with a proof of its target fact.
// Surface: `thm name: ? fact` then proof body
// Stores: a reusable theorem interface; universals also enter matching.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefThmStmt {
    pub name: PlainName,
    pub fact: Fact,
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: declare a named axiom (interface checked; truth trusted).
// Surface: `axiom name: forall …`
// Stores: a reusable theorem-like interface without a proof body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomStmt {
    pub name: PlainName,
    pub forall_fact: ForallFact,
    pub line_file: LineFile,
}

// What: named reusable proof strategy for a restricted atomic universal.
// Surface: `strategy name: forall …` then proof body
// Stores: the proved forall into ordinary matching under that name.
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

// What: instantiate a theorem and commit all of its conclusions.
// Surface: `release thm name(args)` / `release thm name`
// Stores: every instantiated conclusion and ordinary inferred consequences.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseThmStmt {
    pub call: TheoremCall,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// ByStmt
// -----------------------------------------------------------------------------

// What: prove a goal by a named proof method (`by cases`, `by induc`, …).
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

// What: prove a target by exhaustive case split.
// Surface: `by cases: case … prove: …`
// Stores: the requested then-facts / target when every branch closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByCasesStmt {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: LineFile,
}

// What: prove a target by deriving an impossibility from its negation.
// Surface: `by contra: …`
// Stores: the target fact when the contradiction closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByContraStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: LineFile,
}

// What: prove a forall by enumerating a finite set carrier.
// Surface: `by enumerate: forall x {…}: …`
// Stores: the forall when every element case closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateFiniteSetStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: ordinary induction on N (or from a lower bound).
// Surface: `by induc n from k: …`
// Stores: the inductive target when base and step close.
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

// What: strong induction on N (or from a lower bound).
// Surface: `by strong_induc n from k: …`
// Stores: the inductive target when base and strong step close.
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

// What: either a closed range `{a, …, b}` or an open-ended range form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

// What: how `by for` expands parameters over ranges or a cart of list sets.
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

// What: prove a forall by iterating over finite ranges / carts.
// Surface: `by for: forall …`
// Stores: the forall when every generated instance closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByForStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: prove object equality from both `$subset` directions (extensionality).
// Surface: `by extension: A = B`
// Stores: `A = B` as ordinary object equality in the pure-set model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByExtensionStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: prove membership by enumerating a numeric range.
// Surface: `by enumerate_range: e $in …`
// Stores: the membership fact when enumeration succeeds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateRangeStmt {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: LineFile,
}

// What: treat closed-range membership as a finite case split.
// Surface: `by closed_range_as_cases: e $in {a, …, b}`
// Stores: the membership fact when the case split closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByClosedRangeAsCasesStmt {
    pub element: Obj,
    pub closed_range: ClosedRange,
    pub line_file: LineFile,
}

// What: register / use transitivity of a user prop.
// Surface: `by transitive: forall …`
// Stores: a reusable transitive rewrite route for that prop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByTransitivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: register / use symmetry of a user prop.
// Surface: `by symmetric: forall …`
// Stores: a reusable symmetric rewrite route for that prop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BySymmetricPropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: register / use reflexivity of a user prop.
// Surface: `by reflexive: forall …`
// Stores: a reusable reflexive rewrite route for that prop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByReflexivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: apply Zorn's lemma with named order / bound / maximality props.
// Surface: `by zorn_lemma: …`
// Stores: `exist m S st {$M(m)}` using the supplied maximality prop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByZornLemmaStmt {
    pub set: Obj,
    pub prop_name: AtomicName,
    pub upper_bound_prop_name: AtomicName,
    pub maximal_prop_name: AtomicName,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: apply the axiom of choice to a family of nonempty sets.
// Surface: `by axiom_of_choice: family F`
// Stores: existence of a choice function for the family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByAxiomOfChoiceStmt {
    pub family: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: apply the axiom of regularity to a set.
// Surface: `by regularity_axiom: set S` (also `by regularity:`)
// Stores: the regularity conclusion for that set (strict mode rejects).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByRegularityAxiomStmt {
    pub set: Obj,
    pub line_file: LineFile,
}

// What: prove an atomic fact by unfolding a concrete / builtin definition.
// Surface: `by def: $P(…)`
// Stores: the target with explicit definition provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByDefStmt {
    pub fact: AtomicFact,
    pub line_file: LineFile,
}

// What: open one definition-owned struct layer (fields / bridges / laws).
// Surface: `release struct def e`
// Stores: one layer of tuple/identity bridges, field carriers, struct laws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseStructDefStmt {
    pub obj: Obj,
    pub line_file: LineFile,
}

// What: re-store one object-definition's facts for an identifier (preview).
// Surface: `release obj def I`
// Stores: that definition's type / equality / body / fn facts under `I`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseObjDefStmt {
    pub name: IdentifierObj,
    pub line_file: LineFile,
}

// What: cite a theorem and commit only one selected atomic conclusion.
// Surface: `by thm name(args): selected_fact`
// Stores: the selected atomic fact and ordinary inferred consequences.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByThmStmt {
    pub call: TheoremCall,
    pub selected_fact: AtomicFact,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// WitnessStmt
// -----------------------------------------------------------------------------

// What: supply concrete witnesses for an exist / atomic / nonempty goal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessAtomicFact(WitnessAtomicFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

// What: introduce an exist-shaped fact by exhibiting witnesses.
// Surface: `witness exist … from a, b:` …
// Stores: the exist / exist! fact (binder names stay local).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessExistFact {
    pub equal_tos: Vec<Obj>,
    pub exist_shaped_fact_in_witness: ExistShapedFact,
    pub line_file: LineFile,
}

// What: prove `$P(…)` when its concrete def is a single positive exist clause.
// Surface: `witness $P(…) from a:` …
// Stores: `$P(…)` then ordinary definition inference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessAtomicFact {
    pub atomic_fact: NormalAtomicFact,
    pub witnesses: Vec<Obj>,
    pub line_file: LineFile,
}

// What: prove a set is nonempty by exhibiting a member.
// Surface: `witness $is_nonempty_set(S) from e:` …
// Stores: nonemptiness of `S`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessNonemptySet {
    pub obj: Obj,
    pub set: Obj,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// ProofBlockStmt
// -----------------------------------------------------------------------------

// What: nested proof blocks that scope local work (claim / example / sketch / try).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    ExampleStmt(ExampleStmt),
    SketchStmt(SketchStmt),
    TryStmt(TryStmt),
}

// What: prove a subgoal in a child scope and keep only that target.
// Surface: `claim: ? fact` then proof body
// Stores: the target fact; helpers do not escape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: worked example with a goal and proof in a child scope.
// Surface: `example: ? fact` then proof body
// Stores: nothing outside the block (target and helpers stay local).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExampleStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: informal / non-binding proof sketch whose body still checks.
// Surface: `sketch:` …
// Stores: nothing outside the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SketchStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// What: soft-fail probe — Failed inside rolls back and does not stop the session.
// Surface: `try:` …
// Stores: all block effects when the body succeeds; none when rolled back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TryStmt {
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

// -----------------------------------------------------------------------------
// CommandStmt
// -----------------------------------------------------------------------------

// What: non-proof session commands (eval, …).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandStmt {
    EvalStmt(EvalStmt),
}

// What: evaluate an object for display (no new proof fact).
// Surface: `eval expr`
// Stores: evaluation output only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line_file: LineFile,
}
