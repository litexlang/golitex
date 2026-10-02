//! Framework AST data shapes.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: definition / store-key names are PlainName; binder params use
//! BoundName / IdentifierId where wired (see `identifier_identity.md`).
//! FactId; SourceLine.

use super::fact::{
    AndChainAtomicFact, AtomicFact, ExistOrAndChainAtomicFact, ExistShapedFact, Fact, ForallFact,
    InFact, NormalAtomicFact, QuantifierFreeFact,
};
use super::line_file::SourceLine;
use super::names::{AtomicName, BoundName, PlainName};
use super::obj::{AnonymousFn, ClosedRange, IdentifierObj, ListSet, Obj, Range};
use super::param::{SetBoundParameterList, TypedParameterList};

// -----------------------------------------------------------------------------
// Stmt (file spine)
// -----------------------------------------------------------------------------

// Env-changing action: assert a Fact, define names/interfaces, prove by …,
// release / expand packaged facts, register prop properties, trust, … .
// Not a value (Obj) and not itself a proposition (Fact); a bare Fact stmt asserts one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    // Assert one fact; search a proof and store it. Example: `1 + 1 = 2`.
    Fact(Fact),
    // Skip truth search; WD still required; `-strict` rejects. Example: `trust: …`.
    Trust(TrustBoundaryStmt),
    // Define a name / interface into the env (`DefineObj` or prop/thm/have fn/…).
    // Example: `let a = 1`, `have x R`, `prop P(x R): …`, `thm t: ? …`.
    Definition(DefinitionStmt),
    // Unpack packaged defs / axioms, or expand range membership into equality cases.
    // Example: `release thm t(a)`, `expand: x $in range(1, 3)`, `release zorn_lemma: …`.
    ReleaseAndExpand(ReleaseAndExpandStmt),
    // Prove a goal by a named method. Example: `by cases: …`, `by contra: …`.
    By(ByStmt),
    // Register rewrite/infer laws of a user prop (no proof body).
    // Example: `register transitive: ? forall …`.
    Register(RegisterStmt),
    // Exhibit witnesses for exist / atomic-exist / nonempty goals.
    // Example: `witness exist x R st {…} from a:`.
    Witness(WitnessStmt),
    // Nested local proof scope. Example: `claim: ? fact` … / `sketch:` ….
    ProofBlock(ProofBlockStmt),
    // Non-proof session command. Example: `eval expr`.
    Command(CommandStmt),
}

// -----------------------------------------------------------------------------
// Fact — see fact.rs
// -----------------------------------------------------------------------------

// -----------------------------------------------------------------------------
// TrustBoundaryStmt
// -----------------------------------------------------------------------------

// Trust boundary: skip truth search; still requires WD; `-strict` rejects these.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrustBoundaryStmt {
    // Assert facts without searching a proof. Example: `trust: 1 = 1`.
    TrustStmt(TrustStmt),
    // Introduce typed names and assert facts without searching a proof.
    // Example: `trust have x R: x = x`.
    TrustHaveStmt(TrustHaveStmt),
}

// What: assert facts without searching a proof.
// Surface: `trust: …`
// Stores: the listed facts (trusted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustStmt {
    pub facts: Vec<Fact>,
    pub line_file: SourceLine,
}

// What: introduce typed names and assert facts without searching a proof.
// Surface: `trust have x A: …`
// Stores: the names plus the listed facts (trusted).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrustHaveStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<Fact>,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// DefinitionStmt
// -----------------------------------------------------------------------------

// Define something into the environment.
// `DefineObj` nests fresh object names; other variants are flat siblings
// (reusable interfaces / function objects).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionStmt {
    // Fresh object names: `let` / `have` / `obtain` / `have by …`.
    DefineObj(DefineObjStmt),
    // Named function by one expression body. Example: `have fn f(x R) R = x`.
    HaveFnEqualStmt(HaveFnEqualStmt),
    // Named function by exhaustive disjoint cases.
    // Example: `have fn f(x R) R by cases: case x = 0: 0 …`.
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    // Named function by induction on a measure.
    // Example: `have fn countdown(n N) N by induc n from 0: …`.
    HaveFnByInducStmt(HaveFnByInducStmt),
    // Named function from a proved `forall … exist!` (no formula body).
    // Example: `have fn f by exist!: ? forall x A: exist! y B st {…}`.
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
    // Concrete predicate with iff body. Example: `prop above_zero(x R): x > 0`.
    DefPropStmt(DefPropStmt),
    // Abstract predicate signature only. Example: `abstract_prop F(x, y)`.
    DefAbstractPropStmt(DefAbstractPropStmt),
    // Parameterized counterpart of one ordinary definition.
    // Example: `template<S set>: have carrier_copy set = S`.
    DefTemplateStmt(DefTemplateStmt),
    // Named product carrier. Example:
    //   struct Point:
    //       x R
    //       y R
    DefStructStmt(DefStructStmt),
    // Define a named function together with its executable cases.
    // Example: `algo f(x R) R by cases: case …: …`.
    DefAlgoByCasesStmt(DefAlgoByCasesStmt),
    // Define a named function together with its executable induction.
    // Example: `algo countdown(n N) N by induc n from 0: …`.
    DefAlgoByInducStmt(DefAlgoByInducStmt),
    // Named theorem with goal and proof. Example: `thm t: ? 1 = 1`.
    DefThmStmt(DefThmStmt),
    // Named axiom (interface checked; truth trusted). Example: `axiom a: ? forall …`.
    AxiomStmt(AxiomStmt),
    // Named reusable proof strategy. Example: `strategy s: ? forall …` then proof.
    DefStrategyStmt(DefStrategyStmt),
}

// Introduce / define fresh object names and carriers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefineObjStmt {
    // Untyped equality binding. Example: `let a = 1`.
    LetObjStmt(LetObjStmt),
    // Typed names from a nonempty carrier (set). Example: `have x R` / `have x, y R`.
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    // Typed names equal to given objects. Example: `have x R = 1`.
    HaveObjEqualStmt(HaveObjEqualStmt),
    // Typed names satisfying body facts; the matching `exist` must already be known.
    // Example: `have x R: x > 0` (requires `exist x R st {x > 0}` proved).
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    // Name witnesses of a known `exist` / `exist!`.
    // Example: `obtain a from exist x R st {x = 0}`.
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    // Name witnesses when `$P(…)` unfolds to one positive exist.
    // Example: `obtain a from $P(…)`.
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    // Opaque preimages from known image membership.
    // Example: `have by fn_preimage: a from f(x) $in fn_range(f)`.
    HaveByPreimageStmt(HaveByPreimageStmt),
    // Named set via ZF Replacement (no anonymous replacement_image Obj).
    // Example: `have by replacement_axiom: Img from prop P, set A`.
    HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt),
}

// What: bind a fresh name to a well-defined object (untyped equality def).
// Surface: `let a = expr`
// Stores: name `a` and `a = expr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetObjStmt {
    pub name: crate::ast::names::BoundName,
    pub value: Obj,
    pub line_file: SourceLine,
}

// What: introduce typed names from a nonempty set / param-type carrier.
// Surface: `have x A` / `have x, y A`
// Stores: the names, membership / param-type facts, and ordinary infer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: TypedParameterList,
    pub line_file: SourceLine,
}

// What: introduce typed names defined equal to given objects.
// Surface: `have x A = expr`
// Stores: the names, carrier facts, and `x = expr` (plus ordinary infer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjEqualStmt {
    pub param_def: TypedParameterList,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: SourceLine,
}

// What: introduce typed names that satisfy given quantifier-free facts.
// Surface: `have x R:` then indented facts (not `st {…}` sugar here).
// Requires: the corresponding `exist` (same params + body) is already proved.
// Stores: the names, carrier facts, the body facts, and ordinary infer.
// Example: `have x R: x > 0` after `exist x R st {x > 0}` is known.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveObjByExistFactsStmt {
    pub param_def: TypedParameterList,
    pub facts: Vec<QuantifierFreeFact>,
    pub line_file: SourceLine,
}

// What: eliminate a known exist-shaped fact by naming its witnesses.
// Surface: `obtain a, b from exist …` / `exist! …`
// Stores: opaque witness names, their types, and the exist body facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromExistFact {
    pub equal_tos: Vec<BoundName>,
    pub fact: ExistShapedFact,
    pub line_file: SourceLine,
}

// What: eliminate a known `$P(…)` whose concrete def is a single positive exist.
// Surface: `obtain a from $P(…)`
// Stores: opaque witness names after projecting the prop definition to exist.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObtainObjFromAtomicFact {
    pub equal_tos: Vec<BoundName>,
    pub fact: NormalAtomicFact,
    pub line_file: SourceLine,
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
    pub preimage_names: Vec<BoundName>,
    // Must be `… $in fn_range(…)`.
    pub range_membership: InFact,
    pub line_file: SourceLine,
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
    pub line_file: SourceLine,
}

// What: define a named function by an anonymous fn body.
// Surface: `have fn f(x A) B = expr`
// Stores: `f`, `f $in fn(…)`, and `f = anon_fn` (plus ordinary infer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualStmt {
    pub name: BoundName,
    pub equal_to_anonymous_fn: AnonymousFn,
    pub line_file: SourceLine,
}

// What: shared `fn(params: dom) ret` shape for case-by-case / induction defs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSetClause {
    pub set_bound_parameters: SetBoundParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    pub ret_set: Obj,
}

// What: define a named function by exhaustive, pairwise-disjoint cases.
// Surface: `have fn f(…) B by cases:` then `case …: …`
// Stores: `f`, signature membership, and guarded case equations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: BoundName,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: SourceLine,
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
    pub name: BoundName,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
    pub line_file: SourceLine,
}

// What: define a named function from a proved `forall … exist!` goal (no formula body).
// Surface: `have fn f by exist!:` then `? forall …: exist! …`
// Stores: `f $in FnSet`, the property forall, and the uniqueness forall
// (`release obj def` re-stores the same three facts).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HaveFnByForallExistUniqueStmt {
    pub name: BoundName,
    pub forall: ForallFact,
    pub line_file: SourceLine,
}

// What: define a named concrete predicate with an iff body.
// Surface: `prop P(x A):` then body facts (each fact is an iff conjunct).
// Stores: foldable prop definition used by `by def` / `$P` verify.
// Example: `prop above_zero(x R): x > 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefPropStmt {
    pub name: PlainName,
    pub typed_parameters: TypedParameterList,
    pub iff_facts: Vec<Fact>,
    pub line_file: SourceLine,
}

// What: declare a named abstract predicate (signature only, no body).
// Surface: `abstract_prop P(x, y)`
// Stores: an uninterpreted predicate interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAbstractPropStmt {
    pub name: PlainName,
    pub params: Vec<PlainName>,
    pub line_file: SourceLine,
}

// Bodies allowed inside a `template<…>:` definition — same shapes that work
// outside the template; the template only adds parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemplateDefEnum {
    // Example: `template<S set>: have carrier_copy set`.
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    // Example: `template<S set>: have carrier_copy set = S`.
    HaveObjEqualStmt(HaveObjEqualStmt),
    // Example: `template<S set>: have x S: x = x`.
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    // Example: `template<S set>: have by replacement_axiom: Img from prop P, set S`.
    HaveByReplacementAxiomStmt(HaveByReplacementAxiomStmt),
    // Example: `template<S set>: trust have x S: x = x`.
    TrustHaveStmt(TrustHaveStmt),
    // Example: `template<S set>: obtain a from exist x S st {…}`.
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    // Example: `template<S set>: obtain a from $P(…)`.
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    // Example: `template<S set>: have fn id(x S) S = x`.
    HaveFnEqualStmt(HaveFnEqualStmt),
    // Example: `template<S set>: have fn f(x S) S by cases: …`.
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    // Example: `template<S set>: have fn f(…) S by induc …`.
    HaveFnByInducStmt(HaveFnByInducStmt),
    // Example: `template<S set>: have fn f by exist!: …`.
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
}

// What: parameterized counterpart of an ordinary definition statement.
// Surface: `template<A set>: have name …` / `template<A set>: have fn f …`
// Stores: a definition family; `\name<args>` fills the template args.
//
// The body is checked as if the angle-bracket parameters were already
// introduced. Instantiating `\name<args>` yields the corresponding defined
// object or function.
//
// Why not `fn(A set)` / a fake fn_set domain: a function parameter must range
// over one fixed set. Binder kind `set` is not such a set — it means "a set
// parameter," not an element of a set-of-all-sets. Use template when the
// definition itself is parameterized by an arbitrary set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefTemplateStmt {
    pub template_name: PlainName,
    pub template_arg_def: TypedParameterList,
    pub template_arg_dom: Vec<QuantifierFreeFact>,
    pub template_def_stmt: TemplateDefEnum,
    pub line_file: SourceLine,
}

// What: one field of a struct definition — binder name + carrier set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructFieldDef {
    // Parse-allocated binder id; must match free refs in `<=>:` facts.
    pub binding: crate::ast::names::BoundName,
    pub field_type: Obj,
}

// What: define a named struct carrier with fields and optional laws.
// Surface: `struct Point:` then fields; optional `<=>:` laws.
// Stores: the struct def; field paths need `release struct def` to open.
// Example:
//   struct Point:
//       x R
//       y R
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStructStmt {
    pub name: PlainName,
    pub param_def_with_dom: Option<(TypedParameterList, Vec<QuantifierFreeFact>)>,
    pub fields: Vec<StructFieldDef>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: SourceLine,
}

// What: define a named function by cases and store its executable presentation.
// Surface: `algo f(…) B by cases:` then `case …: …`
// Stores: mathematical fn facts (same strength as `have fn … by cases`) plus algo.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoByCasesStmt {
    pub name: BoundName,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: SourceLine,
}

// What: define a named function by induction and store its executable presentation.
// Surface: `algo f(…) B by induc measure from lower: …`
// Stores: mathematical fn facts (same strength as `have fn … by induc`) plus algo.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefAlgoByInducStmt {
    pub name: BoundName,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
    pub line_file: SourceLine,
}

// What: define a named theorem with a proof of its target fact.
// Surface: `thm name: ? fact` then proof body
// Stores: a reusable theorem interface; universals also enter matching.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefThmStmt {
    pub name: PlainName,
    pub fact: Fact,
    pub prove_process: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: declare a named axiom (interface checked; truth trusted).
// Surface: `axiom name: forall …`
// Stores: a reusable theorem-like interface without a proof body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomStmt {
    pub name: PlainName,
    pub forall_fact: ForallFact,
    pub line_file: SourceLine,
}

// What: named reusable proof strategy for a restricted atomic universal.
// Surface: `strategy name: forall …` then proof body
// Stores: the named strategy definition; later non-equality atomics may apply
// it via the known_strategy search stage (not ambient known_forall).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefStrategyStmt {
    pub name: PlainName,
    pub forall_fact: ForallFact,
    pub prove_process: Vec<Stmt>,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// ReleaseAndExpandStmt
// -----------------------------------------------------------------------------

// Unpack packaged definitions / axioms, or expand finite numeric membership.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReleaseAndExpandStmt {
    // Instantiate a theorem and commit all conclusions.
    // Example: `release thm t` / `release thm t(a, b)`.
    ReleaseThmStmt(ReleaseThmStmt),
    // Open one definition-owned struct layer (fields / bridges / laws).
    // Example: `release struct def p`.
    ReleaseStructDefStmt(ReleaseStructDefStmt),
    // Re-store one object-definition's facts for an identifier (preview).
    // Example: `release obj def f`.
    ReleaseObjDefStmt(ReleaseObjDefStmt),
    // Expand numeric-range membership into equality cases.
    // Example: `expand: x $in range(1, 3)` stores `x = 1 or x = 2`.
    ExpandRangeStmt(ExpandRangeStmt),
    // Apply Zorn's lemma with named order / bound / maximality props.
    // Example: `release zorn_lemma: set S, prop P, prop U, prop M:`.
    ReleaseZornLemmaStmt(ReleaseZornLemmaStmt),
    // Axiom of choice on a family of nonempty sets.
    // Example: `release axiom_of_choice: set F:`.
    ReleaseAxiomOfChoiceStmt(ReleaseAxiomOfChoiceStmt),
    // Axiom of regularity.
    // Example: `release regularity_axiom(S)`.
    ReleaseRegularityAxiomStmt(ReleaseRegularityAxiomStmt),
}

// What: instantiate a theorem and commit all of its conclusions.
// Surface: `release thm name(args)` / `release thm name`
// Stores: every instantiated conclusion and ordinary inferred consequences.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseThmStmt {
    pub call: TheoremCall,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// ByStmt
// -----------------------------------------------------------------------------

// Prove a goal by a named proof method.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ByStmt {
    // Exhaustive case split. Example: `by cases: case … prove: …`.
    ByCasesStmt(ByCasesStmt),
    // Contradiction from the negation. Example: `by contra: …`.
    ByContraStmt(ByContraStmt),
    // Forall by enumerating a finite set. Example: `by enumerate: forall x {…}: …`.
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    // Ordinary induction on N (or from a lower bound). Example: `by induc n from 0: …`.
    ByInducStmt(ByInducStmt),
    // Strong induction on N. Example: `by strong_induc n from 0: …`.
    ByStrongInducStmt(ByStrongInducStmt),
    // Forall by iterating finite ranges / carts. Example: `by for: forall …`.
    ByForStmt(ByForStmt),
    // Set extensionality via both `$subset` directions. Example: `by extension: A = B`.
    ByExtensionStmt(ByExtensionStmt),
    // Function extensionality on a shared FnSet (preview). Example: `by fn_extension: f = g`.
    ByFnExtensionStmt(ByFnExtensionStmt),
    // Unfold a concrete / builtin definition. Example: `by def: $P(…)`.
    ByDefStmt(ByDefStmt),
    // Cite a theorem for one selected atomic conclusion.
    // Example: `by thm name(args): selected_fact`.
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
    pub line_file: SourceLine,
}

// What: prove a target by deriving an impossibility from its negation.
// Surface: `by contra: …`
// Stores: the target fact when the contradiction closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByContraStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: AtomicFact,
    pub line_file: SourceLine,
}

// What: prove a forall by enumerating a finite set carrier.
// Surface: `by enumerate: forall x {…}: …`
// Stores: the forall when every element case closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByEnumerateFiniteSetStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
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
    pub line_file: SourceLine,
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
    pub line_file: SourceLine,
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
    pub line_file: SourceLine,
}

// What: prove object equality from both `$subset` directions (extensionality).
// Surface: `by extension: A = B`
// Stores: `A = B` as ordinary object equality in the pure-set model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByExtensionStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: prove function object equality from pointwise equality on a shared FnSet.
// Surface: `by fn_extension: f = g` (preview)
// Stores: `f = g` as ordinary object equality when carriers are alpha-equivalent
// and the reconstructed pointwise forall succeeds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByFnExtensionStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: expand numeric-range membership into equality cases.
// Surface: `expand: e $in range(…)` / `expand: e $in closed_range(…)` / `expand: e $in a...b`
// Stores: `e = a or e = b or …` when membership is already known.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandRangeStmt {
    pub element: Obj,
    pub range: ClosedRangeOrRange,
    pub line_file: SourceLine,
}

// What: apply Zorn's lemma with named order / bound / maximality props.
// Surface: `release zorn_lemma: set S, prop P, prop U, prop M:`
// Stores: `exist m S st {$M(m)}` using the supplied maximality prop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseZornLemmaStmt {
    pub set: Obj,
    pub prop_name: AtomicName,
    pub upper_bound_prop_name: AtomicName,
    pub maximal_prop_name: AtomicName,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: apply the axiom of choice to a family of nonempty sets.
// Surface: `release axiom_of_choice: set F`
// Stores: existence of a choice function for the family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseAxiomOfChoiceStmt {
    pub family: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: apply the axiom of regularity to a set.
// Surface: `release regularity_axiom(S)`
// Stores: the regularity conclusion for that set (strict mode rejects).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseRegularityAxiomStmt {
    pub set: Obj,
    pub line_file: SourceLine,
}

// What: prove an atomic fact by unfolding a concrete / builtin definition.
// Surface: `by def: $P(…)`
// Stores: the target with explicit definition provenance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByDefStmt {
    pub fact: AtomicFact,
    pub line_file: SourceLine,
}

// What: open one definition-owned struct layer (fields / bridges / laws).
// Surface: `release struct def e`
// Stores: one layer of tuple/identity bridges, field carriers, struct laws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseStructDefStmt {
    pub obj: Obj,
    pub line_file: SourceLine,
}

// What: re-store one object-definition's facts for an identifier (preview).
// Surface: `release obj def I`
// Stores: that definition's type / equality / body / fn facts under `I`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseObjDefStmt {
    pub name: IdentifierObj,
    pub line_file: SourceLine,
}

// What: cite a theorem and commit only one selected atomic conclusion.
// Surface: `by thm name(args): selected_fact`
// Stores: the selected atomic fact and ordinary inferred consequences.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByThmStmt {
    pub call: TheoremCall,
    pub selected_fact: AtomicFact,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// RegisterStmt
// -----------------------------------------------------------------------------

// Register rewrite / infer properties of a user prop (not a proof method).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegisterStmt {
    // Transitivity for later rewrite / chain infer.
    // Example: `register transitive: ? forall x, y, z … =>: $P(x, z)`.
    RegisterTransitivePropStmt(RegisterTransitivePropStmt),
    // Symmetry for later rewrite.
    // Example: `register symmetric: ? forall x, y … =>: $P(y, x)`.
    RegisterSymmetricPropStmt(RegisterSymmetricPropStmt),
    // Reflexivity for later rewrite.
    // Example: `register reflexive: ? forall x … =>: $P(x, x)`.
    RegisterReflexivePropStmt(RegisterReflexivePropStmt),
}

// What: register transitivity of a user prop for later rewrite / chain infer.
// Surface: `register transitive:` + one shaped `? forall …` (no proof body).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisterTransitivePropStmt {
    pub forall_fact: ForallFact,
    pub line_file: SourceLine,
}

// What: register symmetry of a user prop for later rewrite.
// Surface: `register symmetric:` + one shaped `? forall …` (no proof body).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisterSymmetricPropStmt {
    pub forall_fact: ForallFact,
    pub line_file: SourceLine,
}

// What: register reflexivity of a user prop for later rewrite.
// Surface: `register reflexive:` + one shaped `? forall …` (no proof body).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisterReflexivePropStmt {
    pub forall_fact: ForallFact,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// WitnessStmt
// -----------------------------------------------------------------------------

// Supply concrete witnesses for an exist / atomic / nonempty goal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessStmt {
    // Exist-shaped fact by exhibiting witnesses.
    // Example: `witness exist x R st {x = 0} from 0` or `… from 0:` with proof body.
    WitnessExistFact(WitnessExistFact),
    // `$P(…)` when its concrete def is a single positive exist clause.
    // Example: `witness $P(…) from a` or `… from a:` with proof body.
    WitnessAtomicFact(WitnessAtomicFact),
    // Nonemptiness by exhibiting a member.
    // Example: `witness $is_nonempty_set(S) from e` or `… from e:` with proof body.
    WitnessNonemptySet(WitnessNonemptySet),
}

// What: introduce an exist-shaped fact by exhibiting witnesses.
// Surface: `witness exist … from a, b` or `… from a, b:` + local proof body.
// Stores: the exist / exist! fact (binder names stay local; helpers stay in local_env).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessExistFact {
    pub equal_tos: Vec<Obj>,
    pub exist_shaped_fact_in_witness: ExistShapedFact,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: prove `$P(…)` when its concrete def is a single positive exist clause.
// Surface: `witness $P(…) from a` or `… from a:` + local proof body.
// Stores: `$P(…)` then ordinary definition inference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessAtomicFact {
    pub atomic_fact: NormalAtomicFact,
    pub witnesses: Vec<Obj>,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: prove a set is nonempty by exhibiting a member.
// Surface: `witness $is_nonempty_set(S) from e` or `… from e:` + local proof body.
// Stores: nonemptiness of `S`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessNonemptySet {
    pub obj: Obj,
    pub set: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// ProofBlockStmt
// -----------------------------------------------------------------------------

// Nested proof blocks that scope local work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofBlockStmt {
    // Prove a subgoal in a child scope; keep only that target.
    // Example: `claim: ? 1 = 1` then proof body.
    ClaimStmt(ClaimStmt),
    // Informal / non-binding sketch whose body still checks.
    // Example: `sketch: 1 = 1`.
    SketchStmt(SketchStmt),
}

// What: prove a subgoal in a child scope and keep only that target.
// Surface: `claim: ? fact` then proof body
// Stores: the target fact; helpers do not escape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimStmt {
    pub fact: Fact,
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// What: informal / non-binding proof sketch whose body still checks.
// Surface: `sketch:` …
// Stores: nothing outside the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SketchStmt {
    pub proof: Vec<Stmt>,
    pub line_file: SourceLine,
}

// -----------------------------------------------------------------------------
// CommandStmt
// -----------------------------------------------------------------------------

// Non-proof session commands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandStmt {
    // Evaluate an object for display (no new proof fact). Example: `eval 1 + 1`.
    EvalStmt(EvalStmt),
}

// What: evaluate an object for display (no new proof fact).
// Surface: `eval expr`
// Stores: evaluation output only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalStmt {
    pub obj_to_eval: Obj,
    pub line_file: SourceLine,
}
