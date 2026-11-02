import Litex.ElementaryFunctions

universe u
namespace Litex

/-- The checked source domain, decreasing rank, restricted self domain and
body interpretation. Certification is separate from mathematical identity. -/
structure RecursiveFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  rank : M.Value → ℕ
  recursiveDomain : M.Value → M.Value
  bodyValue : M.Value → M.Value → M.Value

namespace RecursiveFn
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def prefixGraph (r : RecursiveFn M) (x : M.Value)
    (values : M.Value → M.Value) : M.Value :=
  F.graphValue (r.recursiveDomain x) r.signature.output values

noncomputable def valueOf (output : M.Value) (rank : M.Value → ℕ)
    (recursiveDomain : M.Value → M.Value)
    (body : M.Value → M.Value → M.Value) : M.Value → M.Value := by
  classical
  exact (measure rank).wf.fix fun x previous =>
    body x (F.graphValue (recursiveDomain x) output (fun y =>
      if h : rank y < rank x then previous y h else M.number 0))

noncomputable def value (r : RecursiveFn M) : M.Value → M.Value :=
  valueOf r.signature.output r.rank r.recursiveDomain r.bodyValue

noncomputable def previousValues (r : RecursiveFn M) (x y : M.Value) : M.Value := by
  classical
  exact if r.rank y < r.rank x then r.value y else M.number 0

theorem value_eq (r : RecursiveFn M) (x : M.Value) :
    r.value x = r.bodyValue x (r.prefixGraph x (r.previousValues x)) := by
  classical
  rw [value, valueOf, WellFounded.fix_eq]
  rfl

/-- Each premise is discharged from retained source evidence: smaller recursive
calls, body WD/return membership, and congruence on those exact call inputs. -/
structure Certified (r : RecursiveFn M) : Prop where
  domainSound : ∀ x y, M.mem x r.signature.domain → M.mem y (r.recursiveDomain x) →
    M.mem y r.signature.domain ∧ r.rank y < r.rank x
  bodyReturn : ∀ x prefixFn, M.mem x r.signature.domain →
    M.mem prefixFn (F.fnSetValue (r.recursiveDomain x) r.signature.output) →
    M.mem (r.bodyValue x prefixFn) r.signature.output
  bodyCongr : ∀ x f g, M.mem x r.signature.domain →
    M.mem f (F.fnSetValue (r.recursiveDomain x) r.signature.output) →
    (∀ y, M.mem y (r.recursiveDomain x) → F.callValue f y = F.callValue g y) →
    r.bodyValue x f = r.bodyValue x g

theorem value_mem (r : RecursiveFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x r.signature.domain) :
    M.mem (r.value x) r.signature.output := by
  classical
  induction x using (measure r.rank).wf.induction with
  | h x ih =>
    rw [r.value_eq]
    apply h.bodyReturn x _ hx
    apply FunctionSemantics.graph_inFnSet
    intro y hy
    obtain ⟨hyDomain, hyRank⟩ := h.domainSound x y hx hy
    simpa only [previousValues, if_pos hyRank] using ih y hyRank hyDomain

theorem previousValues_mem (r : RecursiveFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x r.signature.domain) :
    ∀ y, M.mem y (r.recursiveDomain x) →
      M.mem (r.previousValues x y) r.signature.output := by
  classical
  intro y hy
  obtain ⟨hyDomain, hyRank⟩ := h.domainSound x y hx hy
  simpa only [previousValues, if_pos hyRank] using r.value_mem h y hyDomain

noncomputable def graph (r : RecursiveFn M) : M.Value :=
  F.graphValue r.signature.domain r.signature.output r.value

theorem graph_mem (r : RecursiveFn M) (h : r.Certified) :
    M.mem r.graph (F.fnSetValue r.signature.domain r.signature.output) :=
  FunctionSemantics.graph_inFnSet _ _ _ (r.value_mem h)

theorem call_graph (r : RecursiveFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x r.signature.domain) :
    F.callValue r.graph x = r.value x :=
  FunctionSemantics.call_graphValue _ _ _ (r.value_mem h) x hx

theorem equation (r : RecursiveFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x r.signature.domain) :
    F.callValue r.graph x = r.bodyValue x r.graph := by
  classical
  rw [r.call_graph h x hx, r.value_eq]
  apply h.bodyCongr x _ _ hx
    (FunctionSemantics.graph_inFnSet _ _ _ (r.previousValues_mem h x hx))
  intro y hy
  obtain ⟨hyDomain, hyRank⟩ := h.domainSound x y hx hy
  rw [FunctionSemantics.call_graphValue _ _ _
    (r.previousValues_mem h x hx) y hy]
  simpa only [previousValues, if_pos hyRank] using (r.call_graph h y hyDomain).symm

end RecursiveFn

namespace NativeBridge
variable {M : Semantics.{u}}

theorem integerValue_le_of_raw (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer))
    (h : ∃ x y : ℝ, a = M.number (x : ℂ) ∧ b = M.number (y : ℂ) ∧ x ≤ y) :
    integerValue a ≤ integerValue b := by
  have ha' : a = M.number ((integerValue a : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using integerValue_spec a ha
  have hb' : b = M.number ((integerValue b : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using integerValue_spec b hb
  have h' := (le_iff_ofDenoteReal
    (semanticObject a (M.member_isSet ha)) (semanticObject b (M.member_isSet hb))
    (integerValue a : ℝ) (integerValue b : ℝ) ha' hb').mp h
  exact_mod_cast h'

theorem integerValue_lt_of_raw (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer))
    (h : ∃ x y : ℝ, a = M.number (x : ℂ) ∧ b = M.number (y : ℂ) ∧ x < y) :
    integerValue a < integerValue b := by
  have ha' : a = M.number ((integerValue a : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using integerValue_spec a ha
  have hb' : b = M.number ((integerValue b : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using integerValue_spec b hb
  have h' := (lt_iff_ofDenoteReal
    (semanticObject a (M.member_isSet ha)) (semanticObject b (M.member_isSet hb))
    (integerValue a : ℝ) (integerValue b : ℝ) ha' hb').mp h
  exact_mod_cast h'

/-- The source requires a strictly smaller integer measure and a lower bound
that does not decrease. Its nonnegative difference is a well-founded rank. -/
theorem integerRank_decreases (measure lower nextMeasure nextLower : M.Value)
    (hm : M.mem measure (M.standard .integer))
    (hb : M.mem lower (M.standard .integer))
    (hn : M.mem nextMeasure (M.standard .integer))
    (hc : M.mem nextLower (M.standard .integer))
    (hsmaller : ∃ x y : ℝ, nextMeasure = M.number (x : ℂ) ∧
      measure = M.number (y : ℂ) ∧ x < y)
    (hbounded : ∃ x y : ℝ, nextLower = M.number (x : ℂ) ∧
      nextMeasure = M.number (y : ℂ) ∧ x ≤ y)
    (hlower : ∃ x y : ℝ, lower = M.number (x : ℂ) ∧
      nextLower = M.number (y : ℂ) ∧ x ≤ y) :
    (integerValue nextMeasure - integerValue nextLower).toNat <
      (integerValue measure - integerValue lower).toNat := by
  have hs := integerValue_lt_of_raw nextMeasure measure hn hm hsmaller
  have hbnd := integerValue_le_of_raw nextLower nextMeasure hc hn hbounded
  have hlo := integerValue_le_of_raw lower nextLower hb hc hlower
  omega

end NativeBridge

noncomputable instance recursiveFnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] : Representation M (RecursiveFn M) where
  wd r := r.Certified
  denote r := r.graph
  wd_isSet {r} h := M.member_isSet (r.graph_mem h)

noncomputable def recursiveFn {M : Semantics.{u}} [F : FunctionSemantics M]
    (data : RecursiveFn M) (checked : data.Certified) : Obj (M := M) (RecursiveFn M) :=
  ⟨data, checked⟩

theorem recursiveFnInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveFn M)) : In f (fnSet f.val.signature) :=
  f.val.graph_mem f.wd

theorem recursiveFn_equation {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveFn M)) (x : M.Value)
    (hx : M.mem x f.val.signature.domain) :
    F.callValue (denote f) x = f.val.bodyValue x (denote f) :=
  f.val.equation f.wd x hx

end Litex

