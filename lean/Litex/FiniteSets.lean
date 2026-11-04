import Litex.OrderedArithmetic

universe u v w x

namespace Litex

open Lean Elab Tactic in
/-- Fixed coordinate normalization for the verifier's Complex polynomial tag.
Each stage runs only on remaining goals; the produced proof is kernel checked. -/
elab "litex_normalize_complex" : tactic => do
  evalTactic (← `(tactic| apply Complex.ext))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals norm_num [pow_succ]))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals ring!))

open Lean Elab Tactic Lean.Parser.Tactic in
/-- Check the selected guarded complex certificate with its supplied nonzero proofs. -/
elab "litex_normalize_guarded_complex" d:discharger : tactic => do
  evalTactic (← `(tactic| field_simp $d))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| litex_normalize_complex))

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

def IsRange (f r : M.Value) : Prop :=
  M.isSet r ∧ ∀ y, M.mem y r ↔ ∃ a, M.mem (F.pairValue a y) f

/-- The range depends only on the graph, independently of which signature certifies it. -/
noncomputable def rangeValue (f : M.Value) : M.Value :=
  by classical exact if h : ∃ r, IsRange f r then Classical.choose h else F.emptyValue

theorem range_spec {D B f : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) : IsRange f (rangeValue f) := by
  have exists_range : ∃ r, IsRange f r := by
    refine ⟨F.sepValue B (fun y => ∃ a, M.mem (F.pairValue a y) f), F.sep_isSet _ _ hB, ?_⟩
    intro y
    rw [F.sep_members]
    constructor
    · exact And.right
    · intro h
      obtain ⟨a, ha⟩ := h
      obtain ⟨x, _, z, hz, eq⟩ := ((F.fnSet_members D B f).mp hf).1 _ ha
      have hy : M.mem y B := (F.pair_injective eq).2.symm ▸ hz
      exact ⟨hy, a, ha⟩
  simpa only [rangeValue, dif_pos exists_range] using Classical.choose_spec exists_range

theorem range_mem_iff {D B f y : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) :
    M.mem y (rangeValue f) ↔ ∃ a, M.mem a D ∧ y = F.callValue f a := by
  rw [(range_spec hB hf).2 y]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, F.call_graph D B f a ((F.fnSet_members D B f).mp hf) ha⟩

theorem range_subset {D B f y : M.Value} (hB : M.isSet B)
    (hf : M.mem f (F.fnSetValue D B)) (hy : M.mem y (rangeValue f)) : M.mem y B := by
  obtain ⟨a, ha, rfl⟩ := (range_mem_iff hB hf).mp hy
  exact call_mem D B f a hf ha
end FunctionSemantics

structure FunctionRange {M : Semantics.{u}} (α : Type v) [Representation M α] where
  function : Obj (M := M) α

noncomputable instance functionRangeRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (FunctionRange (M := M) α) where
  wd r := ∃ s : FunctionSignature M, In r.function (fnSet s)
  denote r := FunctionSemantics.rangeValue (denote r.function)
  wd_isSet h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.range_spec s.output_isSet hs).1

noncomputable def fnRange {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α)
    (s : FunctionSignature M) (hf : In f (fnSet s)) : Obj (M := M) (FunctionRange (M := M) α) :=
  ⟨⟨f⟩, ⟨s, hf⟩⟩

theorem fnRangeEmptyOfDomainEmpty {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α)
    (s : FunctionSignature M) (hf : In f (fnSet s))
    (empty : ∀ a, ¬ M.mem a s.domain) :
    Same (fnRange f s hf) (emptySet (M := M)) := by
  change FunctionSemantics.rangeValue (denote f) = F.emptyValue
  apply F.ext _ _ (FunctionSemantics.range_spec s.output_isSet hf).1 F.empty_isSet
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, _⟩ := (FunctionSemantics.range_mem_iff s.output_isSet hf).mp hy
    exact (empty a ha).elim
  · intro hy
    exact (F.empty_members y hy).elim

theorem functionGraphEmptyOfDomainEmpty {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α)
    (s : FunctionSignature M) (hf : In f (fnSet s))
    (empty : ∀ a, ¬ M.mem a s.domain) :
    Same f (emptySet (M := M)) := by
  change denote f = F.emptyValue
  apply F.ext _ _ (M.member_isSet hf) F.empty_isSet
  intro p
  constructor
  · intro hp
    obtain ⟨a, ha, _⟩ := ((F.fnSet_members s.domain s.target _).mp hf).1 p hp
    exact (empty a ha).elim
  · intro hp
    exact (F.empty_members p hp).elim

theorem functionSpaceSingletonOfEmptyDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (s : FunctionSignature M) (empty : ∀ a, ¬ M.mem a s.domain) :
    denote (fnSet s) = F.insertValue F.emptyValue F.emptyValue := by
  change F.fnSetValue s.domain s.target = _
  apply F.ext _ _ (isSet (fnSet s))
    (F.insert_isSet _ _ F.empty_isSet F.empty_isSet)
  intro f
  constructor
  · intro hf
    have same : f = F.emptyValue :=
      functionGraphEmptyOfDomainEmpty
        (semanticObject (M := M) f (M.member_isSet hf)) s hf empty
    exact (F.insert_members _ _ _).mpr (Or.inl same)
  · intro hf
    rcases (F.insert_members _ _ _).mp hf with same | impossible
    · rw [same]
      apply (F.fnSet_members s.domain s.target _).mpr
      constructor
      · intro p hp
        exact (F.empty_members p hp).elim
      · intro a ha
        exact (empty a ha).elim
    · exact (F.empty_members f impossible).elim


theorem emptyTupleDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    (t : Obj (M := M) (TupleObj M 0)) : denote t = F.emptyValue := by
  rfl


theorem cartZeroEqFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    (c : Obj (M := M) (CartObj M 0)) : Same c (fnSet (cartCompleteSignature c)) := by
  apply cartZeroSame c (fnSet (cartCompleteSignature c))
  change F.fnSetValue (finiteSeqDomain (number ((0 : ℕ) : ℂ)))
    (FiniteFunction.orderedUnionValue (List.ofFn c.val.factors)) = _
  rw [finiteSeqDomain_number]
  rfl

theorem fnRangeSingletonOfConstantCalls {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (c : Obj (M := M) β) (s : FunctionSignature M)
    (hf : In f (fnSet s)) (inhabited : ∃ a, M.mem a s.domain)
    (constant : ∀ a, M.mem a s.domain → F.callValue (denote f) a = denote c) :
    denote (fnRange f s hf) = F.insertValue (denote c) F.emptyValue := by
  change F.rangeValue (denote f) = _
  apply F.ext _ _ (F.range_spec s.output_isSet hf).1
    (F.insert_isSet _ _ (isSet c) F.empty_isSet)
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, same⟩ := (F.range_mem_iff s.output_isSet hf).mp hy
    exact (F.insert_members _ _ _).mpr (Or.inl (same.trans (constant a ha)))
  · intro hy
    rcases (F.insert_members _ _ _).mp hy with same | impossible
    · obtain ⟨a, ha⟩ := inhabited
      exact (F.range_mem_iff s.output_isSet hf).mpr
        ⟨a, ha, same.trans (constant a ha).symm⟩
    · exact (F.empty_members y impossible).elim

theorem inFnRange_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (FunctionRange (M := M) α)) (y : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In r.val.function (fnSet s)) :
    In y r ↔ ∃ a : Obj (M := M) M.Value, ∃ (_ha : M.mem (denote a) s.domain),
      denote y = F.callValue (denote r.val.function) (denote a) := by
  change M.mem (denote y) (FunctionSemantics.rangeValue (denote r.val.function)) ↔ _
  rw [FunctionSemantics.range_mem_iff s.output_isSet hf]
  constructor
  · rintro ⟨a, ha, eq⟩
    exact ⟨semanticObject a (M.member_isSet ha), ha, eq⟩
  · rintro ⟨a, ha, eq⟩
    exact ⟨denote a, ha, eq⟩

theorem fnRangeInOutput {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (FunctionRange (M := M) α)) (y : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In r.val.function (fnSet s)) (hy : In y r) :
    M.mem (denote y) s.output := FunctionSemantics.range_subset s.output_isSet hf hy

theorem callOnInFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (denote c.val.argument))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.signature.output_isSet c.wd.1).mpr
    ⟨denote c.val.argument, c.wd.2, rfl⟩

theorem callInFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (denote c.val.argument))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.output_isSet c.wd.1).mpr
    ⟨denote c.val.argument, (FunctionSignature.oneTarget_domain _ _ _ _ _).mpr c.wd.2, rfl⟩

theorem call2InFnRange {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ))
    (r : Obj (M := M) (FunctionRange (M := M) α))
    (same : Same c.val.function r.val.function) : In c r := by
  change M.mem (F.callValue (denote c.val.function) (FiniteFunction.pack2 (denote c.val.first) (denote c.val.second)))
    (FunctionSemantics.rangeValue (denote r.val.function))
  rw [← same]
  exact (FunctionSemantics.range_mem_iff c.val.output_isSet c.wd.1).mpr
    ⟨FiniteFunction.pack2 (denote c.val.first) (denote c.val.second),
      (FunctionSignature.twoTarget_domain _ _ _ _ _ _ _).mpr c.wd.2, rfl⟩

end Litex

namespace Litex

structure RangeObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  start : Obj (M := M) α
  finish : Obj (M := M) β

def RangeObj.condition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (r : RangeObj (M := M) α β) (value : M.Value) : Prop :=
  ∃ lower upper k : ℤ, denote r.start = M.number (lower : ℂ) ∧
    denote r.finish = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
    lower ≤ k ∧ k < upper

instance rangeRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (RangeObj (M := M) α β) where
  wd r := In r.start Z ∧ In r.finish Z
  denote r := S.sepValue (M.standard .integer) r.condition
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .integer)

def range {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a Z) (hb : In b Z) :
    Obj (M := M) (RangeObj (M := M) α β) := ⟨⟨a, b⟩, ⟨ha, hb⟩⟩

theorem inRange_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) :
    In p (range a b ha hb) ↔
      ∃ lower upper k : ℤ, denote a = M.number (lower : ℂ) ∧
        denote b = M.number (upper : ℂ) ∧ denote p = M.number (k : ℂ) ∧
        lower ≤ k ∧ k < upper := by
  change M.mem (denote p) (S.sepValue (M.standard .integer) _) ↔ _
  rw [S.sep_members]
  constructor
  · exact fun h => h.2
  · rintro ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k, hp⟩, lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem inRangeOfDenote {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (lower upper k : ℤ)
    (hl : denote a = M.number (lower : ℂ))
    (hu : denote b = M.number (upper : ℂ))
    (hp : denote p = M.number (k : ℂ)) (hlo : lower ≤ k) (hhi : k < upper) :
    In p (range a b ha hb) :=
  (inRange_iff a b p ha hb).mpr ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem numberInRange {M : Semantics.{u}} [SetSemantics M]
    (lower upper k : ℤ) (hlo : lower ≤ k) (hhi : k < upper) :
    In (number (M := M) (k : ℂ))
      (range (number (lower : ℂ)) (number (upper : ℂ))
        (NativeBridge.numberInZ lower) (NativeBridge.numberInZ upper)) :=
  inRangeOfDenote _ _ _ _ _ lower upper k rfl rfl rfl hlo hhi

theorem numberInRangeOfEq {M : Semantics.{u}} [SetSemantics M]
    (a b p : ℂ) (lower upper k : ℤ)
    (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ)) (hp : p = (k : ℂ))
    (hlo : lower ≤ k) (hhi : k < upper) :
    In (number (M := M) p)
      (range (number a) (number b)
        (NativeBridge.numberInZOfEq a lower ha) (NativeBridge.numberInZOfEq b upper hb)) :=
  inRangeOfDenote _ _ _ _ _ lower upper k
    (congrArg M.number ha) (congrArg M.number hb) (congrArg M.number hp) hlo hhi


theorem integerPositiveOfWitness {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) α) (k : ℤ)
    (hk : denote p = M.number (k : ℂ)) (hpos : 0 < k) : In p NPos := by
  apply (S.sep_members _ _ _).mpr
  have hn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hpos)
  refine ⟨(M.natural_members _).mpr ⟨k.toNat, ?_⟩, (k : ℝ), ?_, ?_⟩
  · exact hk.trans (congrArg M.number (by exact_mod_cast hn.symm))
  · simpa only [Complex.ofReal_intCast] using hk
  · exact_mod_cast hpos

theorem inClosedRangeInteger {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower upper : ℤ)
    (hl : denote r.val.start = M.number (lower : ℂ))
    (hu : denote r.val.finish = M.number (upper : ℂ)) (h : In p r) :
    ∃ k : ℤ, Same p (number (k : ℂ)) ∧ lower ≤ k ∧ k ≤ upper := by
  obtain ⟨l, u, k, ha, hb, hp, hlo, hhi⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  have hb' : u = upper := by exact_mod_cast M.number_injective (hb.symm.trans hu)
  subst l
  subst u
  exact ⟨k, hp, hlo, hhi⟩

theorem inClosedRangeBounds {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (h : In p r) : In p Z ∧ Le r.val.start p ∧ Le p r.val.finish := by
  obtain ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  refine ⟨(M.integer_members _).mpr ⟨k, hp⟩, ?_, ?_⟩
  · refine ⟨(lower : ℝ), (k : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hl
    · simpa only [Complex.ofReal_intCast] using hp
    · exact_mod_cast hlo
  · refine ⟨(k : ℝ), (upper : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hp
    · simpa only [Complex.ofReal_intCast] using hu
    · exact_mod_cast hhi

theorem inClosedRangePositive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower : ℤ) (hl : denote r.val.start = M.number (lower : ℂ))
    (hpos : 0 < lower) (h : In p r) : In p NPos := by
  obtain ⟨l, upper, k, ha, _, hp, hlo, _⟩ :=
    (inClosedRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  subst l
  exact integerPositiveOfWitness p k hp (lt_of_lt_of_le hpos hlo)

theorem inRangeInteger {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower upper : ℤ)
    (hl : denote r.val.start = M.number (lower : ℂ))
    (hu : denote r.val.finish = M.number (upper : ℂ)) (h : In p r) :
    ∃ k : ℤ, Same p (number (k : ℂ)) ∧ lower ≤ k ∧ k < upper := by
  obtain ⟨l, u, k, ha, hb, hp, hlo, hhi⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  have hb' : u = upper := by exact_mod_cast M.number_injective (hb.symm.trans hu)
  subst l
  subst u
  exact ⟨k, hp, hlo, hhi⟩

theorem inRangeBounds {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (h : In p r) : In p Z ∧ Le r.val.start p ∧ Lt p r.val.finish := by
  obtain ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  refine ⟨(M.integer_members _).mpr ⟨k, hp⟩, ?_, ?_⟩
  · refine ⟨(lower : ℝ), (k : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hl
    · simpa only [Complex.ofReal_intCast] using hp
    · exact_mod_cast hlo
  · refine ⟨(k : ℝ), (upper : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using hp
    · simpa only [Complex.ofReal_intCast] using hu
    · exact_mod_cast hhi

theorem inRangePositive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (r : Obj (M := M) (RangeObj (M := M) α β)) (p : Obj (M := M) γ)
    (lower : ℤ) (hl : denote r.val.start = M.number (lower : ℂ))
    (hpos : 0 < lower) (h : In p r) : In p NPos := by
  obtain ⟨l, upper, k, ha, _, hp, hlo, _⟩ :=
    (inRange_iff r.val.start r.val.finish p r.wd.1 r.wd.2).mp h
  have ha' : l = lower := by exact_mod_cast M.number_injective (ha.symm.trans hl)
  subst l
  exact integerPositiveOfWitness p k hp (lt_of_lt_of_le hpos hlo)

/-! Weak additive shifts consume an ordered bound and a signed addend. -/

theorem leAddOfLeOfNonneg {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.left) (hb : Le (number 0) p.val.right) : Le a p := by
  obtain ⟨a', x', ha', hx', hax⟩ := ha
  obtain ⟨z', y', hz', hy', hzy⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, le_trans hax (le_add_of_nonneg_right (hz0 ▸ hzy))⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem leAddOfLeOfNonnegSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.right) (hb : Le (number 0) p.val.left) : Le a p := by
  obtain ⟨a', y', ha', hy', hay⟩ := ha
  obtain ⟨z', x', hz', hx', hzx⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, le_trans hay (le_add_of_nonneg_left (hz0 ▸ hzx))⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeOfLeOfNonpos {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (a : Obj (M := M) γ)
    (ha : Le p.val.left a) (hb : Le p.val.right (number 0)) : Le p a := by
  obtain ⟨x', a', hx', ha', hxa⟩ := ha
  obtain ⟨y', z', hy', hz', hyz⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨x' + y', a', ?_, ha', le_trans (add_le_of_nonpos_right (hz0 ▸ hyz)) hxa⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeOfLeOfNonposSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (a : Obj (M := M) γ)
    (ha : Le p.val.right a) (hb : Le p.val.left (number 0)) : Le p a := by
  obtain ⟨y', a', hy', ha', hya⟩ := ha
  obtain ⟨x', z', hx', hz', hxz⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨x' + y', a', ?_, ha', le_trans (add_le_of_nonpos_left (hz0 ▸ hxz)) hya⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [hx', hy', M.add_numbers, Complex.ofReal_add]

theorem addLeAdd {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.left) (h₂ : Le p.val.right q.val.right) : Le p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_le_add hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addLeAddSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.right) (h₂ : Le p.val.right q.val.left) : Le p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, d + b, ?_, ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hd, hb, M.add_numbers, Complex.ofReal_add]
  · simpa only [add_comm b d] using add_le_add hab hcd

theorem addLtAddOfLtOfLe {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.left) (h₂ : Le p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add_of_lt_of_le hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addLtAddOfLeOfLt {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Le p.val.left q.val.left) (h₂ : Lt p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add_of_le_of_lt hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem subStructuralLeRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Le lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hdiff : (a : ℂ) - z = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.sub_numbers] using hr
  have hc : denote lhs.val.right = M.number ((a - r : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (by
      calc z = (a : ℂ) - ((a : ℂ) - z) := (sub_sub_cancel _ _).symm
           _ = (a : ℂ) - (r : ℂ) := congrArg (fun t : ℂ => (a : ℂ) - t) hdiff)
  refine NativeBridge.leOfDenoteReal lhs rhs (a - (a - r)) (b - (a - r)) ?_ ?_ (sub_le_sub_right hab (a - r))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, ha, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, hb, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLeLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Le rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Le lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hdiff : z - (b : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, hb, M.sub_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r + b : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_add]
    exact congrArg M.number (sub_eq_iff_eq_add.mp hdiff)
  refine NativeBridge.leOfDenoteReal lhs rhs ((r + b) - b) ((r + b) - a) ?_ ?_ (sub_le_sub_left hab (r + b))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, hb, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, ha, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Lt lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hdiff : (a : ℂ) - z = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.sub_numbers] using hr
  have hc : denote lhs.val.right = M.number ((a - r : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (by
      calc z = (a : ℂ) - ((a : ℂ) - z) := (sub_sub_cancel _ _).symm
           _ = (a : ℂ) - (r : ℂ) := congrArg (fun t : ℂ => (a : ℂ) - t) hdiff)
  refine NativeBridge.ltOfDenoteReal lhs rhs (a - (a - r)) (b - (a - r)) ?_ ?_ (sub_lt_sub_right hab (a - r))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, ha, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, hb, M.sub_numbers, Complex.ofReal_sub]

theorem subStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (SubObj (M := M) α β))
    (rhs : Obj (M := M) (SubObj (M := M) γ δ))
    (hDiff : In lhs R) (hOrder : Lt rhs.val.right lhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hDiff
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hdiff : z - (b : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, hb, M.sub_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r + b : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_add]
    exact congrArg M.number (sub_eq_iff_eq_add.mp hdiff)
  refine NativeBridge.ltOfDenoteReal lhs rhs ((r + b) - b) ((r + b) - a) ?_ ?_ (sub_lt_sub_left hab (r + b))
  · change M.subValue (denote lhs.val.left) (denote lhs.val.right) = _
    simp only [hc, hb, M.sub_numbers, Complex.ofReal_sub]
  · change M.subValue (denote rhs.val.left) (denote rhs.val.right) = _
    simp only [hSame.symm.trans hc, ha, M.sub_numbers, Complex.ofReal_sub]

structure IntersectObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance intersectRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (IntersectObj (M := M) α β) where
  wd _ := True
  denote p := S.sepValue (denote p.left) (fun x => M.mem x (denote p.right))
  wd_isSet {p} _ := S.sep_isSet _ _ (isSet p.left)

def intersect {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (IntersectObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inIntersect_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (intersect A B) ↔ In a A ∧ In a B := S.sep_members _ _ _

/-- Optional foundation law; the ZF interpretation proves this below. -/
class RegularitySemantics (M : Semantics.{u}) where
  regularity : ∀ A, M.isSet A → (∃ x, M.mem x A) →
    ∃ x, M.mem x A ∧ ∀ y, M.mem y x → ¬ M.mem y A

noncomputable instance numericRegularitySemantics : RegularitySemantics NumericModel.model where
  regularity := fun (A : ZFSet.{0}) _ h => by
    change (∃ x : ZFSet.{0}, x ∈ A) at h
    change ∃ x : ZFSet.{0}, x ∈ A ∧ ∀ y : ZFSet.{0}, y ∈ x → ¬ y ∈ A
    have hA : A ≠ (∅ : ZFSet.{0}) := by
      rintro rfl
      obtain ⟨x, hx⟩ := h
      exact ZFSet.notMem_empty x hx
    obtain ⟨x, hx, disjoint⟩ := ZFSet.regularity A hA
    refine ⟨x, hx, ?_⟩
    intro y hy hAy
    have hm : y ∈ A ∩ x := ZFSet.mem_inter.mpr ⟨hAy, hy⟩
    rw [disjoint] at hm
    exact ZFSet.notMem_empty y hm

theorem regularity {M : Semantics.{u}} [S : SetSemantics M] [R : RegularitySemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (hA : IsNonempty A) :
    ∃ x : Obj (M := M) M.Value, ∃ (_ : In x A), Same (intersect x A) emptySet := by
  obtain ⟨x, hx, disjoint⟩ := R.regularity (denote A) (isSet A) hA
  let a := semanticObject x (M.member_isSet hx)
  refine ⟨a, hx, ?_⟩
  apply S.ext _ _ (isSet (intersect a A)) (isSet emptySet)
  intro y
  constructor
  · intro hy
    obtain ⟨hya, hyA⟩ := (S.sep_members _ _ _).mp hy
    exact False.elim (disjoint y hya hyA)
  · intro hy
    exact False.elim (S.empty_members y hy)

theorem intersectSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (intersect A B) A :=
  fun x h => ((S.sep_members _ _ x).mp h).1

theorem intersectSubsetRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (intersect A B) B :=
  fun x h => ((S.sep_members _ _ x).mp h).2

theorem intersectSubsetOfLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) : Subset (intersect A B) D :=
  fun x h => hAD x ((S.sep_members _ _ x).mp h).1

theorem intersectSubsetOfRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hBD : Subset B D) : Subset (intersect A B) D :=
  fun x h => hBD x ((S.sep_members _ _ x).mp h).2

theorem subsetIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (D : Obj (M := M) γ) (A : Obj (M := M) α) (B : Obj (M := M) β)
    (hDA : Subset D A) (hDB : Subset D B) : Subset D (intersect A B) :=
  fun x h => (S.sep_members _ _ x).mpr ⟨hDA x h, hDB x h⟩

theorem intersectComm {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect A B) (intersect B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (denote B))) ↔ M.mem z (S.sepValue (denote B) (fun t => M.mem t (denote A)))
  simp only [S.sep_members, and_comm]

theorem intersectIdem {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect A A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (denote A))) ↔ M.mem z (denote A)
  simp only [S.sep_members, and_self]

theorem intersectEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect A (emptySet (M := M))) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t S.emptyValue)) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, and_false]

theorem intersectEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (intersect (emptySet (M := M)) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue S.emptyValue (fun t => M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, false_and]

theorem intersectAssoc {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (intersect (intersect A B) C) (intersect A (intersect B C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => M.mem t (denote B))) (fun t => M.mem t (denote C))) ↔ M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.sepValue (denote B) (fun t => M.mem t (denote C)))))
  simp only [S.sep_members, and_assoc]

theorem unionComm {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (union A B) (union B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (denote B)) ↔ M.mem z (S.unionValue (denote B) (denote A))
  simp only [S.union_members, or_comm]

theorem unionIdem {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union A A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (denote A)) ↔ M.mem z (denote A)
  simp only [S.union_members, or_self]

theorem unionEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union A (emptySet (M := M))) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) S.emptyValue) ↔ M.mem z (denote A)
  simp only [S.union_members, S.empty_members, or_false]

theorem unionEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (union (emptySet (M := M)) A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue S.emptyValue (denote A)) ↔ M.mem z (denote A)
  simp only [S.union_members, S.empty_members, false_or]

theorem unionAssoc {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (union (union A B) C) (union A (union B C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (S.unionValue (denote A) (denote B)) (denote C)) ↔ M.mem z (S.unionValue (denote A) (S.unionValue (denote B) (denote C)))
  simp only [S.union_members, or_assoc]

theorem intersectUnionDistrib {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) : Same (intersect A (union B C)) (union (intersect A B) (intersect A C)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.unionValue (denote B) (denote C)))) ↔ M.mem z (S.unionValue (S.sepValue (denote A) (fun t => M.mem t (denote B))) (S.sepValue (denote A) (fun t => M.mem t (denote C))))
  simp only [S.sep_members, S.union_members, and_or_left]

theorem intersectOfSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) : Same (intersect A B) A :=
  setExt _ _ (intersectSubsetLeft A B)
    (subsetIntersect A A B (subsetRefl A) h)

theorem intersectOfSubsetRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset B A) : Same (intersect A B) B :=
  setExt _ _ (intersectSubsetRight A B)
    (subsetIntersect B A B h (subsetRefl B))

theorem intersectCongr {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAD : Same A D) (hBE : Same B E) : Same (intersect A B) (intersect D E) := by
  change S.sepValue (denote A) (fun t => M.mem t (denote B)) =
    S.sepValue (denote D) (fun t => M.mem t (denote E))
  rw [hAD, hBE]

theorem unionIntersectDistrib {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (union A (intersect B D)) (intersect (union A B) (union A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.unionValue (denote A) (S.sepValue (denote B) (fun t => M.mem t (denote D)))) ↔
    M.mem z (S.sepValue (S.unionValue (denote A) (denote B)) (fun t => M.mem t (S.unionValue (denote A) (denote D))))
  simp only [S.sep_members, S.union_members, or_and_left]

structure SetMinusObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance setMinusRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SetMinusObj (M := M) α β) where
  wd _ := True
  denote p := S.sepValue (denote p.left) (fun t => ¬ M.mem t (denote p.right))
  wd_isSet {p} _ := S.sep_isSet _ _ (isSet p.left)

def setMinus {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (SetMinusObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inSetMinus_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (setMinus A B) ↔ In a A ∧ ¬ In a B := S.sep_members _ _ _

theorem setMinusSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Subset (setMinus A B) A :=
  fun z h => ((S.sep_members _ _ z).mp h).1

theorem notInSetMinusOfRight {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : In a B) : ¬ In a (setMinus A B) :=
  fun hx => ((inSetMinus_iff a A B).mp hx).2 h

theorem notInSetMinusOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) : ¬ In a (setMinus A B) :=
  fun hx => h ((inSetMinus_iff a A B).mp hx).1

theorem setMinusSelf {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus A A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, and_not_self]

theorem setMinusEmptyRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus A (emptySet (M := M))) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t S.emptyValue)) ↔ M.mem z (denote A)
  simp only [S.sep_members, S.empty_members, not_false_eq_true, and_true]

theorem setMinusEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v}
    [Representation M α]
    (A : Obj (M := M) α) : Same (setMinus (emptySet (M := M)) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue S.emptyValue (fun t => ¬ M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members, false_and]

theorem setMinusUnion {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) : Same (setMinus A (union B D)) (intersect (setMinus A B) (setMinus A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote B) (denote D)))) ↔ M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => M.mem t (S.sepValue (denote A) (fun t => ¬ M.mem t (denote D)))))
  simp only [S.sep_members, S.union_members, not_or]
  constructor
  · intro h; exact ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩
  · intro h; exact ⟨h.1.1, h.1.2, h.2.2⟩

theorem setMinusIntersect {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) : Same (setMinus A (intersect B D)) (union (setMinus A B) (setMinus A D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.sepValue (denote B) (fun t => M.mem t (denote D))))) ↔ M.mem z (S.unionValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (S.sepValue (denote A) (fun t => ¬ M.mem t (denote D))))
  simp only [S.sep_members, S.union_members, not_and_or, and_or_left]

theorem intersectSetMinusEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect A (setMinus B A)) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A))))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members]
  exact ⟨fun h => h.2.2 h.1, False.elim⟩

theorem setMinusIntersectEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Same (intersect (setMinus B A) A) (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A))) (fun t => M.mem t (denote A))) ↔ M.mem z S.emptyValue
  simp only [S.sep_members, S.empty_members]
  exact ⟨fun h => h.1.2 h.2, False.elim⟩

theorem setMinusChain {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (setMinus (setMinus A B) D) (setMinus A (union B D)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => ¬ M.mem t (denote D))) ↔
    M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote B) (denote D))))
  simp only [S.sep_members, S.union_members, not_or, and_assoc]

theorem setMinusChainSwap {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ) :
    Same (setMinus (setMinus A B) D) (setMinus A (union D B)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (S.sepValue (denote A) (fun t => ¬ M.mem t (denote B))) (fun t => ¬ M.mem t (denote D))) ↔
    M.mem z (S.sepValue (denote A) (fun t => ¬ M.mem t (S.unionValue (denote D) (denote B))))
  simp only [S.sep_members, S.union_members, not_or]
  exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem notInIntersectOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) : ¬ In a (intersect A B) :=
  fun hx => h ((inIntersect_iff a A B).mp hx).1

theorem notInIntersectOfRight {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a B) : ¬ In a (intersect A B) :=
  fun hx => h ((inIntersect_iff a A B).mp hx).2

theorem notInUnion {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (hA : ¬ In a A) (hB : ¬ In a B) : ¬ In a (union A B) :=
  fun hx => ((inUnion_iff a A B).mp hx).elim hA hB

theorem subsetTrans {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAB : Subset A B) (hBD : Subset B D) : Subset A D :=
  fun z hz => hBD z (hAB z hz)

theorem unionSubsetOfBoth {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) (hBD : Subset B D) : Subset (union A B) D :=
  fun z hz => ((S.union_members _ _ z).mp hz).elim (hAD z) (hBD z)

theorem unionMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAD : Subset A D) (hBE : Subset B E) : Subset (union A B) (union D E) :=
  fun z hz => (S.union_members _ _ z).mpr (((S.union_members _ _ z).mp hz).elim
    (fun h => Or.inl (hAD z h)) (fun h => Or.inr (hBE z h)))

theorem unionMonoSwap {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (D : Obj (M := M) γ) (E : Obj (M := M) δ)
    (hAE : Subset A E) (hBD : Subset B D) : Subset (union A B) (union D E) :=
  fun z hz => (S.union_members _ _ z).mpr (((S.union_members _ _ z).mp hz).elim
    (fun h => Or.inr (hAE z h)) (fun h => Or.inl (hBD z h)))

/-- The native zero-premise power-set nonemptiness rule uses the empty set. -/
theorem powerSetObjNonempty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α]
    (P : Obj (M := M) (PowerSetObj (M := M) α)) :
    IsNonempty P := by
  refine ⟨S.emptyValue, ?_⟩
  change M.mem S.emptyValue (S.powerValue (denote P.val.bound))
  exact (S.power_members _ _).mpr
    ⟨S.empty_isSet, fun x hx => (S.empty_members x hx).elim⟩

theorem powerSetMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (hAB : Subset A B) : Subset (powerSet A) (powerSet B) := by
  intro z hz
  obtain ⟨hs, hsub⟩ := (S.power_members _ z).mp hz
  exact (S.power_members _ z).mpr ⟨hs, fun t ht => hAB t (hsub t ht)⟩

theorem setMinusMono {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAB : Subset A B) : Subset (setMinus A D) (setMinus B D) :=
  fun z hz => (S.sep_members _ _ z).mpr
    ⟨hAB z ((S.sep_members _ _ z).mp hz).1, ((S.sep_members _ _ z).mp hz).2⟩

theorem setMinusSubsetOfLeft {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (D : Obj (M := M) γ)
    (hAD : Subset A D) : Subset (setMinus A B) D :=
  subsetTrans _ A D (setMinusSubsetLeft A B) hAD

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Input selection depends on the graph and predicate, not on a signature witness. -/
def IsPreimage (f : M.Value) (P : M.Value → Prop) (r : M.Value) : Prop :=
  M.isSet r ∧ ∀ x, M.mem x r ↔ ∃ y, M.mem (F.pairValue x y) f ∧ P y

noncomputable def preimageValue (f : M.Value) (P : M.Value → Prop) : M.Value :=
  by classical exact if h : ∃ r, IsPreimage f P r then Classical.choose h else F.emptyValue

theorem preimage_spec {D B f : M.Value} (P : M.Value → Prop) (hD : M.isSet D)
    (hf : M.mem f (F.fnSetValue D B)) : IsPreimage f P (preimageValue f P) := by
  have exists_preimage : ∃ r, IsPreimage f P r := by
    refine ⟨F.sepValue D (fun x => P (F.callValue f x)), F.sep_isSet _ _ hD, ?_⟩
    intro x
    rw [F.sep_members]
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨F.callValue f x, F.call_graph D B f x ((F.fnSet_members D B f).mp hf) hx, hp⟩
    · rintro ⟨y, hy, hp⟩
      obtain ⟨hx, eq⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) hy
      exact ⟨hx, eq ▸ hp⟩
  simpa only [preimageValue, dif_pos exists_preimage] using Classical.choose_spec exists_preimage

theorem preimage_mem_iff {D B f x : M.Value} (P : M.Value → Prop) (hD : M.isSet D)
    (hf : M.mem f (F.fnSetValue D B)) :
    M.mem x (preimageValue f P) ↔ M.mem x D ∧ P (F.callValue f x) := by
  rw [(preimage_spec P hD hf).2 x]
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨hx, eq⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members D B f).mp hf) hy
    exact ⟨hx, eq ▸ hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨F.callValue f x, F.call_graph D B f x ((F.fnSet_members D B f).mp hf) hx, hp⟩
end FunctionSemantics

structure PointPreimageObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  target : Obj (M := M) β

noncomputable instance preimageRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (PointPreimageObj (M := M) α β) where
  wd p := ∃ s : FunctionSignature M, In p.function (fnSet s)
  denote p := FunctionSemantics.preimageValue (denote p.function) (fun y => y = denote p.target)
  wd_isSet {p} h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.preimage_spec (fun y => y = denote p.target) s.domain_isSet hs).1

noncomputable def preimage {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (target : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In f (fnSet s)) :
    Obj (M := M) (PointPreimageObj (M := M) α β) := ⟨⟨f, target⟩, ⟨s, hf⟩⟩

theorem preimageMembers {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (PointPreimageObj (M := M) α β))
    (s : FunctionSignature M) (hf : In p.val.function (fnSet s)) (x : M.Value) :
    M.mem x (denote p) ↔ M.mem x s.domain ∧
      F.callValue (denote p.val.function) x = denote p.val.target :=
  FunctionSemantics.preimage_mem_iff _ s.domain_isSet hf

structure SetPreimageObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  function : Obj (M := M) α
  target : Obj (M := M) β

noncomputable instance preimageSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SetPreimageObj (M := M) α β) where
  wd p := ∃ s : FunctionSignature M, In p.function (fnSet s)
  denote p := FunctionSemantics.preimageValue (denote p.function) (fun y => M.mem y (denote p.target))
  wd_isSet {p} h := by
    obtain ⟨s, hs⟩ := h
    exact (FunctionSemantics.preimage_spec (fun y => M.mem y (denote p.target)) s.domain_isSet hs).1

noncomputable def preimageSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (target : Obj (M := M) β)
    (s : FunctionSignature M) (hf : In f (fnSet s)) :
    Obj (M := M) (SetPreimageObj (M := M) α β) := ⟨⟨f, target⟩, ⟨s, hf⟩⟩

theorem preimageSetMembers {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (SetPreimageObj (M := M) α β))
    (s : FunctionSignature M) (hf : In p.val.function (fnSet s)) (x : M.Value) :
    M.mem x (denote p) ↔ M.mem x s.domain ∧
      M.mem (F.callValue (denote p.val.function) x) (denote p.val.target) :=
  FunctionSemantics.preimage_mem_iff _ s.domain_isSet hf

namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Complete presentations of one graph have the same input members. -/
theorem domain_mem_iff {f D B E C x : M.Value}
    (hf : M.mem f (F.fnSetValue D B)) (hg : M.mem f (F.fnSetValue E C)) :
    M.mem x D ↔ M.mem x E := by
  constructor
  · intro hx
    exact (FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hg)
      (F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hf) hx)).1
  · intro hx
    exact (FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hf)
      (F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hg) hx)).1

/-- Graph composition mentions only its operands, never a signature witness. -/
def IsComposition (f g r : M.Value) : Prop :=
  M.isSet r ∧ ∀ edge, M.mem edge r ↔
    ∃ x y z, M.mem (F.pairValue x y) g ∧ M.mem (F.pairValue y z) f ∧ edge = F.pairValue x z

noncomputable def compositionValue (f g : M.Value) : M.Value := by
  classical
  exact if h : ∃ r, IsComposition f g r then Classical.choose h else F.emptyValue

theorem composition_graph_spec {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    IsComposition f g (F.graphValue D C (fun x => F.callValue f (F.callValue g x))) := by
  have hreturn : ∀ x, M.mem x D → M.mem (F.callValue f (F.callValue g x)) C :=
    fun x hx => call_mem _ _ _ _ hf (hc x hx)
  refine ⟨M.member_isSet (graph_inFnSet _ _ _ hreturn), ?_⟩
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, z, _, heq, hz⟩ := (F.graph_members _ _ _ _).mp he
    refine ⟨x, F.callValue g x, z, F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hg) hx, ?_, heq⟩
    rw [hz]
    exact F.call_graph _ _ _ _ ((F.fnSet_members _ _ _).mp hf) (hc x hx)
  · rintro ⟨x, y, z, hxy, hyz, rfl⟩
    obtain ⟨hx, hy⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hg) hxy
    obtain ⟨_, hz⟩ := FiniteFunction.graph_pair_value ((F.fnSet_members _ _ _).mp hf) hyz
    apply (pair_mem_graph _ _ _ _ _).mpr
    refine ⟨hx, ?_, ?_⟩
    · rw [hz, hy]
      exact hreturn x hx
    · rw [hz, hy]

theorem composition_spec {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    IsComposition f g (compositionValue f g) := by
  have h : ∃ r, IsComposition f g r := ⟨_, composition_graph_spec hf hg hc⟩
  simpa only [compositionValue, dif_pos h] using Classical.choose_spec h

theorem composition_eq_graph {f g D E B C : M.Value}
    (hf : M.mem f (F.fnSetValue E C)) (hg : M.mem g (F.fnSetValue D B))
    (hc : ∀ x, M.mem x D → M.mem (F.callValue g x) E) :
    compositionValue f g = F.graphValue D C (fun x => F.callValue f (F.callValue g x)) := by
  have hs := composition_spec hf hg hc
  have ht := composition_graph_spec hf hg hc
  exact F.ext _ _ hs.1 ht.1 (fun p => (hs.2 p).trans (ht.2 p).symm)

end FunctionSemantics

structure CompositionObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  outer : Obj (M := M) α
  inner : Obj (M := M) β

noncomputable instance compositionRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CompositionObj (M := M) α β) where
  wd c := ∃ s t : FunctionSignature M, In c.outer (fnSet s) ∧ In c.inner (fnSet t) ∧
    ∀ x, M.mem x t.domain → M.mem (F.callValue (denote c.inner) x) s.domain
  denote c := FunctionSemantics.compositionValue (denote c.outer) (denote c.inner)
  wd_isSet {c} h := by
    obtain ⟨s, t, hf, hg, hc⟩ := h
    exact (FunctionSemantics.composition_spec hf hg hc).1

noncomputable def compose {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (g : Obj (M := M) β) (s t : FunctionSignature M)
    (hf : In f (fnSet s)) (hg : In g (fnSet t))
    (hc : ∀ x, M.mem x t.domain → M.mem (F.callValue (denote g) x) s.domain) :
    Obj (M := M) (CompositionObj (M := M) α β) := ⟨⟨f, g⟩, ⟨s, t, hf, hg, hc⟩⟩

/-- A cached composition remains compatible under any checked complete interfaces. -/
theorem composeCompatible {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    ∀ x, M.mem x t.domain → M.mem (F.callValue (denote c.val.inner) x) s.domain := by
  obtain ⟨s₀, t₀, hf₀, hg₀, hc₀⟩ := c.wd
  intro x hx
  exact (FunctionSemantics.domain_mem_iff hf₀ hf).mp
    (hc₀ x ((FunctionSemantics.domain_mem_iff hg hg₀).mp hx))

theorem composeGraph {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    denote c = F.graphValue t.domain s.output
      (fun x => F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x)) :=
  FunctionSemantics.composition_eq_graph hf hg (composeCompatible c s t hf hg)

theorem composeInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t)) :
    In c (fnSet (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet)) := by
  change M.mem (denote c) (F.fnSetValue t.domain s.output)
  rw [composeGraph c s t hf hg]
  exact FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
    FunctionSemantics.call_mem _ _ _ _ hf (composeCompatible c s t hf hg x hx))

theorem composeCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t))
    (x : M.Value) (hx : M.mem x t.domain) :
    F.callValue (denote c) x = F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x) := by
  rw [composeGraph c s t hf hg]
  exact FunctionSemantics.call_graphValue _ _ _ (fun a ha =>
    FunctionSemantics.call_mem _ _ _ _ hf (composeCompatible c s t hf hg a ha)) _ hx

theorem callInputInDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β)) (s : FunctionSignature M)
    (hf : In c.val.function (fnSet s)) : M.mem (denote c.val.argument) s.domain :=
  (FunctionSemantics.domain_mem_iff c.wd.1 hf).mp
    ((FunctionSignature.oneTarget_domain _ _ _ _ _).mpr c.wd.2)

theorem callOnInputInDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β)) (s : FunctionSignature M)
    (hf : In c.val.function (fnSet s)) : M.mem (denote c.val.argument) s.domain :=
  (FunctionSemantics.domain_mem_iff c.wd.1 hf).mp c.wd.2


namespace FunctionSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem composition_pair_iff {f g c x z : M.Value} (hc : IsComposition f g c) :
    M.mem (F.pairValue x z) c ↔ ∃ y, M.mem (F.pairValue x y) g ∧ M.mem (F.pairValue y z) f := by
  constructor
  · intro h
    obtain ⟨a, y, b, hay, hyb, heq⟩ := (hc.2 _).mp h
    obtain ⟨rfl, rfl⟩ := F.pair_injective heq
    exact ⟨y, hay, hyb⟩
  · rintro ⟨y, hxy, hyz⟩
    exact (hc.2 _).mpr ⟨x, y, z, hxy, hyz, rfl⟩

theorem composition_associative {f g h fg gh left right : M.Value}
    (hfg : IsComposition f g fg) (hgh : IsComposition g h gh)
    (hl : IsComposition fg h left) (hr : IsComposition f gh right) : left = right := by
  apply F.ext _ _ hl.1 hr.1
  intro edge
  constructor
  · intro he
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := (hl.2 edge).mp he
    obtain ⟨a, hya, haz⟩ := (composition_pair_iff hfg).mp hyz
    exact (hr.2 _).mpr ⟨x, a, z, (composition_pair_iff hgh).mpr ⟨y, hxy, hya⟩, haz, rfl⟩
  · intro he
    obtain ⟨x, a, z, hxa, haz, rfl⟩ := (hr.2 edge).mp he
    obtain ⟨y, hxy, hya⟩ := (composition_pair_iff hgh).mp hxa
    exact (hl.2 _).mpr ⟨x, y, z, hxy, (composition_pair_iff hfg).mpr ⟨a, hya, haz⟩, rfl⟩

end FunctionSemantics

theorem composeSpec {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β)) :
    FunctionSemantics.IsComposition (denote c.val.outer) (denote c.val.inner) (denote c) := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  exact FunctionSemantics.composition_spec hf hg hc

theorem composeLeftIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (identity : Obj (M := M) (FormulaFn M)) (heq : Same c.val.outer identity)
    (hbody : ∀ x, identity.val.bodyValue x = x) : Same c c.val.inner := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  have hi : In c.val.outer (fnSet identity.val.signature) := by
    change M.mem (denote c.val.outer) _
    rw [heq]
    exact formulaFnInFnSet identity
  apply functionExtOnDomain c c.val.inner
    (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet) t
    (composeInFnSet c s t hf hg) hg rfl
  intro x hx
  rw [composeCall c s t hf hg x hx, heq]
  exact (FunctionSemantics.call_graphValue _ _ _ identity.wd _
    ((FunctionSemantics.domain_mem_iff hf hi).mp (hc x hx))).trans (hbody _)

theorem composeRightIdentity {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (identity : Obj (M := M) (FormulaFn M)) (heq : Same c.val.inner identity)
    (hbody : ∀ x, identity.val.bodyValue x = x)
    (s : FunctionSignature M) (hf : In c.val.outer (fnSet s))
    (hD : s.domain = identity.val.signature.domain) : Same c c.val.outer := by
  obtain ⟨s₀, t, hf₀, hg, hc⟩ := c.wd
  have hi : In c.val.inner (fnSet identity.val.signature) := by
    change M.mem (denote c.val.inner) _
    rw [heq]
    exact formulaFnInFnSet identity
  have hdomain : t.domain = identity.val.signature.domain :=
    F.ext _ _ t.domain_isSet identity.val.signature.domain_isSet
      (fun x => FunctionSemantics.domain_mem_iff hg hi)
  apply functionExtOnDomain c c.val.outer
    (FunctionSignature.ofDomain t.domain s₀.output t.domain_isSet s₀.output_isSet) s
    (composeInFnSet c s₀ t hf₀ hg) hf (hdomain.trans hD.symm)
  intro x hx
  rw [composeCall c s₀ t hf₀ hg x hx, heq]
  exact congrArg (F.callValue (denote c.val.outer))
    ((FunctionSemantics.call_graphValue _ _ _ identity.wd _ (hdomain ▸ hx)).trans (hbody x))

theorem composeEqFormula {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (f : Obj (M := M) (FormulaFn M)) (s t : FunctionSignature M)
    (hf : In c.val.outer (fnSet s)) (hg : In c.val.inner (fnSet t))
    (hD : t.domain = f.val.signature.domain)
    (hbody : ∀ x, M.mem x t.domain → f.val.bodyValue x =
      F.callValue (denote c.val.outer) (F.callValue (denote c.val.inner) x)) : Same c f := by
  apply functionExtOnDomain c f
    (FunctionSignature.ofDomain t.domain s.output t.domain_isSet s.output_isSet)
    f.val.signature (composeInFnSet c s t hf hg) (formulaFnInFnSet f) hD
  intro x hx
  rw [composeCall c s t hf hg x hx]
  exact ((FunctionSemantics.call_graphValue _ _ _ f.wd _ (hD ▸ hx)).trans (hbody x hx)).symm

theorem composeRangeSubset {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CompositionObj (M := M) α β))
    (r : Obj (M := M) (FunctionRange (M := M) γ))
    (q : Obj (M := M) (FunctionRange (M := M) δ))
    (hr : Same r.val.function c) (hq : Same q.val.function c.val.outer) : Subset r q := by
  obtain ⟨s, t, hf, hg, hc⟩ := c.wd
  intro z hz
  change M.mem z (FunctionSemantics.rangeValue (denote q.val.function))
  change M.mem z (FunctionSemantics.rangeValue (denote r.val.function)) at hz
  rw [hr] at hz
  rw [hq]
  obtain ⟨a, ha, rfl⟩ := (FunctionSemantics.range_mem_iff s.output_isSet
    (composeInFnSet c s t hf hg)).mp hz
  exact (FunctionSemantics.range_mem_iff s.output_isSet hf).mpr
    ⟨F.callValue (denote c.val.inner) a, hc a ha, composeCall c s t hf hg a ha⟩

end Litex

namespace Litex

def memberSet {M : Semantics.{u}} (A : M.Value) : Set M.Value := {x | M.mem x A}

def IsFiniteSet {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Prop := (memberSet (denote A)).Finite

noncomputable def finiteCard {M : Semantics.{u}} (A : M.Value) : ℕ :=
  (memberSet A).ncard

structure FiniteSetSizeObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance finiteSetSizeRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (FiniteSetSizeObj (M := M) α) where
  wd p := IsFiniteSet p.set
  denote p := M.number (finiteCard (denote p.set) : ℂ)
  wd_isSet _ := M.member_isSet ((M.natural_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteSetSize {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsFiniteSet A) : Obj (M := M) (FiniteSetSizeObj (M := M) α) :=
  ⟨⟨A⟩, h⟩

theorem finiteSetSizeInN {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) : In p N :=
  (M.natural_members _).mpr ⟨_, rfl⟩

theorem memberSet_empty {M : Semantics.{u}} [S : SetSemantics M] :
    memberSet S.emptyValue = ∅ := by
  ext x
  exact ⟨fun h => (S.empty_members x h).elim, False.elim⟩

theorem memberSet_insert {M : Semantics.{u}} [S : SetSemantics M] (a A : M.Value) :
    memberSet (S.insertValue a A) = Insert.insert a (memberSet A) := by
  ext x
  exact S.insert_members a A x

theorem finiteSetEmpty {M : Semantics.{u}} [S : SetSemantics M] :
    IsFiniteSet (emptySet (M := M)) := by
  change (memberSet S.emptyValue).Finite
  rw [memberSet_empty]
  exact Set.finite_empty

theorem finiteSetInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (h : IsFiniteSet p.val.tail) :
    IsFiniteSet p := by
  change (memberSet (S.insertValue _ _)).Finite
  rw [memberSet_insert]
  exact h.insert _

theorem finiteCardEmpty {M : Semantics.{u}} [S : SetSemantics M] :
    finiteCard S.emptyValue = 0 := by rw [finiteCard, memberSet_empty, Set.ncard_empty]

theorem finiteCardInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (h : IsFiniteSet p.val.tail) :
    finiteCard (denote p) = finiteCard (denote p.val.tail) + 1 := by
  change (memberSet (S.insertValue _ _)).ncard = _
  rw [memberSet_insert]
  exact Set.ncard_insert_of_notMem (s := memberSet (denote p.val.tail)) (a := denote p.val.element) p.wd h

theorem memberSetSingletonIntersection {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) :
    memberSet (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue b S.emptyValue))) = ({a} ∩ {b} : Set M.Value) := by
  ext x
  simp only [memberSet, Set.mem_setOf_eq, S.sep_members, S.insert_members,
    S.empty_members, or_false, Set.mem_inter_iff, Set.mem_singleton_iff]

theorem finiteCardSingletonIntersectionSame {M : Semantics.{u}} [S : SetSemantics M]
    (a : M.Value) :
    finiteCard (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue a S.emptyValue))) = 1 := by
  rw [finiteCard, memberSetSingletonIntersection, Set.inter_self, Set.ncard_singleton]

theorem finiteCardSingletonIntersectionDifferent {M : Semantics.{u}} [S : SetSemantics M]
    (a b : M.Value) (h : a ≠ b) :
    finiteCard (S.sepValue (S.insertValue a S.emptyValue)
      (fun x => M.mem x (S.insertValue b S.emptyValue))) = 0 := by
  rw [finiteCard, memberSetSingletonIntersection]
  have empty : ({a} ∩ {b} : Set M.Value) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hab⟩
    exact h hab
  rw [empty, Set.ncard_empty]

theorem finiteSetSizeDenote {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) (n : ℕ)
    (h : finiteCard (denote p.val.set) = n) : denote p = M.number (n : ℂ) := by
  change M.number ((finiteCard _) : ℂ) = _
  rw [h]

theorem finiteSetSizeNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) : Le (number 0) p := by
  refine ⟨0, (finiteCard (denote p.val.set) : ℝ), ?_, ?_, Nat.cast_nonneg _⟩
  · change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
    rfl
  · change M.number ((finiteCard _) : ℂ) = _
    rw [Complex.ofReal_natCast]

/-- Real observations of members, independent of any finiteness/WD proof. -/
def realMembers {M : Semantics.{u}} (A : M.Value) : Set ℝ :=
  {r | M.mem (M.number (r : ℂ)) A}

theorem realMembers_finite {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsFiniteSet A) : (realMembers (denote A)).Finite :=
  Set.Finite.preimage (M.number_injective.comp Complex.ofReal_injective).injOn h

theorem realMembers_nonempty {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : IsNonempty A) (hr : Subset A R) :
    (realMembers (denote A)).Nonempty := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨r, he⟩ := (M.real_members a).mp (hr a ha)
  refine ⟨r, ?_⟩
  change M.mem (M.number (r : ℂ)) (denote A)
  rw [← he]
  exact ha

noncomputable def finiteExtremumValue {M : Semantics.{u}} (maximum : Bool) (A : M.Value) : ℝ :=
  if maximum then sSup (realMembers A) else sInf (realMembers A)

structure FiniteExtremumObj {M : Semantics.{u}} (maximum : Bool) (α : Type v) [Representation M α] where
  set : Obj (M := M) α

noncomputable instance finiteExtremumRepresentation {M : Semantics.{u}} (maximum : Bool)
    {α : Type v} [Representation M α] : Representation M (FiniteExtremumObj (M := M) maximum α) where
  wd p := IsFiniteSet p.set ∧ IsNonempty p.set ∧ Subset p.set R
  denote p := M.number (finiteExtremumValue maximum (denote p.set) : ℂ)
  wd_isSet _ := M.member_isSet ((M.real_members _).mpr ⟨_, rfl⟩)


noncomputable def finiteExtremum {M : Semantics.{u}} (maximum : Bool)
    {α : Type v} [Representation M α] (A : Obj (M := M) α)
    (hf : IsFiniteSet A) (hn : IsNonempty A) (hr : Subset A R) :
    Obj (M := M) (FiniteExtremumObj (M := M) maximum α) := ⟨⟨A⟩, hf, hn, hr⟩

theorem finiteExtremumInR {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) : In p R :=
  (M.real_members _).mpr ⟨_, rfl⟩

theorem finiteExtremumInSet {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) : In p p.val.set := by
  have hf := realMembers_finite p.val.set p.wd.1
  have hn := realMembers_nonempty p.val.set p.wd.2.1 p.wd.2.2
  cases maximum
  · exact hn.csInf_mem hf
  · exact hn.csSup_mem hf

theorem finiteExtremumDenote {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α)) (r : ℝ)
    (hr : M.mem (M.number (r : ℂ)) (denote p.val.set))
    (hb : ∀ x ∈ realMembers (denote p.val.set), if maximum then x ≤ r else r ≤ x) :
    denote p = M.number (r : ℂ) := by
  have hf := realMembers_finite p.val.set p.wd.1
  have hn := realMembers_nonempty p.val.set p.wd.2.1 p.wd.2.2
  apply congrArg (fun x : ℝ => M.number (x : ℂ))
  cases maximum
  · exact le_antisymm (csInf_le hf.bddBelow hr) (le_csInf hn hb)
  · exact le_antisymm (csSup_le hn hb) (le_csSup hf.bddAbove hr)

theorem finiteExtremumBound {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α))
    (a : Obj (M := M) β) (ha : In a p.val.set) : if maximum then Le a p else Le p a := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp (p.wd.2.2 (denote a) ha)
  have hm : r ∈ realMembers (denote p.val.set) := by
    change M.mem (M.number (r : ℂ)) (denote p.val.set)
    rw [← hr]
    exact ha
  have hf := realMembers_finite p.val.set p.wd.1
  cases maximum
  · exact ⟨_, r, rfl, hr, csInf_le hf.bddBelow hm⟩
  · exact ⟨r, _, hr, rfl, le_csSup hf.bddAbove hm⟩


theorem finiteMembersEmpty {M : Semantics.{u}} [S : SetSemantics M] (x : M.Value) :
    M.mem x (denote (emptySet (M := M))) ↔ x ∈ ([] : List M.Value) := by
  exact ⟨fun h => (S.empty_members x h).elim, fun h => (List.not_mem_nil h).elim⟩

theorem finiteMembersInsert {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (a : M.Value) (xs : List M.Value)
    (he : denote p.val.element = a)
    (ht : ∀ x, M.mem x (denote p.val.tail) ↔ x ∈ xs) :
    ∀ x, M.mem x (denote p) ↔ x ∈ a :: xs := by
  intro x
  change M.mem x (S.insertValue _ _) ↔ _
  rw [S.insert_members, he, ht, List.mem_cons]

theorem finiteExtremumListDenote {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteExtremumObj (M := M) maximum α))
    (xs : List ℝ) (r : ℝ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map (fun q : ℝ => M.number (q : ℂ)))
    (hs : r ∈ xs) (hb : ∀ x ∈ xs, if maximum then x ≤ r else r ≤ x) :
    denote p = M.number (r : ℂ) := by
  apply finiteExtremumDenote p r
  · exact (hm _).mpr ((List.mem_map (f := fun q : ℝ => M.number (q : ℂ))).mpr ⟨r, hs, rfl⟩)
  · intro x hx
    obtain ⟨q, hq, he⟩ := (List.mem_map (f := fun q : ℝ => M.number (q : ℂ))).mp ((hm _).mp hx)
    have hqx : q = x := Complex.ofReal_injective (M.number_injective he)
    exact hqx ▸ hb q hq


theorem noMemClosedIntegerRange {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b : ℂ) (lower upper : ℤ) (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ))
    (h : upper < lower) (x : M.Value) :
    ¬ M.mem x (F.sepValue (M.standard .integer)
      (ClosedRangeObj.condition ⟨number a, number b⟩)) := by
  subst a
  subst b
  intro hx
  obtain ⟨_, l, r, k, hl, hr, _, hlow, hupp⟩ := (F.sep_members _ _ _).mp hx
  change M.number (lower : ℂ) = M.number (l : ℂ) at hl
  change M.number (upper : ℂ) = M.number (r : ℂ) at hr
  have hl' : l = lower := by exact_mod_cast M.number_injective hl.symm
  have hr' : r = upper := by exact_mod_cast M.number_injective hr.symm
  omega

theorem noMemIntegerRange {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b : ℂ) (lower upper : ℤ) (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ))
    (h : upper ≤ lower) (x : M.Value) :
    ¬ M.mem x (F.sepValue (M.standard .integer)
      (RangeObj.condition ⟨number a, number b⟩)) := by
  subst a
  subst b
  intro hx
  obtain ⟨_, l, r, k, hl, hr, _, hlow, hupp⟩ := (F.sep_members _ _ _).mp hx
  change M.number (lower : ℂ) = M.number (l : ℂ) at hl
  change M.number (upper : ℂ) = M.number (r : ℂ) at hr
  have hl' : l = lower := by exact_mod_cast M.number_injective hl.symm
  have hr' : r = upper := by exact_mod_cast M.number_injective hr.symm
  omega


theorem closedRangeStartMember {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (ClosedRangeObj (M := M) α β))
    (hi : In r.val.start Z) (ho : Le r.val.start r.val.finish) :
    In r.val.start r := by
  obtain ⟨l, hl⟩ := (M.integer_members _).mp hi
  obtain ⟨h, hh⟩ := (M.integer_members _).mp r.wd.2
  have order := (NativeBridge.le_iff_ofDenoteReal r.val.start r.val.finish
    (l : ℝ) (h : ℝ)
    (by simpa only [Complex.ofReal_intCast] using hl)
    (by simpa only [Complex.ofReal_intCast] using hh)).mp ho
  have order' : l ≤ h := by exact_mod_cast order
  exact (inClosedRange_iff r.val.start r.val.finish r.val.start r.wd.1 r.wd.2).mpr
    ⟨l,h,l,hl,hh,hl,le_rfl,order'⟩

theorem rangeStartMember {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (r : Obj (M := M) (RangeObj (M := M) α β))
    (hi : In r.val.start Z) (ho : Lt r.val.start r.val.finish) :
    In r.val.start r := by
  obtain ⟨l, hl⟩ := (M.integer_members _).mp hi
  obtain ⟨h, hh⟩ := (M.integer_members _).mp r.wd.2
  have order := (NativeBridge.lt_iff_ofDenoteReal r.val.start r.val.finish
    (l : ℝ) (h : ℝ)
    (by simpa only [Complex.ofReal_intCast] using hl)
    (by simpa only [Complex.ofReal_intCast] using hh)).mp ho
  have order' : l < h := by exact_mod_cast order
  exact (inRange_iff r.val.start r.val.finish r.val.start r.wd.1 r.wd.2).mpr
    ⟨l,h,l,hl,hh,hl,le_rfl,order'⟩

end Litex

