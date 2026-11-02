import Litex.FiniteSets

universe u v w x

namespace Litex

namespace NativeBridge
variable {M : Semantics.{u}}

/-- Total observations of the fixed denotation. Source WD supplies their domains. -/
noncomputable def complexValue (a : M.Value) : ℂ := by
  classical
  exact if h : ∃ z : ℂ, a = M.number z then Classical.choose h else 0

theorem complexValue_number (z : ℂ) : complexValue (M.number z) = z := by
  classical
  have h : ∃ w : ℂ, M.number z = M.number w := ⟨z, rfl⟩
  unfold complexValue
  rw [dif_pos h]
  exact (M.number_injective (Classical.choose_spec h)).symm

theorem complexValue_spec (a : M.Value) (ha : M.mem a (M.standard .complex)) :
    a = M.number (complexValue a) := by
  obtain ⟨z, rfl⟩ := (M.complex_members a).mp ha
  rw [complexValue_number]

noncomputable def integerValue (a : M.Value) : ℤ := by
  classical
  exact if h : ∃ k : ℤ, a = M.number (k : ℂ) then Classical.choose h else 0

theorem integerValue_number (k : ℤ) : integerValue (M.number (k : ℂ)) = k := by
  classical
  have h : ∃ j : ℤ, M.number (k : ℂ) = M.number (j : ℂ) := ⟨k, rfl⟩
  unfold integerValue
  rw [dif_pos h]
  have he := M.number_injective (Classical.choose_spec h)
  exact_mod_cast he.symm

theorem integerValue_spec (a : M.Value) (ha : M.mem a (M.standard .integer)) :
    a = M.number (integerValue a : ℂ) := by
  obtain ⟨k, rfl⟩ := (M.integer_members a).mp ha
  rw [integerValue_number]

end NativeBridge

noncomputable def nativeRangeAggregate (product : Bool) (first last : ℤ)
    (value : ℤ → ℂ) : ℂ :=
  if product then ∏ i ∈ Finset.Icc first last, value i
  else ∑ i ∈ Finset.Icc first last, value i

structure RangeAggregateObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  first : Obj (M := M) α
  last : Obj (M := M) β
  function : Obj (M := M) γ
  signature : FunctionSignature M

noncomputable instance rangeAggregateRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (RangeAggregateObj (M := M) product α β γ) where
  wd p := In p.first Z ∧ In p.last Z ∧ Le p.first p.last ∧
    In p.function (fnSet p.signature) ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    (∀ k : ℤ, NativeBridge.integerValue (denote p.first) ≤ k →
      k ≤ NativeBridge.integerValue (denote p.last) →
      M.mem (M.number (k : ℂ)) p.signature.domain)
  denote p := M.number (nativeRangeAggregate product
    (NativeBridge.integerValue (denote p.first))
    (NativeBridge.integerValue (denote p.last))
    (fun k => NativeBridge.complexValue (F.callValue (denote p.function) (M.number (k : ℂ)))))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def rangeAggregate {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (f : Obj (M := M) γ)
    (s : FunctionSignature M) (ha : In a Z) (hb : In b Z) (hle : Le a b)
    (hf : In f (fnSet s))
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hd : ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → M.mem (M.number (k : ℂ)) s.domain) :
    Obj (M := M) (RangeAggregateObj (M := M) product α β γ) :=
  ⟨⟨a, b, f, s⟩, ha, hb, hle, hf, hr, hd⟩

theorem rangeAggregateInC {M : Semantics.{u}} [FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ)) : In p C :=
  (M.complex_members _).mpr ⟨_, rfl⟩

theorem rangeAggregateCallInC {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (k : ℤ) (ha : NativeBridge.integerValue (denote p.val.first) ≤ k)
    (hb : k ≤ NativeBridge.integerValue (denote p.val.last)) :
    M.mem (F.callValue (denote p.val.function) (M.number (k : ℂ))) (M.standard .complex) :=
  p.wd.2.2.2.2.1 _ (FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2.1
    (p.wd.2.2.2.2.2 k ha hb))

theorem rangeAggregateDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (a b : ℤ) (ha : denote p.val.first = M.number (a : ℂ))
    (hb : denote p.val.last = M.number (b : ℂ)) (value : ℂ)
    (h : nativeRangeAggregate product a b
      (fun k => NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number (k : ℂ)))) = value) :
    denote p = M.number value := by
  change M.number (nativeRangeAggregate product _ _ _) = _
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number, h]

theorem integerInUnboundedCarrier {M : Semantics.{u}} (A : StandardSetValue)
    (h : A ≠ .natural) (k : ℤ) : M.mem (M.number (k : ℂ)) (M.standard A) := by
  cases A
  · exact (h rfl).elim
  · exact NativeBridge.numberInZ k
  · exact integerToRational (number (k : ℂ)) (NativeBridge.numberInZ k)
  · exact integerToReal (number (k : ℂ)) (NativeBridge.numberInZ k)
  · exact numberInC (k : ℂ)

theorem unguardedIntegerDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B) (h : A ≠ .natural)
    (k : ℤ) : M.mem (M.number (k : ℂ))
      (FunctionSignature.oneTarget A B hB (fun _ => True)).domain :=
  (FunctionSignature.oneTarget_domain A B hB (fun _ => True) _).mpr
    ⟨integerInUnboundedCarrier A h k, True.intro⟩

theorem standardZeroMember {M : Semantics.{u}} (A : StandardSetValue) :
    M.mem (M.number 0) (M.standard A) := by
  cases A
  · exact (M.natural_members _).mpr ⟨0, by simp⟩
  · exact (M.integer_members _).mpr ⟨0, by simp⟩
  · exact (M.rational_members _).mpr ⟨0, by simp⟩
  · exact (M.real_members _).mpr ⟨0, by simp⟩
  · exact (M.complex_members _).mpr ⟨0, by simp⟩

theorem standardOneMember {M : Semantics.{u}} (A : StandardSetValue) :
    M.mem (M.number 1) (M.standard A) := by
  cases A
  · exact (M.natural_members _).mpr ⟨1, by simp⟩
  · exact (M.integer_members _).mpr ⟨1, by simp⟩
  · exact (M.rational_members _).mpr ⟨1, by simp⟩
  · exact (M.real_members _).mpr ⟨1, by simp⟩
  · exact (M.complex_members _).mpr ⟨1, by simp⟩

theorem standardAddMember {M : Semantics.{u}} (A : StandardSetValue)
    (a b : ℂ) (ha : M.mem (M.number a) (M.standard A))
    (hb : M.mem (M.number b) (M.standard A)) :
    M.mem (M.number (a + b)) (M.standard A) := by
  rw [← M.add_numbers]
  cases A
  · exact addInN (number a) (number b) ha hb
  · exact addInZ (number a) (number b) ha hb
  · exact addInQ (number a) (number b) ha hb
  · exact addInR (number a) (number b) ha hb
  · exact addInC (number a) (number b) ha hb

theorem standardMulMember {M : Semantics.{u}} (A : StandardSetValue)
    (a b : ℂ) (ha : M.mem (M.number a) (M.standard A))
    (hb : M.mem (M.number b) (M.standard A)) :
    M.mem (M.number (a * b)) (M.standard A) := by
  rw [← M.mul_numbers]
  cases A
  · exact mulInN (number a) (number b) ha hb
  · exact mulInZ (number a) (number b) ha hb
  · exact mulInQ (number a) (number b) ha hb
  · exact mulInR (number a) (number b) ha hb
  · exact mulInC (number a) (number b) ha hb

theorem nativeRangeAggregateMember {M : Semantics.{u}} (product : Bool)
    (A : StandardSetValue) (a b : ℤ) (value : ℤ → ℂ)
    (h : ∀ i ∈ Finset.Icc a b, M.mem (M.number (value i)) (M.standard A)) :
    M.mem (M.number (nativeRangeAggregate product a b value)) (M.standard A) := by
  unfold nativeRangeAggregate
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    generalize Finset.Icc a b = s at *
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    generalize Finset.Icc a b = s at *
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem rangeAggregateMemberOfOutputSubset {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : ∀ y, M.mem y p.val.signature.output → M.mem y (M.standard A)) :
    In p (standardSet A) := by
  apply nativeRangeAggregateMember product A
  intro i hi
  obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hi
  rw [← NativeBridge.complexValue_spec _ (rangeAggregateCallInC p i ha hb)]
  apply hs
  exact FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2.2 i ha hb)



theorem rangeAggregateMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  apply rangeAggregateMemberOfOutputSubset p A
  intro y hy
  rw [← hs]
  exact hy

end Litex

namespace Litex

/-- The finite fold observes semantic members; no WD proof selects its value. -/
noncomputable def finiteAggregateValue {M : Semantics.{u}} (product : Bool)
    (A : M.Value) (value : M.Value → ℂ) : ℂ := by
  classical
  exact if h : (memberSet A).Finite then
    if product then ∏ x ∈ h.toFinset, value x else ∑ x ∈ h.toFinset, value x
  else if product then 1 else 0

structure FiniteAggregateObj {M : Semantics.{u}} (product : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  input : StandardSetValue
  signature : FunctionSignature M

noncomputable instance finiteAggregateRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] (product : Bool)
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (FiniteAggregateObj (M := M) product α β) where
  wd p := IsFiniteSet p.set ∧ Subset p.set (standardSet p.input) ∧
    (∀ y, M.mem y p.signature.output → M.mem y (M.standard .complex)) ∧
    In p.function (fnSet p.signature) ∧
    (∀ x, M.mem x (M.standard p.input) → M.mem x p.signature.domain)
  denote p := M.number (finiteAggregateValue product (denote p.set)
    (fun x => NativeBridge.complexValue (F.callValue (denote p.function) x)))
  wd_isSet _ := M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def finiteAggregate {M : Semantics.{u}} [FunctionSemantics M]
    (product : Bool) {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (f : Obj (M := M) β)
    (input : StandardSetValue) (s : FunctionSignature M)
    (hf : IsFiniteSet A) (hi : Subset A (standardSet input))
    (hr : ∀ y, M.mem y s.output → M.mem y (M.standard .complex))
    (hfn : In f (fnSet s))
    (hd : ∀ x, M.mem x (M.standard input) → M.mem x s.domain) :
    Obj (M := M) (FiniteAggregateObj (M := M) product α β) :=
  ⟨⟨A, f, input, s⟩, hf, hi, hr, hfn, hd⟩

theorem finiteAggregateCallInOutput {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (x : M.Value) (hx : M.mem x (denote p.val.set)) :
    M.mem (F.callValue (denote p.val.function) x) p.val.signature.output :=
  F.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2 x (p.wd.2.1 x hx))

theorem finiteAggregateMemberOfOutputSubset {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (A : StandardSetValue) (hs : ∀ y, M.mem y p.val.signature.output → M.mem y (M.standard A)) :
    In p (standardSet A) := by
  classical
  have hm : ∀ x ∈ p.wd.1.toFinset,
      M.mem (M.number (NativeBridge.complexValue (F.callValue (denote p.val.function) x)))
        (M.standard A) := by
    intro x hx
    have ho := finiteAggregateCallInOutput p x (p.wd.1.mem_toFinset.mp hx)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho)]
    exact hs _ ho
  change M.mem (M.number (finiteAggregateValue product _ _)) (M.standard A)
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  generalize p.wd.1.toFinset = s at *
  cases product
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using standardZeroMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact standardAddMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))
  · simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using standardOneMember (M := M) A
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact standardMulMember A _ _ (hm i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hm j (Finset.mem_insert_of_mem hj)))



theorem finiteAggregateMember {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (A : StandardSetValue) (hs : p.val.signature.output = M.standard A) :
    In p (standardSet A) := by
  apply finiteAggregateMemberOfOutputSubset p A
  intro y hy
  rw [← hs]
  exact hy

theorem finiteAggregateListDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (xs : List ℂ) (value : ℂ)
    (hm : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs.map M.number)
    (hc : (if product then ∏ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))
      else ∑ x ∈ xs.toFinset,
        NativeBridge.complexValue (F.callValue (denote p.val.function) (M.number x))) = value) :
    denote p = M.number value := by
  classical
  have ht : p.wd.1.toFinset = xs.toFinset.image M.number := by
    ext x
    rw [Set.Finite.mem_toFinset]
    change M.mem x (denote p.val.set) ↔ _
    rw [hm]
    simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]
  change M.number (finiteAggregateValue product _ _) = _
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf, ht]
  apply congrArg M.number
  have hi : ∀ a ∈ xs.toFinset, ∀ b ∈ xs.toFinset, M.number a = M.number b → a = b :=
    fun _ _ _ _ h => M.number_injective h
  cases product
  · simpa only [Bool.false_eq_true, ↓reduceIte, Finset.sum_image hi] using hc
  · simpa only [↓reduceIte, Finset.prod_image hi] using hc

end Litex

namespace Litex

def realBound {M : Semantics.{u}} (closed : Bool) (a b : M.Value) : Prop :=
  if closed then ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s
  else ∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r < s

theorem realBound_iff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (closed : Bool)
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    realBound closed (denote a) (denote b) ↔ (if closed then Le a b else Lt a b) := by
  cases closed <;> rfl

theorem realBound_le {M : Semantics.{u}} {c : Bool} {a b : M.Value}
    (h : realBound c a b) : realBound true a b := by
  cases c
  · obtain ⟨r,s,hr,hs,h⟩ := h; exact ⟨r,s,hr,hs,h.le⟩
  · exact h

theorem realBound_not_opposite {M : Semantics.{u}} {c : Bool} {a b : M.Value}
    (h : realBound c a b) : ¬ realBound (!c) b a := by
  cases c <;> intro g
  all_goals
    obtain ⟨r,s,hr,hs,h⟩ := h
    obtain ⟨t,q,ht,hq,g⟩ := g
    have hst : s = t := Complex.ofReal_injective (M.number_injective (hs.symm.trans ht))
    have hrq : r = q := Complex.ofReal_injective (M.number_injective (hr.symm.trans hq))
    subst t; subst q
    linarith

structure RealIntervalObj {M : Semantics.{u}} (lc rc : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  lower : Obj (M := M) α
  upper : Obj (M := M) β

instance realIntervalRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    (lc rc : Bool) {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (RealIntervalObj (M := M) lc rc α β) where
  wd p := In p.lower R ∧ In p.upper R
  denote p := S.sepValue (M.standard .real)
    (fun a => realBound lc (denote p.lower) a ∧ realBound rc a (denote p.upper))
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .real)

def realInterval {M : Semantics.{u}} [SetSemantics M] (lc rc : Bool)
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a R) (hb : In b R) :
    Obj (M := M) (RealIntervalObj (M := M) lc rc α β) := ⟨⟨a,b⟩,ha,hb⟩

theorem inRealInterval_iff {M : Semantics.{u}} [S : SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ) :
    In a p ↔ In a R ∧ (if lc then Le p.val.lower a else Lt p.val.lower a) ∧
      (if rc then Le a p.val.upper else Lt a p.val.upper) := by
  change M.mem (denote a) (S.sepValue _ _) ↔ _
  rw [S.sep_members, realBound_iff, realBound_iff]
  rfl

theorem realIntervalSubsetR {M : Semantics.{u}} [S : SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) : Subset p R :=
  fun _ h => (S.sep_members _ _ _).mp h |>.1

theorem notInRealIntervalLower {M : Semantics.{u}} [SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ)
    (h : Lt a p.val.lower) : ¬ In a p := by
  intro hi
  have hb := ((realBound_iff lc p.val.lower a).mpr ((inRealInterval_iff p a).mp hi).2.1)
  exact realBound_not_opposite (realBound_le hb) h

theorem notInRealIntervalUpper {M : Semantics.{u}} [SetSemantics M]
    {lc rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc rc α β)) (a : Obj (M := M) γ)
    (h : Lt p.val.upper a) : ¬ In a p := by
  intro hi
  have hb := ((realBound_iff rc a p.val.upper).mpr ((inRealInterval_iff p a).mp hi).2.2)
  exact realBound_not_opposite (realBound_le hb) h

theorem notInRealIntervalOpenLower {M : Semantics.{u}} [SetSemantics M]
    {rc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) false rc α β)) (a : Obj (M := M) γ)
    (h : Same a p.val.lower) : ¬ In a p :=
  fun hi => ltNotSame p.val.lower a ((inRealInterval_iff p a).mp hi).2.1 h.symm

theorem notInRealIntervalOpenUpper {M : Semantics.{u}} [SetSemantics M]
    {lc : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RealIntervalObj (M := M) lc false α β)) (a : Obj (M := M) γ)
    (h : Same a p.val.upper) : ¬ In a p :=
  fun hi => ltNotSame a p.val.upper ((inRealInterval_iff p a).mp hi).2.2 h

structure RealRayObj {M : Semantics.{u}} (lower closed : Bool)
    (α : Type v) [Representation M α] where
  endpoint : Obj (M := M) α

instance realRayRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    (lower closed : Bool) {α : Type v} [Representation M α] :
    Representation M (RealRayObj (M := M) lower closed α) where
  wd p := In p.endpoint R
  denote p := S.sepValue (M.standard .real) (fun a =>
    if lower then realBound closed (denote p.endpoint) a else realBound closed a (denote p.endpoint))
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .real)

def realRay {M : Semantics.{u}} [SetSemantics M] (lower closed : Bool)
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (RealRayObj (M := M) lower closed α) := ⟨⟨a⟩,ha⟩

theorem inRealRay_iff {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) (a : Obj (M := M) β) :
    In a p ↔ In a R ∧ (if lower then
      (if closed then Le p.val.endpoint a else Lt p.val.endpoint a)
      else (if closed then Le a p.val.endpoint else Lt a p.val.endpoint)) := by
  change M.mem (denote a) (S.sepValue _ _) ↔ _
  rw [S.sep_members]
  cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte, realBound_iff] <;> rfl

theorem realRaySubsetR {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) : Subset p R :=
  fun _ h => (S.sep_members _ _ _).mp h |>.1

theorem notInRealRayOpposite {M : Semantics.{u}} [S : SetSemantics M]
    {lower closed : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower closed α)) (a : Obj (M := M) β)
    (h : if lower then (if closed then Lt a p.val.endpoint else Le a p.val.endpoint)
      else (if closed then Lt p.val.endpoint a else Le p.val.endpoint a)) : ¬ In a p := by
  intro hi
  have hb := ((S.sep_members _ _ _).mp hi).2
  cases lower <;> cases closed <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hb h <;>
    exact realBound_not_opposite hb h

theorem notInRealRayEndpoint {M : Semantics.{u}} [SetSemantics M]
    {lower : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (RealRayObj (M := M) lower false α)) (a : Obj (M := M) β)
    (h : Same a p.val.endpoint) : ¬ In a p := by
  intro hi
  have hb := ((inRealRay_iff p a).mp hi).2
  cases lower
  · exact ltNotSame a p.val.endpoint hb h
  · exact ltNotSame p.val.endpoint a hb h.symm

/-- Sequence indices are positive naturals, as in the source seq(S) contract. -/
structure SeqSetObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  carrier : Obj (M := M) α

def seqSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) : FunctionSignature M :=
  FunctionSignature.withGuard (denote (NPos (M := M))) (denote A)
    (isSet NPos) (isSet A) (fun _ => True)

instance seqSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] : Representation M (SeqSetObj (M := M) α) where
  wd p := IsSet p.carrier
  denote p := F.fnSetValue (seqSignature p.carrier).domain (denote p.carrier)
  wd_isSet {p} h := F.fnSet_isSet _ _ (seqSignature p.carrier).domain_isSet h

def seqSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (hA : IsSet A) :
    Obj (M := M) (SeqSetObj (M := M) α) := ⟨⟨A⟩,hA⟩

theorem seqSet_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (s : Obj (M := M) (SeqSetObj (M := M) α)) :
    Same s (fnSet (seqSignature s.val.carrier)) := rfl

end Litex

namespace Litex

/-- A total denotation on semantic values; the constructor owns its domain WD. -/
noncomputable def realUnaryValue {M : Semantics.{u}} (f : ℝ → ℝ) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((f (Classical.choose h) : ℝ) : ℂ) else M.number 0

theorem realUnaryValue_number {M : Semantics.{u}} (f : ℝ → ℝ) (r : ℝ) :
    realUnaryValue f (M.number (r : ℂ)) = M.number ((f r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold realUnaryValue
  rw [dif_pos h, hr]

structure ExpObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance expRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ExpObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.exp (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.exp r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def exp {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) : Obj (M := M) (ExpObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteExp {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.exp r : ℝ) : ℂ) := by
  change realUnaryValue Real.exp (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

/-- The exponential of a real is nonzero. -/
theorem expNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg p.wd
  have hx : ((Real.exp r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.exp_pos r))
  have hp : denote p = M.number ((Real.exp r : ℝ) : ℂ) := denoteExp p r hr
  intro h
  exact hx (M.number_injective (hp.symm.trans h))

theorem expInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.exp (NativeBridge.asReal p.val.arg p.wd),
    denoteExp p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

theorem expInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) α)) : In p RPos :=
  inRPos_intro p (expInR p) (NativeBridge.ltOfDenoteReal (number 0) p 0 _ rfl
    (denoteExp p _ (NativeBridge.asReal_spec p.val.arg p.wd)) (Real.exp_pos _))

structure LnObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance lnRepresentation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (LnObj (M := M) α) where
  wd a := In a.arg RPos
  denote a := realUnaryValue Real.log (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp (inRPos_real a.arg h)
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.log r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def ln {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a RPos) : Obj (M := M) (LnObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteLn {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.log r : ℝ) : ℂ) := by
  change realUnaryValue Real.log (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem lnInR {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.log (NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)),
    denoteLn p _ (NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd))⟩

/-- The exponential preserves and reflects the order of real arguments. -/
theorem expLtIff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α)) (q : Obj (M := M) (ExpObj (M := M) β)) :
    Lt p q ↔ Lt p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg p.wd
  let y := NativeBridge.asReal q.val.arg q.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hy := NativeBridge.asReal_spec q.val.arg q.wd
  exact (NativeBridge.lt_iff_ofDenoteReal p q (Real.exp x) (Real.exp y) (denoteExp p x hx) (denoteExp q y hy)).trans
    (Real.exp_lt_exp.trans (NativeBridge.lt_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

theorem expLeIff {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α)) (q : Obj (M := M) (ExpObj (M := M) β)) :
    Le p q ↔ Le p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg p.wd
  let y := NativeBridge.asReal q.val.arg q.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hy := NativeBridge.asReal_spec q.val.arg q.wd
  exact (NativeBridge.le_iff_ofDenoteReal p q (Real.exp x) (Real.exp y) (denoteExp p x hx) (denoteExp q y hy)).trans
    (Real.exp_le_exp.trans (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

/-- The logarithm preserves and reflects order on positive real arguments. -/
theorem lnLtIff {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α)) (q : Obj (M := M) (LnObj (M := M) β)) :
    Lt p q ↔ Lt p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)
  let y := NativeBridge.asReal q.val.arg (inRPos_real _ q.wd)
  have hx := NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd)
  have hy := NativeBridge.asReal_spec q.val.arg (inRPos_real _ q.wd)
  have hx0 : 0 < x := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 x rfl hx).mp (inRPos_positive _ p.wd)
  have hy0 : 0 < y := (NativeBridge.lt_iff_ofDenoteReal (number 0) q.val.arg 0 y rfl hy).mp (inRPos_positive _ q.wd)
  exact (NativeBridge.lt_iff_ofDenoteReal p q (Real.log x) (Real.log y) (denoteLn p x hx) (denoteLn q y hy)).trans
    ((Real.log_lt_log_iff hx0 hy0).trans (NativeBridge.lt_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

theorem lnLeIff {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α)) (q : Obj (M := M) (LnObj (M := M) β)) :
    Le p q ↔ Le p.val.arg q.val.arg := by
  let x := NativeBridge.asReal p.val.arg (inRPos_real _ p.wd)
  let y := NativeBridge.asReal q.val.arg (inRPos_real _ q.wd)
  have hx := NativeBridge.asReal_spec p.val.arg (inRPos_real _ p.wd)
  have hy := NativeBridge.asReal_spec q.val.arg (inRPos_real _ q.wd)
  have hx0 : 0 < x := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 x rfl hx).mp (inRPos_positive _ p.wd)
  have hy0 : 0 < y := (NativeBridge.lt_iff_ofDenoteReal (number 0) q.val.arg 0 y rfl hy).mp (inRPos_positive _ q.wd)
  exact (NativeBridge.le_iff_ofDenoteReal p q (Real.log x) (Real.log y) (denoteLn p x hx) (denoteLn q y hy)).trans
    ((Real.log_le_log_iff hx0 hy0).trans (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).symm)

structure LogObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  base : Obj (M := M) α
  arg : Obj (M := M) β

theorem logBaseNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (r : ℝ) (hr : denote a = M.number (r : ℂ))
    (h0 : Lt (number 0) a) (h1 : ¬ Same a (number 1)) : (Real.log r : ℂ) ≠ 0 := by
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp h0
  have hr1 : r ≠ 1 := by
    intro heq
    apply h1
    change denote a = M.number 1
    simpa only [heq, Complex.ofReal_one] using hr
  exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hr0 hr1

noncomputable instance logRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (LogObj (M := M) α β) where
  wd p := In p.base R ∧ In p.arg R ∧ Lt (number 0) p.base ∧
    Lt (number 0) p.arg ∧ ¬ Same p.base (number 1)
  denote p := M.divValue (realUnaryValue Real.log (denote p.arg)) (realUnaryValue Real.log (denote p.base))
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    obtain ⟨s, hs⟩ := (M.real_members _).mp h.2.1
    have hn := logBaseNonzero p.base r hr h.2.2.1 h.2.2.2.2
    rw [hr, hs, realUnaryValue_number, realUnaryValue_number, M.div_numbers _ _ hn]
    exact M.member_isSet ((M.complex_members _).mpr ⟨_, rfl⟩)

noncomputable def log {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) (ha0 : Lt (number 0) a) (hb0 : Lt (number 0) b)
    (ha1 : ¬ Same a (number 1)) : Obj (M := M) (LogObj (M := M) α β) := ⟨⟨a,b⟩,ha,hb,ha0,hb0,ha1⟩

theorem denoteLog {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β))
    (r s : ℝ) (hr : denote p.val.base = M.number (r : ℂ))
    (hs : denote p.val.arg = M.number (s : ℂ)) :
    denote p = M.number (((Real.log s / Real.log r) : ℝ) : ℂ) := by
  change M.divValue (realUnaryValue Real.log (denote p.val.arg)) (realUnaryValue Real.log (denote p.val.base)) = _
  have hn := logBaseNonzero p.val.base r hr p.wd.2.2.1 p.wd.2.2.2.2
  rw [hr, hs, realUnaryValue_number, realUnaryValue_number, M.div_numbers _ _ hn, Complex.ofReal_div]

theorem logNonzeroOfGuards {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β))
    (hb0 : Lt (number 0) p.val.base) (hb1 : ¬ Same p.val.base (number 1))
    (ha0 : Lt (number 0) p.val.arg) (ha1 : ¬ Same p.val.arg (number 1)) : ¬ Same p (number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s,hs⟩ := (M.real_members _).mp p.wd.2.1
  have hbr : Real.log r ≠ 0 := by
    have h := logBaseNonzero p.val.base r hr hb0 hb1
    exact_mod_cast h
  have har : Real.log s ≠ 0 := by
    have h := logBaseNonzero p.val.arg s hs ha0 ha1
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p (((Real.log s / Real.log r : ℝ) : ℂ)) (denoteLog p r s hr hs)
  exact_mod_cast (div_ne_zero har hbr)

theorem powerNonunitOfGuards {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hb0 : Lt (number 0) p.val.base) (hb1 : ¬ Same p.val.base (number 1))
    (heZ : In p.val.exponent Z) (he0 : ¬ Same p.val.exponent (number 0)) :
    ¬ Same p (number 1) := by
  obtain ⟨r0,r,hr0,hr,hlt⟩ := hb0
  have hzero : r0 = 0 := Complex.ofReal_injective (M.number_injective hr0.symm)
  have hrpos : 0 < r := hzero ▸ hlt
  have hr1 : r ≠ 1 := by
    intro h
    apply hb1
    change denote p.val.base = M.number 1
    simpa only [h, Complex.ofReal_one] using hr
  obtain ⟨n, hn⟩ := (M.integer_members _).mp heZ
  have hn0 : n ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.exponent (n : ℂ) hn he0
    exact_mod_cast h
  have hbase0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  have hp : denote p = M.number ((r : ℂ) ^ n) := by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hr, hn, M.pow_numbers_int _ _ hbase0]
  intro he
  change denote p = M.number 1 at he
  have hpower : r ^ n = 1 := by
    have h := M.number_injective (hp.symm.trans he)
    exact_mod_cast h
  exact hn0 ((zpow_eq_one_iff_right₀ (le_of_lt hrpos) hr1).mp hpower)

theorem logInR {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LogObj (M := M) α β)) : In p R :=
  (M.real_members _).mpr ⟨_, denoteLog p _ _ (NativeBridge.asReal_spec p.val.base p.wd.1)
    (NativeBridge.asReal_spec p.val.arg p.wd.2.1)⟩

theorem lnExp {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) (ExpObj (M := M) α))) :
    Same p p.val.arg.val.arg := by
  let r := NativeBridge.asReal p.val.arg.val.arg p.val.arg.wd
  have hr := NativeBridge.asReal_spec p.val.arg.val.arg p.val.arg.wd
  change denote p = _
  rw [denoteLn p (Real.exp r) (denoteExp p.val.arg r hr), Real.log_exp]
  exact hr.symm

theorem expLn {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (ExpObj (M := M) (LnObj (M := M) α)))
    (h : Lt (number 0) p.val.arg.val.arg) : Same p p.val.arg.val.arg := by
  let r := NativeBridge.asReal p.val.arg.val.arg (inRPos_real _ p.val.arg.wd)
  have hr := NativeBridge.asReal_spec p.val.arg.val.arg (inRPos_real _ p.val.arg.wd)
  have h0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg.val.arg 0 r rfl hr).mp h
  change denote p = _
  rw [denoteExp p (Real.log r) (denoteLn p.val.arg r hr), Real.exp_log h0]
  exact hr.symm

end Litex

namespace Litex
theorem rationalLogValue (b x : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hb : 0 < b) (hb1 : b ≠ 1) (hpower : x ^ q = b ^ p) :
    Real.log x / Real.log b = (p : ℝ) / (q : ℝ) := by
  have hn := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hq)
  have h := congrArg Real.log hpower
  rw [Real.log_pow, Real.log_zpow] at h
  field_simp
  nlinarith
theorem logGuardAbove {M : Semantics} {α : Type*} [Representation M α]
    (a : Obj (M := M) α) (h : Lt (number 1) a) :
    Lt (number 0) a ∧ ¬ Same a (number 1) := by
  refine ⟨ltTrans (number 0) (number 1) a ?_ h, ?_⟩
  · exact NativeBridge.ltOfDenoteReal (number 0) (number 1) 0 1 rfl rfl (by norm_num)
  · exact fun heq => ltNotSame (number 1) a h heq.symm

theorem logOne {M : Semantics} {α β : Type*} [Representation M α] [Representation M β]
    (p : Obj (M := M) (LogObj (M := M) α β)) (harg : Same p.val.arg (number 1))
    (hpos : Lt (number 0) p.val.base) (hne : ¬ Same p.val.base (number 1)) :
    Same p (number 0) := by
  let r := NativeBridge.asReal p.val.base p.wd.1
  have hr := NativeBridge.asReal_spec p.val.base p.wd.1
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero p.val.base r hr hpos hne)
  have hs : denote p.val.arg = M.number ((1 : ℝ) : ℂ) := by
    change denote p.val.arg = M.number 1 at harg
    simpa only [Complex.ofReal_one] using harg
  change denote p = M.number 0
  rw [denoteLog p r 1 hr hs]
  have hv : Real.log 1 / Real.log r = 0 := (div_eq_iff hn).mpr (by simp only [Real.log_one, zero_mul])
  rw [hv, Complex.ofReal_zero]

theorem logSelf {M : Semantics} {α β : Type*} [Representation M α] [Representation M β]
    (p : Obj (M := M) (LogObj (M := M) α β)) (harg : Same p.val.arg p.val.base)
    (hpos : Lt (number 0) p.val.base) (hne : ¬ Same p.val.base (number 1)) :
    Same p (number 1) := by
  let r := NativeBridge.asReal p.val.base p.wd.1
  have hr := NativeBridge.asReal_spec p.val.base p.wd.1
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero p.val.base r hr hpos hne)
  change denote p = M.number 1
  rw [denoteLog p r r hr (harg.trans hr), div_self hn, Complex.ofReal_one]

theorem lnEuler {M : Semantics} [SetSemantics M] {α : Type*} [Representation M α]
    (p : Obj (M := M) (LnObj (M := M) α))
    (h : denote p.val.arg = M.number ((Real.exp 1 : ℝ) : ℂ)) : Same p (number 1) := by
  change denote p = M.number 1
  rw [denoteLn p (Real.exp 1) h, Real.log_exp, Complex.ofReal_one]

theorem eulerNonunit {M : Semantics.{u}} :
    ¬ Same (number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (number 1) := by
  intro h
  change M.number ((Real.exp 1 : ℝ) : ℂ) = M.number 1 at h
  have hr : Real.exp (1 : ℝ) = 1 := by
    have hc := M.number_injective h
    exact_mod_cast hc
  have hp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  exact (ne_of_gt hp) hr
end Litex

namespace Litex

structure SinObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sinRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SinObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.sin (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sin r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SinObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sin r : ℝ) : ℂ) := by
  change realUnaryValue Real.sin (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sinInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.sin (NativeBridge.asReal p.val.arg p.wd),
    denoteSin p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CosObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cosRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CosObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.cos (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.cos r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (CosObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteCos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CosObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.cos r : ℝ) : ℂ) := by
  change realUnaryValue Real.cos (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cosInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CosObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.cos (NativeBridge.asReal p.val.arg p.wd),
    denoteCos p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure TanObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance tanRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (TanObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.cos (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue Real.tan (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.tan r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def tan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (cos a ha) (number 0)) :
    Obj (M := M) (TanObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteTan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.tan r : ℝ) : ℂ) := by
  change realUnaryValue Real.tan (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem tanInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.tan (NativeBridge.asReal p.val.arg p.wd.1),
    denoteTan p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem sinSqAddCosSq (x : ℝ) :
    (Real.sin x : ℂ)^2 + (Real.cos x : ℂ)^2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

theorem tanQuotient (x : ℝ) :
    (Real.tan x : ℂ) = (Real.sin x : ℂ) / (Real.cos x : ℂ) := by
  rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
end Litex

namespace Litex
theorem tanPiDivSix : Real.tan (Real.pi / 6) = Real.sqrt 3 / 3 := by
  rw [Real.tan_pi_div_six]
  apply (div_eq_div_iff (by positivity) (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
end Litex

namespace Litex
noncomputable def complexUnaryValue {M : Semantics.{u}} (f : ℂ → ℂ) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ z : ℂ, x = M.number z then
    M.number (f (Classical.choose h)) else M.number 0

theorem complexUnaryValue_number {M : Semantics.{u}} (f : ℂ → ℂ) (z : ℂ) :
    complexUnaryValue f (M.number z) = M.number (f z) := by
  classical
  have h : ∃ w : ℂ, M.number z = M.number w := ⟨z, rfl⟩
  have hz : Classical.choose h = z := (M.number_injective (Classical.choose_spec h)).symm
  unfold complexUnaryValue
  rw [dif_pos h, hz]

structure ConjugateObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance conjRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ConjugateObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => star z) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨star z, by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def conj {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ConjugateObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteConjugate {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number (star z) := by
  change complexUnaryValue (fun z : ℂ => star z) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem conjInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨star z, denoteConjugate p z hz⟩

structure RealPartObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance reRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (RealPartObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(z.re : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def re {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (RealPartObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteRealPart {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((z.re : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (z.re : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem reInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(z.re : ℂ), denoteRealPart p z hz⟩

theorem reInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RealPartObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨z.re, denoteRealPart p z hz⟩

structure ImaginaryPartObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance imgRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ImaginaryPartObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (z.im : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(z.im : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def img {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ImaginaryPartObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteImaginaryPart {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((z.im : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (z.im : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem imgInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(z.im : ℂ), denoteImaginaryPart p z hz⟩

theorem imgInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ImaginaryPartObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨z.im, denoteImaginaryPart p z hz⟩

structure ComplexAbsObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance complexAbsRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ComplexAbsObj (M := M) α) where
  wd a := In a.arg C
  denote a := complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨z, hz⟩ := (M.complex_members _).mp h
    exact M.member_isSet ((M.complex_members _).mpr ⟨(‖z‖ : ℂ), by
      rw [hz, complexUnaryValue_number]⟩)

noncomputable def complexAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) : Obj (M := M) (ComplexAbsObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteComplexAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) (z : ℂ)
    (hz : denote p.val.arg = M.number z) : denote p = M.number ((‖z‖ : ℂ)) := by
  change complexUnaryValue (fun z : ℂ => (‖z‖ : ℂ)) (denote p.val.arg) = _
  rw [hz, complexUnaryValue_number]

theorem complexAbsEqSqrtOfNormSq {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β)) (z : ℂ) (r : ℝ)
    (hz : denote p.val.arg = M.number z)
    (hr : denote q.val.arg = M.number (r : ℂ))
    (hnorm : Complex.normSq z = r) : Same p q := by
  have hp := denoteComplexAbs p z hz
  have hq := NativeBridge.denoteSqrt q.val.arg q.wd.1 q.wd.2 r hr
  change denote p = denote q
  rw [Complex.norm_def, hnorm] at hp
  exact hp.trans hq.symm

theorem complexAbsInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) : In p C := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.complex_members _).mpr ⟨(‖z‖ : ℂ), denoteComplexAbs p z hz⟩

theorem complexAbsInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α)) : In p R := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  exact (M.real_members _).mpr ⟨‖z‖, denoteComplexAbs p z hz⟩

theorem conjugateNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ConjugateObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  have hz0 := NativeBridge.nativeNonzeroOfDenote p.val.arg z hz ha
  apply NativeBridge.notSameOfNativeNonzero p (star z) (denoteConjugate p z hz)
  simpa using hz0

theorem complexAbsNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ComplexAbsObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨z,hz⟩ := (M.complex_members _).mp p.wd
  have hz0 := NativeBridge.nativeNonzeroOfDenote p.val.arg z hz ha
  apply NativeBridge.notSameOfNativeNonzero p ((‖z‖ : ℝ) : ℂ) (denoteComplexAbs p z hz)
  exact_mod_cast (norm_ne_zero_iff.mpr hz0)

theorem complexReconstruction (z : ℂ) : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z :=
  Complex.re_add_im z
end Litex

namespace Litex

noncomputable def nativeCot (x : ℝ) : ℝ := Real.cos x / Real.sin x
noncomputable def nativeSec (x : ℝ) : ℝ := 1 / Real.cos x
noncomputable def nativeCsc (x : ℝ) : ℝ := 1 / Real.sin x
-- Litex uses the principal cotangent inverse in (0, pi).
noncomputable def nativeArccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

theorem nativeCot_arccot (x : ℝ) : nativeCot (nativeArccot x) = x := by
  rw [nativeCot, nativeArccot, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos, Real.tan_arctan]

theorem nativeArccot_pos (x : ℝ) : 0 < nativeArccot x :=
  sub_pos.mpr (Real.arctan_lt_pi_div_two x)

theorem nativeArccot_lt_pi (x : ℝ) : nativeArccot x < Real.pi := by
  unfold nativeArccot
  linarith [Real.neg_pi_div_two_lt_arctan x]

theorem sin_nativeArccot_pos (x : ℝ) : 0 < Real.sin (nativeArccot x) := by
  rw [nativeArccot, Real.sin_pi_div_two_sub]
  exact Real.cos_arctan_pos x


structure ArctanObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arctanRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArctanObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.arctan (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arctan r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (ArctanObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteArctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arctan r : ℝ) : ℂ) := by
  change realUnaryValue Real.arctan (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arctanInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arctan (NativeBridge.asReal p.val.arg p.wd),
    denoteArctan p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩


structure ArccotObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arccotRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArccotObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue nativeArccot (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeArccot r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (ArccotObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteArccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeArccot r : ℝ) : ℂ) := by
  change realUnaryValue nativeArccot (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arccotInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeArccot (NativeBridge.asReal p.val.arg p.wd),
    denoteArccot p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩


structure ArcsinObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arcsinRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArcsinObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number (-1)) a.arg ∧ Le a.arg (number 1)
  denote a := realUnaryValue Real.arcsin (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arcsin r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hlo : Le (number (-1)) a) (hhi : Le a (number 1)) :
    Obj (M := M) (ArcsinObj (M := M) α) := ⟨⟨a⟩,⟨ha,hlo,hhi⟩⟩

theorem denoteArcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arcsin r : ℝ) : ℂ) := by
  change realUnaryValue Real.arcsin (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arcsinInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arcsin (NativeBridge.asReal p.val.arg p.wd.1),
    denoteArcsin p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure ArccosObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance arccosRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (ArccosObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number (-1)) a.arg ∧ Le a.arg (number 1)
  denote a := realUnaryValue Real.arccos (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.arccos r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def arccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hlo : Le (number (-1)) a) (hhi : Le a (number 1)) :
    Obj (M := M) (ArccosObj (M := M) α) := ⟨⟨a⟩,⟨ha,hlo,hhi⟩⟩

theorem denoteArccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.arccos r : ℝ) : ℂ) := by
  change realUnaryValue Real.arccos (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem arccosInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.arccos (NativeBridge.asReal p.val.arg p.wd.1),
    denoteArccos p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure CotObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cotRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CotObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.sin (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeCot (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCot r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (sin a ha) (number 0)) :
    Obj (M := M) (CotObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteCot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CotObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCot r : ℝ) : ℂ) := by
  change realUnaryValue nativeCot (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cotInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CotObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCot (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCot p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem sinNonzeroOfNegatedArg {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SinObj (M := M) α)) (q : Obj (M := M) (SinObj (M := M) β))
    (harg : denote p.val.arg = M.negValue (denote q.val.arg))
    (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal q.val.arg q.wd
  have hr := NativeBridge.asReal_spec q.val.arg q.wd
  have hp : denote p.val.arg = M.number ((-r : ℝ) : ℂ) := by
    rw [harg, hr, M.neg_numbers, Complex.ofReal_neg]
  have hs : Real.sin r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.sin r : ℝ) : ℂ) (denoteSin q r hr) hn
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p ((Real.sin (-r) : ℝ) : ℂ) (denoteSin p (-r) hp)
  exact_mod_cast (show Real.sin (-r) ≠ 0 from by simpa using hs)

theorem cosNonzeroOfNegatedArg {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CosObj (M := M) α)) (q : Obj (M := M) (CosObj (M := M) β))
    (harg : denote p.val.arg = M.negValue (denote q.val.arg))
    (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal q.val.arg q.wd
  have hr := NativeBridge.asReal_spec q.val.arg q.wd
  have hp : denote p.val.arg = M.number ((-r : ℝ) : ℂ) := by
    rw [harg, hr, M.neg_numbers, Complex.ofReal_neg]
  have hc : Real.cos r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.cos r : ℝ) : ℂ) (denoteCos q r hr) hn
    exact_mod_cast h
  apply NativeBridge.notSameOfNativeNonzero p ((Real.cos (-r) : ℝ) : ℂ) (denoteCos p (-r) hp)
  exact_mod_cast (show Real.cos (-r) ≠ 0 from by simpa using hc)

theorem tanNonzeroOfSin {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (TanObj (M := M) α)) (q : Obj (M := M) (SinObj (M := M) β))
    (harg : Same p.val.arg q.val.arg) (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hq : denote q.val.arg = M.number (r : ℂ) := harg.symm.trans hr
  have hs : Real.sin r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.sin r : ℝ) : ℂ) (denoteSin q r hq) hn
    exact_mod_cast h
  have hc : Real.cos r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  have ht : Real.tan r ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hs hc
  apply NativeBridge.notSameOfNativeNonzero p ((Real.tan r : ℝ) : ℂ) (denoteTan p r hr)
  exact_mod_cast ht

theorem cotNonzeroOfCos {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (CotObj (M := M) α)) (q : Obj (M := M) (CosObj (M := M) β))
    (harg : Same p.val.arg q.val.arg) (hn : ¬ Same q (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hq : denote q.val.arg = M.number (r : ℂ) := harg.symm.trans hr
  have hc : Real.cos r ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote q ((Real.cos r : ℝ) : ℂ) (denoteCos q r hq) hn
    exact_mod_cast h
  have hs : Real.sin r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  have ht : nativeCot r ≠ 0 := by
    unfold nativeCot
    exact div_ne_zero hc hs
  apply NativeBridge.notSameOfNativeNonzero p ((nativeCot r : ℝ) : ℂ) (denoteCot p r hr)
  exact_mod_cast ht


structure SecObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance secRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SecObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.cos (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeSec (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeSec r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sec {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (cos a ha) (number 0)) :
    Obj (M := M) (SecObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteSec {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeSec r : ℝ) : ℂ) := by
  change realUnaryValue nativeSec (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem secInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeSec (NativeBridge.asReal p.val.arg p.wd.1),
    denoteSec p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


structure CscObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cscRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CscObj (M := M) α) where
  wd a := In a.arg R ∧ realUnaryValue Real.sin (denote a.arg) ≠ M.number 0
  denote a := realUnaryValue nativeCsc (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCsc r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def csc {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hne : ¬ Same (sin a ha) (number 0)) :
    Obj (M := M) (CscObj (M := M) α) := ⟨⟨a⟩,⟨ha,hne⟩⟩

theorem denoteCsc {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCsc r : ℝ) : ℂ) := by
  change realUnaryValue nativeCsc (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cscInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCsc (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCsc p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩


theorem cosArctanNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) :
    ¬ Same (cos p (arctanInR p)) (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.cos (denote p) ≠ M.number 0
  rw [denoteArctan p r hr, realUnaryValue_number]
  intro h
  have hz : Real.cos (Real.arctan r) = 0 :=
    Complex.ofReal_injective (M.number_injective h)
  exact (Real.cos_arctan_pos r).ne' hz


theorem sinArccotNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) :
    ¬ Same (sin p (arccotInR p)) (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.sin (denote p) ≠ M.number 0
  rw [denoteArccot p r hr, realUnaryValue_number]
  intro h
  have hz : Real.sin (nativeArccot r) = 0 :=
    Complex.ofReal_injective (M.number_injective h)
  exact (sin_nativeArccot_pos r).ne' hz


theorem sinArcsin {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArcsinObj (M := M) α)) :
    Same (sin p (arcsinInR p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hlo : -1 ≤ r := (NativeBridge.le_iff_ofDenoteReal
    (number (-1)) p.val.arg (-1) r (by
      change M.number (-1) = M.number ((-1 : ℝ) : ℂ)
      rw [Complex.ofReal_neg, Complex.ofReal_one]) hr).mp p.wd.2.1
  have hhi : r ≤ 1 := (NativeBridge.le_iff_ofDenoteReal
    p.val.arg (number 1) r 1 hr rfl).mp p.wd.2.2
  change realUnaryValue Real.sin (denote p) = denote p.val.arg
  rw [denoteArcsin p r hr, realUnaryValue_number, Real.sin_arcsin hlo hhi, hr]


theorem cosArccos {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccosObj (M := M) α)) :
    Same (cos p (arccosInR p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hlo : -1 ≤ r := (NativeBridge.le_iff_ofDenoteReal
    (number (-1)) p.val.arg (-1) r (by
      change M.number (-1) = M.number ((-1 : ℝ) : ℂ)
      rw [Complex.ofReal_neg, Complex.ofReal_one]) hr).mp p.wd.2.1
  have hhi : r ≤ 1 := (NativeBridge.le_iff_ofDenoteReal
    p.val.arg (number 1) r 1 hr rfl).mp p.wd.2.2
  change realUnaryValue Real.cos (denote p) = denote p.val.arg
  rw [denoteArccos p r hr, realUnaryValue_number, Real.cos_arccos hlo hhi, hr]


theorem tanArctan {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArctanObj (M := M) α)) :
    Same (tan p (arctanInR p) (cosArctanNonzero p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue Real.tan (denote p) = denote p.val.arg
  rw [denoteArctan p r hr, realUnaryValue_number, Real.tan_arctan r, hr]


theorem cotArccot {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (ArccotObj (M := M) α)) :
    Same (cot p (arccotInR p) (sinArccotNonzero p)) p.val.arg := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr := NativeBridge.asReal_spec p.val.arg p.wd
  change realUnaryValue nativeCot (denote p) = denote p.val.arg
  rw [denoteArccot p r hr, realUnaryValue_number, nativeCot_arccot r, hr]

end Litex

namespace Litex

theorem secNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hd : Real.cos r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  change denote p ≠ M.number 0
  rw [denoteSec p r hr]
  intro h
  have hz : 1 / Real.cos r = 0 := Complex.ofReal_injective (M.number_injective h)
  exact (one_div_ne_zero hd) hz

theorem secInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (SecObj (M := M) α)) : In p RStar :=
  inRStar_intro p (secInR p) (secNonzero p)

theorem cscNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hd : Real.sin r ≠ 0 := by
    intro h
    apply p.wd.2
    rw [hr, realUnaryValue_number, h, Complex.ofReal_zero]
  change denote p ≠ M.number 0
  rw [denoteCsc p r hr]
  intro h
  have hz : 1 / Real.sin r = 0 := Complex.ofReal_injective (M.number_injective h)
  exact (one_div_ne_zero hd) hz

theorem cscInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CscObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cscInR p) (cscNonzero p)
end Litex


