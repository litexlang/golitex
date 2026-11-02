import Litex.NumericModel

universe u v w x

namespace Litex

universe t

/-- This representation exists only for values of the chosen semantic model. -/
instance semanticValueRepresentation (M : Semantics.{u}) : Representation M M.Value where
  wd x := M.isSet x
  denote x := x
  wd_isSet h := h

def semanticObject {M : Semantics.{u}} (x : M.Value) (hx : M.isSet x) :
    Obj (M := M) M.Value := ⟨x, hx⟩

/-- A singleton host carrier may represent a certified semantic value at any level. -/
structure ValueAtLevel {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) : Type v where

instance valueAtLevelRepresentation {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) :
    Representation M (ValueAtLevel.{u,v} value certified) where
  wd _ := True
  denote _ := value
  wd_isSet _ := certified

def objectAtLevel {M : Semantics.{u}} (value : M.Value) (certified : M.isSet value) :
    Obj (M := M) (ValueAtLevel.{u,v} value certified) := ⟨⟨⟩, True.intro⟩

theorem semanticObject_denote {M : Semantics.{u}} (x : M.Value) (hx : M.isSet x) :
    denote (semanticObject x hx) = x := rfl

/-- The value of the original canonical witness; construction still requires existence. -/
noncomputable def obtainedValue {M : Semantics.{u}}
    (property : Obj (M := M) M.Value → Prop) : M.Value := by
  classical
  exact if h : ∃ x, property x then denote (Classical.choose h) else M.number 0

theorem obtainedValue_eq {M : Semantics.{u}}
    {property : Obj (M := M) M.Value → Prop} (h : ∃ x, property x) :
    obtainedValue property = denote (Classical.choose h) := by
  classical
  simp only [obtainedValue, dif_pos h]

noncomputable def obtainedObject {M : Semantics.{u}}
    {property : Obj (M := M) M.Value → Prop} (h : ∃ x, property x) :
    Obj (M := M) M.Value :=
  semanticObject (obtainedValue property) (by
    rw [obtainedValue_eq h]
    exact isSet (Classical.choose h))

theorem obtainedObject_eq {M : Semantics.{u}}
    {property : Obj (M := M) M.Value → Prop} (h : ∃ x, property x) :
    obtainedObject h = Classical.choose h := by
  suffices ∀ (a b : Obj (M := M) M.Value), a.val = b.val → a = b from
    this _ _ (obtainedValue_eq h)
  intro a b he
  cases a
  cases b
  cases he
  rfl

theorem obtainedObject_spec {M : Semantics.{u}}
    {property : Obj (M := M) M.Value → Prop} (h : ∃ x, property x) :
    property (obtainedObject h) := by
  rw [obtainedObject_eq h]
  exact Classical.choose_spec h

theorem obtainedObject_denote {M : Semantics.{u}}
    {property : Obj (M := M) M.Value → Prop} (h : ∃ x, property x) :
    denote (obtainedObject h) = obtainedValue property := rfl

/-- The real-line existence rule chooses a semantic real above its free operand. -/
theorem existsRealAbove {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    ∃ b : Obj (M := M) M.Value, In b R ∧ Lt a b := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
  have hb := NativeBridge.numberInR (M := M) (r + 1)
  exact ⟨semanticObject (M.number ((r + 1 : ℝ) : ℂ)) (M.member_isSet hb),
    hb, r, r + 1, hr, rfl, lt_add_one r⟩

/-- The same rule chooses a semantic real below its free operand. -/
theorem existsRealBelow {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    ∃ b : Obj (M := M) M.Value, In b R ∧ Lt b a := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
  have hb := NativeBridge.numberInR (M := M) (r - 1)
  exact ⟨semanticObject (M.number ((r - 1 : ℝ) : ℂ)) (M.member_isSet hb),
    hb, r - 1, r, rfl, hr, sub_one_lt r⟩

namespace NativeBridge

@[simp] theorem asComplex_semanticObject {M : Semantics.{u}} {α : Type v}
    [Representation M α] (a : Obj (M := M) α) (hs : M.isSet (denote a))
    (hc : In (semanticObject (denote a) hs) C) :
    asComplex (semanticObject (denote a) hs) hc = asComplex a hc :=
  M.number_injective
    ((asComplex_spec (semanticObject (denote a) hs) hc).symm.trans (asComplex_spec a hc))

@[simp] theorem asComplex_semanticNumber {M : Semantics.{u}} (z : ℂ)
    (hs : M.isSet (M.number z)) (hc : In (semanticObject (M.number z) hs) C) :
    asComplex (semanticObject (M.number z) hs) hc = z :=
  M.number_injective (asComplex_spec (semanticObject (M.number z) hs) hc).symm

theorem naturalValue_lt_number {M : Semantics.{u}} (n : ℕ) (x : M.Value)
    (hx : M.mem x (M.standard .natural))
    (hLt : Lt (semanticObject x (M.member_isSet hx)) (number (n : ℂ))) :
    naturalValue x < n := by
  have h := (lt_iff_ofDenoteReal (semanticObject x (M.member_isSet hx))
    (number (n : ℂ)) (naturalValue x : ℝ) (n : ℝ)
    (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using naturalValue_spec x hx)
    (by simp only [denoteNumber, Complex.ofReal_natCast])).mp hLt
  exact_mod_cast h

theorem naturalValue_pos {M : Semantics.{u}} (x : M.Value)
    (hx : M.mem x (M.standard .natural))
    (hLt : Lt (number 0) (semanticObject x (M.member_isSet hx))) :
    0 < naturalValue x := by
  have h := (lt_iff_ofDenoteReal (number 0) (semanticObject x (M.member_isSet hx))
    0 (naturalValue x : ℝ) rfl
    (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using naturalValue_spec x hx)).mp hLt
  exact_mod_cast h

end NativeBridge

/-- The exported index keeps its original representation. Only the proof
interpretation observes a nonnegative integer as a natural number. -/
theorem integerInductionFromZero {M : Semantics.{u}}
    (P : M.Value → Prop) (h0 : P (M.number 0))
    (hstep : ∀ (k : M.Value) (hkZ : M.mem k (M.standard .integer)),
      Le (number 0) (semanticObject k (M.member_isSet hkZ)) →
      P k → P (M.addValue k (M.number 1)))
    {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : P (denote a) := by
  have hn := integerToNaturalOfNonnegative a haZ ha0
  have hall : ∀ n : ℕ, P (M.number (n : ℂ)) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero] using h0
    | succ n ih =>
      have hz : M.mem (M.number (n : ℂ)) (M.standard .integer) :=
        (M.integer_members _).mpr ⟨(n : ℤ), by simp only [Int.cast_natCast]⟩
      have hnonnegative := naturalNonnegative
        (semanticObject (M.number (n : ℂ)) (M.member_isSet hz))
        (NativeBridge.numberInN n)
      simpa only [M.add_numbers, Nat.cast_add, Nat.cast_one] using
        hstep (M.number (n : ℂ)) hz hnonnegative ih
  exact (NativeBridge.asNat_spec a hn).symm ▸ hall (NativeBridge.asNat a hn)

/-- Strong induction uses precisely the integer indices from zero through the
current predecessor. The exported object keeps its original representation. -/
theorem integerStrongInductionFromZero {M : Semantics.{u}}
    (P : M.Value → Prop) (h0 : P (M.number 0))
    (hstep : ∀ (k : M.Value) (hkZ : M.mem k (M.standard .integer)),
      Le (number 0) (semanticObject k (M.member_isSet hkZ)) →
      (∀ (m : M.Value) (hmZ : M.mem m (M.standard .integer)),
        Le (number 0) (semanticObject m (M.member_isSet hmZ)) →
        Le (semanticObject m (M.member_isSet hmZ))
          (semanticObject k (M.member_isSet hkZ)) → P m) →
      P (M.addValue k (M.number 1)))
    {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : P (denote a) := by
  have hn := integerToNaturalOfNonnegative a haZ ha0
  have hall : ∀ n : ℕ, P (M.number (n : ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simpa only [Nat.cast_zero] using h0
      | succ k =>
        have hkZ : M.mem (M.number (k : ℂ)) (M.standard .integer) :=
          (M.integer_members _).mpr ⟨(k : ℤ), by simp only [Int.cast_natCast]⟩
        have hk0 := naturalNonnegative
          (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))
          (NativeBridge.numberInN k)
        have previous (m : M.Value) (hmZ : M.mem m (M.standard .integer))
            (hm0 : Le (number 0) (semanticObject m (M.member_isSet hmZ)))
            (hmk : Le (semanticObject m (M.member_isSet hmZ))
              (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))) : P m := by
          have hmN := integerToNaturalOfNonnegative
            (semanticObject m (M.member_isSet hmZ)) hmZ hm0
          obtain ⟨j, hj⟩ := (M.natural_members m).mp hmN
          have hle := (NativeBridge.le_iff_ofDenoteReal
            (semanticObject m (M.member_isSet hmZ))
            (semanticObject (M.number (k : ℂ)) (M.member_isSet hkZ))
            (j : ℝ) (k : ℝ)
            (by simpa only [semanticObject_denote, Complex.ofReal_natCast] using hj)
            (by simp only [semanticObject_denote, Complex.ofReal_natCast])).mp hmk
          have hjk : j ≤ k := by exact_mod_cast hle
          exact hj.symm ▸ ih j (Nat.lt_succ_of_le hjk)
        simpa only [M.add_numbers, Nat.cast_add, Nat.cast_one] using
          hstep (M.number (k : ℂ)) hkZ hk0 previous
  exact (NativeBridge.asNat_spec a hn).symm ▸ hall (NativeBridge.asNat a hn)

/-- The bounded set primitives are shared by set builders and function domains.
The laws are explicit model obligations, proved by the ZF model below. -/
class SetSemantics (M : Semantics.{u}) where
  emptyValue : M.Value
  empty_members : ∀ x, ¬ M.mem x emptyValue
  empty_isSet : M.isSet emptyValue
  insertValue : M.Value → M.Value → M.Value
  insert_members : ∀ a A x, M.mem x (insertValue a A) ↔ x = a ∨ M.mem x A
  insert_isSet : ∀ a A, M.isSet a → M.isSet A → M.isSet (insertValue a A)
  sepValue : M.Value → (M.Value → Prop) → M.Value
  sep_members : ∀ D p x, M.mem x (sepValue D p) ↔ M.mem x D ∧ p x
  sep_isSet : ∀ D p, M.isSet D → M.isSet (sepValue D p)
  unionValue : M.Value → M.Value → M.Value
  union_members : ∀ A B x, M.mem x (unionValue A B) ↔ M.mem x A ∨ M.mem x B
  union_isSet : ∀ A B, M.isSet A → M.isSet B → M.isSet (unionValue A B)
  powerValue : M.Value → M.Value
  power_members : ∀ A B, M.mem B (powerValue A) ↔
    M.isSet B ∧ ∀ x, M.mem x B → M.mem x A
  power_isSet : ∀ A, M.isSet A → M.isSet (powerValue A)
  ext : ∀ A B, M.isSet A → M.isSet B → (∀ x, M.mem x A ↔ M.mem x B) → A = B

noncomputable instance numericSetSemantics : SetSemantics NumericModel.model where
  emptyValue := (∅ : ZFSet.{0})
  empty_members := ZFSet.notMem_empty
  empty_isSet := True.intro
  insertValue := ZFSet.Insert
  insert_members _ _ _ := ZFSet.mem_insert_iff
  insert_isSet _ _ _ _ := True.intro
  sepValue D p := ZFSet.sep p D
  sep_members _ _ _ := ZFSet.mem_sep
  sep_isSet _ _ _ := True.intro
  unionValue := ZFSet.union
  union_members _ _ _ := ZFSet.mem_union
  union_isSet _ _ _ _ := True.intro
  powerValue := ZFSet.powerset
  power_members A B := by
    change B ∈ ZFSet.powerset A ↔ True ∧ ZFSet.Subset B A
    exact ⟨fun h => ⟨True.intro, ZFSet.mem_powerset.mp h⟩,
      fun h => ZFSet.mem_powerset.mpr h.2⟩
  power_isSet _ _ := True.intro
  ext _ _ _ _ := ZFSet.ext

/-- Optional indexed unions for dependent carriers. This does not strengthen
`SetSemantics`: a model supplies this interface when such constructions are used.
The index domain is a set, never a collection of all semantic values. -/
class IndexedUnionSemantics (M : Semantics.{u}) where
  indexedUnionValue : M.Value → (M.Value → M.Value) → M.Value
  indexedUnion_members : ∀ A B x, M.mem x (indexedUnionValue A B) ↔
    ∃ a, M.mem a A ∧ M.mem x (B a)
  indexedUnion_isSet : ∀ A B, M.isSet A →
    (∀ a, M.mem a A → M.isSet (B a)) → M.isSet (indexedUnionValue A B)

noncomputable instance numericIndexedUnionSemantics :
    IndexedUnionSemantics NumericModel.model where
  indexedUnionValue := fun (A : ZFSet.{0}) (B : ZFSet.{0} → ZFSet.{0}) =>
    ZFSet.iUnion (fun a : A => B a.val)
  indexedUnion_members := fun (A : ZFSet.{0}) (B : ZFSet.{0} → ZFSet.{0}) (x : ZFSet.{0}) => by
    change x ∈ ZFSet.iUnion (fun a : A => B a.val) ↔ ∃ a, a ∈ A ∧ x ∈ B a
    constructor
    · intro h
      obtain ⟨a, ha⟩ := ZFSet.mem_iUnion.mp h
      exact ⟨a.val, a.property, ha⟩
    · rintro ⟨a, ha, hx⟩
      exact ZFSet.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  indexedUnion_isSet _ _ _ _ := True.intro

private noncomputable def replacementChoice {M : Semantics.{u}} [S : SetSemantics M]
    (P : M.Value → M.Value → Prop) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ y, M.isSet y ∧ P x y then Classical.choose h else S.emptyValue

private theorem replacementChoice_spec {M : Semantics.{u}} [SetSemantics M]
    (P : M.Value → M.Value → Prop) (x : M.Value) (h : ∃ y, M.isSet y ∧ P x y) :
    M.isSet (replacementChoice P x) ∧ P x (replacementChoice P x) := by
  rw [replacementChoice, dif_pos h]
  exact Classical.choose_spec h

structure ReplacementObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  domain : Obj (M := M) α
  relation : M.Value → M.Value → Prop

noncomputable def replacementValue {M : Semantics.{u}}
    [S : SetSemantics M] [I : IndexedUnionSemantics M]
    (D : M.Value) (P : M.Value → M.Value → Prop) : M.Value :=
  I.indexedUnionValue (S.sepValue D (fun x => ∃ y, M.isSet y ∧ P x y))
    (fun x => S.insertValue (replacementChoice P x) S.emptyValue)

private theorem replacementValue_isSet {M : Semantics.{u}}
    [S : SetSemantics M] [I : IndexedUnionSemantics M]
    (D : M.Value) (P : M.Value → M.Value → Prop) (hD : M.isSet D) :
    M.isSet (replacementValue D P) := by
  apply I.indexedUnion_isSet _ _ (S.sep_isSet _ _ hD)
  intro x hx
  have exists_y := ((S.sep_members _ _ _).mp hx).2
  exact S.insert_isSet _ _ (replacementChoice_spec P x exists_y).1 S.empty_isSet

noncomputable instance replacementRepresentation {M : Semantics.{u}}
    [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] : Representation M (ReplacementObj (M := M) α) where
  wd p := ∀ x, M.mem x (denote p.domain) → ∀ y z,
    M.isSet y → p.relation x y → M.isSet z → p.relation x z → y = z
  denote p := replacementValue (denote p.domain) p.relation
  wd_isSet {p} _ := replacementValue_isSet _ _ (isSet p.domain)

noncomputable def replacement {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (P : M.Value → M.Value → Prop)
    (h : ∀ x, M.mem x (denote D) → ∀ y z, M.isSet y → P x y → M.isSet z → P x z → y = z) :
    Obj (M := M) (ReplacementObj (M := M) α) := ⟨⟨D, P⟩, h⟩

theorem replacement_denote {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (ReplacementObj (M := M) α)) :
    denote p = replacementValue (denote p.val.domain) p.val.relation := rfl

theorem replacement_members {M : Semantics.{u}} [S : SetSemantics M] [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (ReplacementObj (M := M) α))
    (y : M.Value) : M.mem y (denote p) ↔
      ∃ x, M.mem x (denote p.val.domain) ∧ M.isSet y ∧ p.val.relation x y := by
  change M.mem y (replacementValue _ _) ↔ _
  rw [replacementValue, I.indexedUnion_members]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨hxD, hex⟩ := (S.sep_members _ _ _).mp hx
    rcases (S.insert_members _ _ _).mp hy with hy | hy
    · subst y
      exact ⟨x, hxD, replacementChoice_spec _ _ hex⟩
    · exact False.elim (S.empty_members _ hy)
  · rintro ⟨x, hxD, hy, hP⟩
    have hex : ∃ z, M.isSet z ∧ p.val.relation x z := ⟨y, hy, hP⟩
    have hc := replacementChoice_spec p.val.relation x hex
    refine ⟨x, (S.sep_members _ _ _).mpr ⟨hxD, hex⟩, ?_⟩
    apply (S.insert_members _ _ _).mpr
    exact Or.inl (p.wd x hxD y _ hy hP hc.1 hc.2)

theorem replacementIntro {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (ReplacementObj (M := M) α)) (x : Obj (M := M) β) (y : Obj (M := M) γ)
    (hx : In x p.val.domain) (hP : p.val.relation (denote x) (denote y)) : In y p :=
  (replacement_members p (denote y)).mpr ⟨denote x, hx, isSet y, hP⟩

theorem replacementElim {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ReplacementObj (M := M) α)) (y : Obj (M := M) β) (hy : In y p) :
    ∃ x : Obj (M := M) M.Value, ∃ (_ : In x p.val.domain), p.val.relation (denote x) (denote y) := by
  obtain ⟨x, hx, _, hP⟩ := (replacement_members p (denote y)).mp hy
  exact ⟨semanticObject x (M.member_isSet hx), hx, hP⟩

/-- Positivity is a faithful real denotation witness, including its carrier. -/
def positiveRealPredicate {M : Semantics.{u}} (x : M.Value) : Prop :=
  ∃ r : ℝ, x = M.number (r : ℂ) ∧ 0 < r

/-- Positive reals are a bounded separation of the existing real set. -/
def positiveReal {M : Semantics.{u}} [S : SetSemantics M] : M.Value :=
  S.sepValue (M.standard .real) positiveRealPredicate

theorem positiveReal_isSet {M : Semantics.{u}} [S : SetSemantics M] :
    M.isSet (positiveReal (M := M)) :=
  S.sep_isSet _ _ (M.standard_isSet .real)

def RPos {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  semanticObject positiveReal positiveReal_isSet

/-- Positive naturals retain both natural membership and strict positivity. -/
def NPos {M : Semantics.{u}} [S : SetSemantics M] : Obj (M := M) M.Value :=
  semanticObject (S.sepValue (M.standard .natural) positiveRealPredicate)
    (S.sep_isSet _ _ (M.standard_isSet .natural))

theorem inNPos_natural {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a NPos) : In a N :=
  ((S.sep_members _ _ _).mp ha).1

theorem numberInNPosOfEq {M : Semantics.{u}} [S : SetSemantics M]
    (z : ℂ) (n : ℕ) (hz : z = (n : ℂ)) (hn : 0 < n) : In (number z) (NPos (M := M)) := by
  apply (S.sep_members _ _ _).mpr
  refine ⟨(M.natural_members _).mpr ⟨n, congrArg M.number hz⟩, (n : ℝ), ?_, ?_⟩
  · change M.number z = M.number ((n : ℝ) : ℂ)
    simpa only [Complex.ofReal_natCast] using congrArg M.number hz
  · exact_mod_cast hn

/-- A refined numeric carrier is bounded separation, using the existing model. -/
def refinedNumericSet {M : Semantics.{u}} [S : SetSemantics M]
    (base : StandardSetValue) (condition : M.Value → Prop) : Obj (M := M) M.Value :=
  semanticObject (S.sepValue (M.standard base) condition)
    (S.sep_isSet _ _ (M.standard_isSet base))

def negativeRealPredicate {M : Semantics.{u}} (x : M.Value) : Prop :=
  ∃ r : ℝ, x = M.number (r : ℂ) ∧ r < 0

theorem positiveRealPredicate_iff {M : Semantics.{u}}
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    positiveRealPredicate (denote a) ↔ Lt (number 0) a := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact NativeBridge.ltOfDenoteReal (number 0) a 0 r rfl hr h
  · rintro ⟨r, s, hr, hs, h⟩
    have hzero : r = 0 := Complex.ofReal_injective (M.number_injective hr).symm
    exact ⟨s, hs, hzero ▸ h⟩

theorem negativeRealPredicate_iff {M : Semantics.{u}}
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    negativeRealPredicate (denote a) ↔ Lt a (number 0) := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact NativeBridge.ltOfDenoteReal a (number 0) r 0 hr rfl h
  · rintro ⟨r, s, hr, hs, h⟩
    have hzero : s = 0 := Complex.ofReal_injective (M.number_injective hs).symm
    exact ⟨r, hr, hzero ▸ h⟩

def QPos {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational positiveRealPredicate

theorem inQPos_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QPos ↔ In a Q ∧ Lt (number 0) a := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) positiveRealPredicate) ↔ _
  rw [S.sep_members]
  rw [positiveRealPredicate_iff]
  rfl

theorem inQPos_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QPos) :
    In a Q := ((inQPos_iff a).mp ha).1

theorem inQPos_positive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QPos) :
    Lt (number 0) a := ((inQPos_iff a).mp ha).2

theorem inQPos_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : Lt (number 0) a) : In a QPos :=
  (inQPos_iff a).mpr ⟨ha, h⟩

theorem qPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QPos (M := M)) :=
  ⟨M.number (1), inQPos_intro (number (1)) (NativeBridge.numberInQOfEq (M := M) (1) (1 : ℚ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number 0) (number (1)) 0 (1) rfl rfl (by norm_num))⟩

def QNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational negativeRealPredicate

theorem inQNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QNeg ↔ In a Q ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inQNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QNeg) :
    In a Q := ((inQNeg_iff a).mp ha).1

theorem inQNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QNeg) :
    Lt a (number 0) := ((inQNeg_iff a).mp ha).2

theorem inQNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : Lt a (number 0)) : In a QNeg :=
  (inQNeg_iff a).mpr ⟨ha, h⟩

theorem qNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QNeg (M := M)) :=
  ⟨M.number (-1), inQNeg_intro (number (-1)) (NativeBridge.numberInQOfEq (M := M) (-1) (-1 : ℚ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def ZNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .integer negativeRealPredicate

theorem inZNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a ZNeg ↔ In a Z ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .integer) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inZNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZNeg) :
    In a Z := ((inZNeg_iff a).mp ha).1

theorem inZNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZNeg) :
    Lt a (number 0) := ((inZNeg_iff a).mp ha).2

theorem inZNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Z) (h : Lt a (number 0)) : In a ZNeg :=
  (inZNeg_iff a).mpr ⟨ha, h⟩

theorem zNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (ZNeg (M := M)) :=
  ⟨M.number (-1), inZNeg_intro (number (-1)) (NativeBridge.numberInZOfEq (M := M) (-1) (-1 : ℤ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def RNeg {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .real negativeRealPredicate

theorem inRNeg_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RNeg ↔ In a R ∧ Lt a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .real) negativeRealPredicate) ↔ _
  rw [S.sep_members]
  rw [negativeRealPredicate_iff]
  rfl

theorem inRNeg_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RNeg) :
    In a R := ((inRNeg_iff a).mp ha).1

theorem inRNeg_negative {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RNeg) :
    Lt a (number 0) := ((inRNeg_iff a).mp ha).2

theorem inRNeg_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (h : Lt a (number 0)) : In a RNeg :=
  (inRNeg_iff a).mpr ⟨ha, h⟩

theorem rNegNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RNeg (M := M)) :=
  ⟨M.number (-1), inRNeg_intro (number (-1)) (NativeBridge.numberInROfEq (M := M) (-1) (-1 : ℝ) (by norm_num)) (NativeBridge.ltOfDenoteReal (number (-1)) (number 0) (-1) 0 (congrArg M.number (by norm_num [number])) rfl (by norm_num))⟩

def QStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .rational (fun x => x ≠ M.number 0)

theorem inQStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a QStar ↔ In a Q ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .rational) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inQStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QStar) :
    In a Q := ((inQStar_iff a).mp ha).1

theorem inQStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a QStar) :
    ¬ Same a (number 0) := ((inQStar_iff a).mp ha).2

theorem inQStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Q) (h : ¬ Same a (number 0)) : In a QStar :=
  (inQStar_iff a).mpr ⟨ha, h⟩

theorem qStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (QStar (M := M)) :=
  ⟨M.number (1), inQStar_intro (number (1)) (NativeBridge.numberInQOfEq (M := M) (1) (1 : ℚ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def ZStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .integer (fun x => x ≠ M.number 0)

theorem inZStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a ZStar ↔ In a Z ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .integer) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inZStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZStar) :
    In a Z := ((inZStar_iff a).mp ha).1

theorem inZStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a ZStar) :
    ¬ Same a (number 0) := ((inZStar_iff a).mp ha).2

theorem inZStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a Z) (h : ¬ Same a (number 0)) : In a ZStar :=
  (inZStar_iff a).mpr ⟨ha, h⟩

theorem zStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (ZStar (M := M)) :=
  ⟨M.number (1), inZStar_intro (number (1)) (NativeBridge.numberInZOfEq (M := M) (1) (1 : ℤ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def RStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .real (fun x => x ≠ M.number 0)

theorem inRStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RStar ↔ In a R ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .real) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inRStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RStar) :
    In a R := ((inRStar_iff a).mp ha).1

theorem inRStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RStar) :
    ¬ Same a (number 0) := ((inRStar_iff a).mp ha).2

theorem inRStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (h : ¬ Same a (number 0)) : In a RStar :=
  (inRStar_iff a).mpr ⟨ha, h⟩

theorem rStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RStar (M := M)) :=
  ⟨M.number (1), inRStar_intro (number (1)) (NativeBridge.numberInROfEq (M := M) (1) (1 : ℝ) (by norm_num)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

def CStar {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) M.Value :=
  refinedNumericSet .complex (fun x => x ≠ M.number 0)

theorem inCStar_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a CStar ↔ In a C ∧ ¬ Same a (number 0) := by
  change M.mem (denote a) (S.sepValue (M.standard .complex) (fun x => x ≠ M.number 0)) ↔ _
  rw [S.sep_members]
  rfl

theorem inCStar_base {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a CStar) :
    In a C := ((inCStar_iff a).mp ha).1

theorem inCStar_nonzero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a CStar) :
    ¬ Same a (number 0) := ((inCStar_iff a).mp ha).2

theorem inCStar_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a C) (h : ¬ Same a (number 0)) : In a CStar :=
  (inCStar_iff a).mpr ⟨ha, h⟩

theorem cStarNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (CStar (M := M)) :=
  ⟨M.number (1), inCStar_intro (number (1)) (numberInC (M := M) (1)) (NativeBridge.numberNonzero (M := M) (1) (by norm_num))⟩

theorem sameBaseZeroOfPositivePowerZero {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (ha : In p.val.base C) (he : In p.val.exponent NPos)
    (hz : Same p (number 0)) : Same p.val.base (number 0) := by
  obtain ⟨a, ha⟩ := (M.complex_members _).mp ha
  obtain ⟨n, hn⟩ := (M.natural_members _).mp (inNPos_natural _ he)
  change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 0 at hz
  rw [ha, hn, M.pow_numbers_nat] at hz
  have ha0 : a = 0 := eq_zero_of_pow_eq_zero (M.number_injective hz)
  exact ha.trans (congrArg M.number ha0)

theorem positiveReal_members {M : Semantics.{u}} [S : SetSemantics M] (x : M.Value) :
    M.mem x positiveReal ↔ M.mem x (M.standard .real) ∧ positiveRealPredicate x :=
  S.sep_members _ _ _

theorem inRPos_iff {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    In a RPos ↔ In a R ∧ Lt (number 0) a := by
  rw [show In a RPos = M.mem (denote a) positiveReal from rfl, positiveReal_members]
  constructor
  · rintro ⟨ha, r, hr, hpos⟩
    exact ⟨ha, NativeBridge.ltOfDenoteReal (number 0) a 0 r rfl hr hpos⟩
  · rintro ⟨ha, hpos⟩
    obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp ha
    exact ⟨ha, r, hr,
      (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp hpos⟩

theorem inRPos_real {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    In a R := ((inRPos_iff a).mp ha).1

theorem positiveRealToComplex {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    In a C := realToComplex a (inRPos_real a ha)

theorem inRPos_positive {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a RPos) :
    Lt (number 0) a := ((inRPos_iff a).mp ha).2

theorem inRPos_intro {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a R) (hpos : Lt (number 0) a) : In a RPos :=
  (inRPos_iff a).mpr ⟨ha, hpos⟩

/-- Replay the recorded operand memberships on the original mul constructor. -/
theorem mulInRPos {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (ha : In p.val.left RPos) (hb : In p.val.right RPos) : In p RPos := by
  apply inRPos_intro p
  · exact mulInR p.val.left p.val.right
      (inRPos_real _ ha) (inRPos_real _ hb)
  · exact mulPositive p.val.left p.val.right p.wd.1 p.wd.2
      (inRPos_positive _ ha) (inRPos_positive _ hb)

/-- Replay the recorded operand memberships on the original div constructor. -/
theorem divInRPos {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DivObj (M := M) α β))
    (ha : In p.val.left RPos) (hb : In p.val.right RPos) : In p RPos := by
  apply inRPos_intro p
  · exact divInR p.val.left p.val.right
      (inRPos_real _ ha) (inRPos_real _ hb) p.wd.2.2
  · exact divPositive p.val.left p.val.right p.wd.1 p.wd.2.1 p.wd.2.2
      (inRPos_positive _ ha) (inRPos_positive _ hb)

/-- Replay the recorded operand memberships on the original mul constructor. -/
theorem mulInQStar {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (ha : In p.val.left QStar) (hb : In p.val.right QStar) : In p QStar := by
  apply inQStar_intro p
  · exact mulInQ p.val.left p.val.right
      (inQStar_base _ ha) (inQStar_base _ hb)
  · exact mulNonzero p.val.left p.val.right p.wd.1 p.wd.2
      (inQStar_nonzero _ ha) (inQStar_nonzero _ hb)

/-- Replay the recorded operand memberships on the original div constructor. -/
theorem divInQStar {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (DivObj (M := M) α β))
    (ha : In p.val.left QStar) (hb : In p.val.right QStar) : In p QStar := by
  apply inQStar_intro p
  · exact divInQ p.val.left p.val.right
      (inQStar_base _ ha) (inQStar_base _ hb) p.wd.2.2
  · exact divNonzero p.val.left p.val.right p.wd.1 p.wd.2.1
      (inQStar_nonzero _ ha) (inQStar_nonzero _ hb)

theorem numberNotInROfImaginary {M : Semantics.{u}} (z : ℂ) (hz : z.im ≠ 0) :
    ¬ In (number (M := M) z) R := by
  intro h
  obtain ⟨r, hr⟩ := (M.real_members _).mp h
  have heq : z = (r : ℂ) := M.number_injective hr
  exact hz (heq ▸ Complex.ofReal_im r)

theorem numberNotInZOfDenominator {M : Semantics.{u}} (q : ℚ) (hq : q.den ≠ 1) :
    ¬ In (number (M := M) (q : ℂ)) Z := by
  intro h
  obtain ⟨z, hz⟩ := (M.integer_members _).mp h
  have hc : (q : ℂ) = (z : ℂ) := M.number_injective hz
  have heq : q = (z : ℚ) := by exact_mod_cast hc
  apply hq
  rw [heq, Rat.den_intCast]

theorem numberNotInNOfNegative {M : Semantics.{u}} (q : ℚ) (hq : q < 0) :
    ¬ In (number (M := M) (q : ℂ)) N := by
  intro h
  have hnonneg := (NativeBridge.le_iff_ofDenoteReal (number 0)
    (number (q : ℂ)) 0 (q : ℝ) rfl rfl).mp (naturalNonnegative _ h)
  have hneg : (q : ℝ) < 0 := by exact_mod_cast hq
  exact (not_lt_of_ge hnonneg) hneg

theorem numberNotPositive {M : Semantics.{u}} (q : ℚ) (hq : q ≤ 0) :
    ¬ Lt (number (M := M) 0) (number (q : ℂ)) := by
  intro h
  have hpos := (NativeBridge.lt_iff_ofDenoteReal (number 0)
    (number (q : ℂ)) 0 (q : ℝ) rfl rfl).mp h
  have hnonpos : (q : ℝ) ≤ 0 := by exact_mod_cast hq
  exact (not_lt_of_ge hnonpos) hpos

theorem numberNotNegative {M : Semantics.{u}} (q : ℚ) (hq : 0 ≤ q) :
    ¬ Lt (number (M := M) (q : ℂ)) (number 0) := by
  intro h
  have hneg := (NativeBridge.lt_iff_ofDenoteReal (number (q : ℂ))
    (number 0) (q : ℝ) 0 rfl rfl).mp h
  have hnonneg : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  exact (not_lt_of_ge hnonneg) hneg

theorem numberInRPos_iff {M : Semantics.{u}} [SetSemantics M] (r : ℝ) :
    In (number (r : ℂ)) (RPos (M := M)) ↔ 0 < r := by
  rw [inRPos_iff]
  have hr : In (number (r : ℂ)) (R (M := M)) :=
    (M.real_members _).mpr ⟨r, rfl⟩
  exact ⟨fun h => (NativeBridge.lt_iff_ofDenoteReal (number 0)
    (number (r : ℂ)) 0 r rfl rfl).mp h.2,
    fun h => ⟨hr, NativeBridge.ltOfDenoteReal (number 0) (number (r : ℂ))
      0 r rfl rfl h⟩⟩

theorem numberInRPos {M : Semantics.{u}} [SetSemantics M] (r : ℝ) (hr : 0 < r) :
    In (number (r : ℂ)) (RPos (M := M)) :=
  (numberInRPos_iff r).mpr hr

namespace NativeBridge

/-- A numeric observer may use a complex expression rather than the real
embedding itself. The explicit equality preserves the original endpoint. -/
theorem numberInRPosOfEq {M : Semantics.{u}} [SetSemantics M]
    (z : ℂ) (r : ℝ) (hz : z = (r : ℂ)) (hr : 0 < r) :
    In (number (M := M) z) RPos :=
  inOfDenoteNumber (number z) (r : ℂ) RPos (congrArg M.number hz) (numberInRPos r hr)

end NativeBridge

theorem rPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (RPos (M := M)) := by
  refine ⟨M.number (1 : ℂ), ?_⟩
  have h := numberInRPos (M := M) (1 : ℝ) zero_lt_one
  change M.mem (M.number ((1 : ℝ) : ℂ)) (denote (RPos (M := M))) at h
  simpa only [Complex.ofReal_one] using h

theorem nPosNonempty {M : Semantics.{u}} [SetSemantics M] :
    IsNonempty (NPos (M := M)) := by
  exact ⟨M.number 1, numberInNPosOfEq 1 1 (by norm_num) (by decide)⟩

theorem inNPos_positive {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (ha : In a NPos) :
    Lt (number 0) a := by
  obtain ⟨r, hr, hpos⟩ := ((S.sep_members _ _ _).mp ha).2
  refine ⟨0, r, ?_, hr, hpos⟩
  change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
  rw [Complex.ofReal_zero]

inductive EmptySetObj where
  | empty

instance emptySetRepresentation {M : Semantics.{u}} [S : SetSemantics M] :
    Representation M EmptySetObj where
  wd _ := True
  denote _ := S.emptyValue
  wd_isSet _ := S.empty_isSet

def emptySet {M : Semantics.{u}} [SetSemantics M] : Obj (M := M) EmptySetObj :=
  ⟨.empty, True.intro⟩

/-- Heterogeneous certified children retain enumeration construction shape.
The stricter source WD requires a fresh element, even though set insertion
itself is defined for duplicates. -/
structure InsertObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  element : Obj (M := M) α
  tail : Obj (M := M) β

instance insertRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (InsertObj (M := M) α β) where
  wd s := ¬ In s.element s.tail
  denote s := S.insertValue (denote s.element) (denote s.tail)
  wd_isSet {s} _ := S.insert_isSet _ _ (isSet s.element) (isSet s.tail)

def insert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (h : ¬ In a A) :
    Obj (M := M) (InsertObj (M := M) α β) := ⟨⟨a, A⟩, h⟩

theorem insertNonempty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (InsertObj (M := M) α β)) : IsNonempty s :=
  ⟨denote s.val.element, (S.insert_members _ _ _).mpr (Or.inl rfl)⟩

theorem notInEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) :
    ¬ In a (emptySet (M := M)) := S.empty_members (denote a)

theorem inInsert_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (x : Obj (M := M) α) (a : Obj (M := M) β) (A : Obj (M := M) γ)
    (h : ¬ In a A) : In x (insert a A h) ↔ Same x a ∨ In x A :=
  S.insert_members _ _ _

theorem notInInsert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (x : Obj (M := M) α) (a : Obj (M := M) β) (A : Obj (M := M) γ)
    (h : ¬ In a A) (hxa : ¬ Same x a) (hxA : ¬ In x A) :
    ¬ In x (insert a A h) :=
  fun hx => ((inInsert_iff x a A h).mp hx).elim hxa hxA

def Subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop :=
  ∀ x, M.mem x (denote A) → M.mem x (denote B)

theorem subsetRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Subset A A := fun _ hx => hx

theorem subsetOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (C : Obj (M := M) γ) (D : Obj (M := M) δ)
    (hAC : Same A C) (hBD : Same B D) (hAB : Subset A B) : Subset C D := by
  intro z hz
  rw [← hBD]
  apply hAB z
  rw [hAC]
  exact hz

/-- Replay the source subset definition at the semantic-value representation.
The forall proof comes from the recorded definition child, not target search. -/
theorem subsetOfForall {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (h : ∀ {γ : Type u} [Representation M γ], (a : Obj (M := M) γ) → In a A → In a B) :
    Subset A B := fun z hz => h (semanticObject z (M.member_isSet hz)) hz

theorem emptySubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Subset (emptySet (M := M)) A := fun x hx => (S.empty_members x hx).elim

theorem insertSubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ)
    (h : ¬ In a A) (ha : In a B) (hA : Subset A B) : Subset (insert a A h) B := by
  intro x hx
  rcases (S.insert_members _ _ _).mp hx with hxa | hxA
  · exact hxa ▸ ha
  · exact hA x hxA

theorem setExt {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (hAB : Subset A B) (hBA : Subset B A) :
    Same A B := S.ext _ _ (isSet A) (isSet B) (fun x => ⟨hAB x, hBA x⟩)

/-- Predicate callbacks are well-typed only on certified members of the bound.
A membership proof certifies formation; it is not a mathematical argument. -/
structure SetBuilderObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  bound : Obj (M := M) α
  predicate : (x : Obj (M := M) M.Value) → In x bound → Prop

namespace SetBuilderObj

def condition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (s : SetBuilderObj (M := M) α) (x : M.Value) : Prop :=
  ∃ hx : M.mem x (denote s.bound), s.predicate (semanticObject x (M.member_isSet hx)) hx

end SetBuilderObj

instance setBuilderRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (SetBuilderObj (M := M) α) where
  wd _ := True
  denote s := S.sepValue (denote s.bound) s.condition
  wd_isSet {s} _ := S.sep_isSet _ _ (isSet s.bound)

def setBuilder {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) :
    Obj (M := M) (SetBuilderObj (M := M) α) := ⟨⟨D, p⟩, True.intro⟩

theorem inSetBuilder_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (D : Obj (M := M) β)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) :
    In a (setBuilder D p) ↔
      ∃ ha : In a D, p (semanticObject (denote a) (M.member_isSet ha)) ha := by
  rw [In, show denote (setBuilder D p) = S.sepValue (denote D)
    (SetBuilderObj.condition ⟨D, p⟩) from rfl, S.sep_members]
  exact ⟨fun h => h.2, fun h => ⟨h.choose, h⟩⟩

theorem setBuilderSubset {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (D : Obj (M := M) α)
    (p : (x : Obj (M := M) M.Value) → In x D → Prop) : Subset (setBuilder D p) D :=
  fun _ hx => ((S.sep_members _ _ _).mp hx).1

namespace NativeSetBridge

/-- A numeric pullback observes only the numeric slice. A full numeric-set view
also needs the corresponding source subset witness, as in the completeness
lemmas below. Arbitrary objects keep their registered host representation. -/
def complexView {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Set ℂ := {z | In (number z) A}

def realView {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Set ℝ := {r | In (number (r : ℂ)) A}

theorem complexView_ofSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Same A B) :
    complexView A = complexView B :=
  Set.ext fun z => ⟨fun hz => Eq.mp (congrArg (M.mem (M.number z)) h) hz,
    fun hz => Eq.mpr (congrArg (M.mem (M.number z)) h) hz⟩

theorem complexView_subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) :
    complexView A ⊆ complexView B := fun z hz => h (M.number z) hz

theorem realView_subset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) :
    realView A ⊆ realView B := fun r hr => h (M.number (r : ℂ)) hr

theorem complexView_complete {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : Subset A C) (x : M.Value) (hx : M.mem x (denote A)) :
    ∃ z : ℂ, x = M.number z ∧ z ∈ complexView A := by
  obtain ⟨z, hz⟩ := (M.complex_members x).mp (h x hx)
  exact ⟨z, hz, Eq.mp (congrArg (fun y => M.mem y (denote A)) hz) hx⟩

theorem realView_complete {M : Semantics.{u}} {α : Type v} [Representation M α]
    (A : Obj (M := M) α) (h : Subset A R) (x : M.Value) (hx : M.mem x (denote A)) :
    ∃ r : ℝ, x = M.number (r : ℂ) ∧ r ∈ realView A := by
  obtain ⟨r, hr⟩ := (M.real_members x).mp (h x hx)
  exact ⟨r, hr, Eq.mp (congrArg (fun y => M.mem y (denote A)) hr) hx⟩

theorem complexView_empty {M : Semantics.{u}} [SetSemantics M] :
    complexView (emptySet (M := M)) = ∅ :=
  Set.ext fun z => ⟨fun hz => (notInEmpty (number z) hz).elim, fun h => h.elim⟩

theorem complexView_insert {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (z : ℂ) (A : Obj (M := M) α)
    (h : ¬ In (number z) A) : complexView (insert (number z) A h) =
      Insert.insert z (complexView A) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases (inInsert_iff (number x) (number z) A h).mp hx with eq | mem
    · exact Or.inl (M.number_injective eq)
    · exact Or.inr mem
  · intro hx
    rcases hx with eq | mem
    · exact (inInsert_iff (number x) (number z) A h).mpr (Or.inl (congrArg M.number eq))
    · exact (inInsert_iff (number x) (number z) A h).mpr (Or.inr mem)

end NativeSetBridge

/-- A graph has exactly its declared domain and one codomain value per input. -/
def IsFunctionGraph {M : Semantics.{u}} (pair : M.Value → M.Value → M.Value)
    (D B f : M.Value) : Prop :=
  (∀ p, M.mem p f → ∃ x, M.mem x D ∧ ∃ y, M.mem y B ∧ p = pair x y) ∧
    ∀ x, M.mem x D → ∃! y, M.mem (pair x y) f

/-- Additional set/function structure; the existing numeric model is not copied. -/
class FunctionSemantics (M : Semantics.{u}) extends SetSemantics M where
  pairValue : M.Value → M.Value → M.Value
  pair_injective : Function.Injective2 pairValue
  productValue : M.Value → M.Value → M.Value
  product_members : ∀ D E p,
    M.mem p (productValue D E) ↔ ∃ x, M.mem x D ∧ ∃ y, M.mem y E ∧ p = pairValue x y
  product_isSet : ∀ D E, M.isSet D → M.isSet E → M.isSet (productValue D E)
  fnSetValue : M.Value → M.Value → M.Value
  fnSet_members : ∀ D B f, M.mem f (fnSetValue D B) ↔ IsFunctionGraph pairValue D B f
  fnSet_isSet : ∀ D B, M.isSet D → M.isSet B → M.isSet (fnSetValue D B)
  graphValue : M.Value → M.Value → (M.Value → M.Value) → M.Value
  graph_members : ∀ D B body p,
    M.mem p (graphValue D B body) ↔
      ∃ x, M.mem x D ∧ ∃ y, M.mem y B ∧ p = pairValue x y ∧ y = body x
  callValue : M.Value → M.Value → M.Value
  call_graph : ∀ D B f x, IsFunctionGraph pairValue D B f → M.mem x D →
    M.mem (pairValue x (callValue f x)) f
  graph_ext : ∀ D B f g, IsFunctionGraph pairValue D B f →
    IsFunctionGraph pairValue D B g →
    (∀ x y, M.mem (pairValue x y) f ↔ M.mem (pairValue x y) g) → f = g

namespace FunctionSemantics

variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem pair_mem_graph (D B : M.Value) (body : M.Value → M.Value) (x y : M.Value) :
    M.mem (F.pairValue x y) (F.graphValue D B body) ↔
      M.mem x D ∧ M.mem y B ∧ y = body x := by
  rw [F.graph_members]
  constructor
  · rintro ⟨a, ha, b, hb, hp, hbody⟩
    obtain ⟨rfl, rfl⟩ := F.pair_injective hp
    exact ⟨ha, hb, hbody⟩
  · rintro ⟨hx, hy, hbody⟩
    exact ⟨x, hx, y, hy, rfl, hbody⟩

theorem graph_isFunction (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) :
    IsFunctionGraph F.pairValue D B (F.graphValue D B body) := by
  constructor
  · intro p hp
    obtain ⟨x, hx, y, hy, hpair, _⟩ := (F.graph_members D B body p).mp hp
    exact ⟨x, hx, y, hy, hpair⟩
  · intro x hx
    refine ⟨body x, (pair_mem_graph D B body x (body x)).mpr ⟨hx, hbody x hx, rfl⟩, ?_⟩
    intro y hy
    exact ((pair_mem_graph D B body x y).mp hy).2.2

theorem graph_inFnSet (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) :
    M.mem (F.graphValue D B body) (F.fnSetValue D B) :=
  (F.fnSet_members D B _).mpr (graph_isFunction D B body hbody)

theorem call_mem (D B f x : M.Value) (hf : M.mem f (F.fnSetValue D B))
    (hx : M.mem x D) : M.mem (F.callValue f x) B := by
  have hgraph := (F.fnSet_members D B f).mp hf
  obtain ⟨a, _, b, hb, hp⟩ := hgraph.1 _ (F.call_graph D B f x hgraph hx)
  obtain ⟨_, hresult⟩ := F.pair_injective hp
  exact hresult ▸ hb

theorem call_graphValue (D B : M.Value) (body : M.Value → M.Value)
    (hbody : ∀ x, M.mem x D → M.mem (body x) B) (x : M.Value) (hx : M.mem x D) :
    F.callValue (F.graphValue D B body) x = body x := by
  have hpoint := F.call_graph D B _ x (graph_isFunction D B body hbody) hx
  exact ((pair_mem_graph D B body x _).mp hpoint).2.2

end FunctionSemantics

namespace NumericFunctionModel

noncomputable def graph (D B : ZFSet.{0}) (body : ZFSet.{0} → ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pairSep (fun x y => y = body x) D B

noncomputable def call (f x : ZFSet.{0}) : ZFSet.{0} := by
  classical
  exact if h : ∃! y, ZFSet.pair x y ∈ f then Classical.choose h.exists
    else NumericModel.codeComplex 0

theorem call_graph (D B f x : ZFSet.{0}) (hf : ZFSet.IsFunc D B f) (hx : x ∈ D) :
    ZFSet.pair x (call f x) ∈ f := by
  classical
  have h := hf.2 x hx
  unfold call
  rw [dif_pos h]
  exact Classical.choose_spec h.exists

theorem function_iff (D B f : ZFSet.{0}) :
    IsFunctionGraph ZFSet.pair (M := NumericModel.model) D B f ↔ ZFSet.IsFunc D B f := by
  constructor
  · intro h
    exact ⟨fun p hp => (ZFSet.mem_prod).mpr (h.1 p hp), h.2⟩
  · intro h
    exact ⟨fun p hp => (ZFSet.mem_prod).mp (h.1 hp), h.2⟩

theorem function_ext (D B f g : ZFSet.{0}) (hf : ZFSet.IsFunc D B f)
    (hg : ZFSet.IsFunc D B g)
    (h : ∀ x y, ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ g) : f = g := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    exact (h x y).mp hp
  · intro hp
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.mp (hg.1 hp)
    exact (h x y).mpr hp

noncomputable instance numericFunctionSemantics : FunctionSemantics NumericModel.model where
  toSetSemantics := numericSetSemantics
  pairValue := ZFSet.pair
  pair_injective := ZFSet.pair_injective
  productValue := ZFSet.prod
  product_members _ _ _ := ZFSet.mem_prod
  product_isSet _ _ _ _ := True.intro
  fnSetValue := ZFSet.funs
  fnSet_members D B f := ZFSet.mem_funs.trans (function_iff D B f).symm
  fnSet_isSet _ _ _ _ := True.intro
  graphValue := graph
  graph_members _ _ _ _ := ZFSet.mem_pairSep
  callValue := call
  call_graph D B f x hf hx := call_graph D B f x ((function_iff D B f).mp hf) hx
  graph_ext D B f g hf hg h := function_ext D B f g
    ((function_iff D B f).mp hf) ((function_iff D B g).mp hg) h

end NumericFunctionModel


namespace FunctionSemantics

variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- Decode the raw ordered-pair encoding used by graph edges. Source tuples
are finite indexed graphs and use `FiniteFunction.unpack2` below. -/
noncomputable def unpairValue (p : M.Value) : M.Value × M.Value := by
  classical
  exact if h : ∃ v : M.Value × M.Value, p = F.pairValue v.1 v.2 then
    Classical.choose h else (M.number 0, M.number 0)

theorem unpair_pair (a b : M.Value) :
    unpairValue (F.pairValue a b) = (a, b) := by
  classical
  have h : ∃ v : M.Value × M.Value, F.pairValue a b = F.pairValue v.1 v.2 :=
    ⟨(a, b), rfl⟩
  unfold unpairValue
  rw [dif_pos h]
  obtain ⟨ha, hb⟩ := F.pair_injective (Classical.choose_spec h)
  exact Prod.ext ha.symm hb.symm

end FunctionSemantics

namespace FiniteFunction

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def finiteSetValue : List M.Value → M.Value
  | [] => F.emptyValue
  | a :: xs => F.insertValue a (finiteSetValue xs)

theorem finiteSet_members (xs : List M.Value) (x : M.Value) :
    M.mem x (finiteSetValue xs) ↔ x ∈ xs := by
  induction xs with
  | nil => exact ⟨fun h => (F.empty_members x h).elim, fun h => nomatch h⟩
  | cons a xs ih =>
    rw [finiteSetValue, F.insert_members, List.mem_cons, ih]

theorem finiteSet_isSet (xs : List M.Value) (h : ∀ x ∈ xs, M.isSet x) :
    M.isSet (finiteSetValue xs) := by
  induction xs with
  | nil => exact F.empty_isSet
  | cons a xs ih =>
    exact F.insert_isSet _ _ (h a (List.mem_cons_self))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

def index {n : ℕ} (i : Fin n) : M.Value := M.number ((i.val + 1 : ℕ) : ℂ)

omit F in
theorem index_injective {n : ℕ} : Function.Injective (index (M := M) (n := n)) := by
  intro i j h
  have hcast := M.number_injective h
  have hnat : i.val + 1 = j.val + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

def indexSet (n : ℕ) : M.Value := finiteSetValue (List.ofFn (index (M := M) (n := n)))

theorem indexSet_members {n : ℕ} (x : M.Value) :
    M.mem x (indexSet n) ↔ ∃ i : Fin n, x = index i := by
  simp only [indexSet, finiteSet_members, List.mem_ofFn]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

theorem index_mem {n : ℕ} (i : Fin n) : M.mem (index (M := M) i) (indexSet n) :=
  (indexSet_members _).mpr ⟨i, rfl⟩

theorem indexSet_isSet (n : ℕ) : M.isSet (indexSet (M := M) n) := by
  apply finiteSet_isSet
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact isSet (number ((i.val + 1 : ℕ) : ℂ))

def tupleValue {n : ℕ} (a : Fin n → M.Value) : M.Value :=
  finiteSetValue (List.ofFn (fun i => F.pairValue (index i) (a i)))

theorem tuple_members {n : ℕ} (a : Fin n → M.Value) (p : M.Value) :
    M.mem p (tupleValue a) ↔ ∃ i : Fin n, p = F.pairValue (index i) (a i) := by
  simp only [tupleValue, finiteSet_members, List.mem_ofFn]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

theorem tuple_pair_mem {n : ℕ} (a : Fin n → M.Value) (x y : M.Value) :
    M.mem (F.pairValue x y) (tupleValue a) ↔
      ∃ i : Fin n, x = index i ∧ y = a i := by
  rw [tuple_members]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, F.pair_injective h⟩
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i, rfl⟩

theorem tuple_isFunction {n : ℕ} (a : Fin n → M.Value) :
    IsFunctionGraph F.pairValue (indexSet n) (finiteSetValue (List.ofFn a))
      (tupleValue a) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := (tuple_members a p).mp hp
    exact ⟨index i, index_mem i, a i,
      (finiteSet_members _ _).mpr (List.mem_ofFn.mpr ⟨i, rfl⟩), rfl⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    refine ⟨a i, (tuple_pair_mem a _ _).mpr ⟨i, rfl, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨j, hij, hy⟩ := (tuple_pair_mem a _ _).mp hy
    have hji : i = j := index_injective hij
    exact hy.trans (congrArg a hji.symm)

theorem tuple_isSet {n : ℕ} (a : Fin n → M.Value) : M.isSet (tupleValue a) :=
  M.member_isSet ((F.fnSet_members _ _ _).mpr (tuple_isFunction a))

theorem call_tuple {n : ℕ} (a : Fin n → M.Value) (i : Fin n) :
    F.callValue (tupleValue a) (index i) = a i := by
  have h := F.call_graph _ _ _ _ (tuple_isFunction a) (index_mem i)
  obtain ⟨j, hij, hy⟩ := (tuple_pair_mem a _ _).mp h
  exact hy.trans (congrArg a (index_injective hij).symm)

def finiteUnionValue : List M.Value → M.Value
  | [] => F.emptyValue
  | A :: As => F.unionValue A (finiteUnionValue As)

theorem finiteUnion_members (As : List M.Value) (x : M.Value) :
    M.mem x (finiteUnionValue As) ↔ ∃ A ∈ As, M.mem x A := by
  induction As with
  | nil =>
    exact ⟨fun h => (F.empty_members x h).elim, fun ⟨A, hA, _⟩ => nomatch hA⟩
  | cons A As ih =>
    rw [finiteUnionValue, F.union_members, ih]
    constructor
    · rintro (hx | ⟨B, hB, hx⟩)
      · exact ⟨A, List.mem_cons_self, hx⟩
      · exact ⟨B, List.mem_cons_of_mem A hB, hx⟩
    · rintro ⟨B, hB, hx⟩
      rcases List.mem_cons.mp hB with rfl | hB
      · exact Or.inl hx
      · exact Or.inr ⟨B, hB, hx⟩

theorem finiteUnion_isSet (As : List M.Value) (h : ∀ A ∈ As, M.isSet A) :
    M.isSet (finiteUnionValue As) := by
  induction As with
  | nil => exact F.empty_isSet
  | cons A As ih =>
    exact F.union_isSet _ _ (h A List.mem_cons_self)
      (ih (fun B hB => h B (List.mem_cons_of_mem A hB)))

def cartValue {n : ℕ} (A : Fin n → M.Value) : M.Value :=
  F.sepValue (F.fnSetValue (indexSet n) (finiteUnionValue (List.ofFn A)))
    (fun p => ∀ i, M.mem (F.callValue p (index i)) (A i))

theorem cart_members {n : ℕ} (A : Fin n → M.Value) (p : M.Value) :
    M.mem p (cartValue A) ↔
      IsFunctionGraph F.pairValue (indexSet n) (finiteUnionValue (List.ofFn A)) p ∧
      ∀ i, M.mem (F.callValue p (index i)) (A i) := by
  rw [cartValue, F.sep_members, F.fnSet_members]

theorem cart_isSet {n : ℕ} (A : Fin n → M.Value) (hA : ∀ i, M.isSet (A i)) :
    M.isSet (cartValue A) := by
  apply F.sep_isSet
  apply F.fnSet_isSet _ _ (indexSet_isSet n)
  apply finiteUnion_isSet
  intro B hB
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
  exact hA i

theorem tuple_inCart {n : ℕ} (a A : Fin n → M.Value) (h : ∀ i, M.mem (a i) (A i)) :
    M.mem (tupleValue a) (cartValue A) := by
  apply (cart_members A _).mpr
  constructor
  · constructor
    · intro p hp
      obtain ⟨i, rfl⟩ := (tuple_members a p).mp hp
      refine ⟨index i, index_mem i, a i, ?_, rfl⟩
      exact (finiteUnion_members _ _).mpr ⟨A i, List.mem_ofFn.mpr ⟨i, rfl⟩, h i⟩
    · exact (tuple_isFunction a).2
  · intro i
    rw [call_tuple]
    exact h i

theorem coordinate_mem {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) (i : Fin n) : M.mem (F.callValue p (index i)) (A i) :=
  ((cart_members A p).mp hp).2 i

theorem coordinate_mem_number {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) (i : Fin n) (z : ℂ)
    (hz : z = ((i.val + 1 : ℕ) : ℂ)) :
    M.mem (F.callValue p (M.number z)) (A i) := by
  rw [hz]
  exact coordinate_mem hp i

theorem graph_pair_value {D B f x y : M.Value}
    (hf : IsFunctionGraph F.pairValue D B f) (hxy : M.mem (F.pairValue x y) f) :
    M.mem x D ∧ y = F.callValue f x := by
  obtain ⟨a, ha, b, _, hab⟩ := hf.1 _ hxy
  obtain ⟨rfl, rfl⟩ := F.pair_injective hab
  have hcall := F.call_graph D B f x hf ha
  obtain ⟨z, _, hz⟩ := hf.2 x ha
  exact ⟨ha, (hz y hxy).trans (hz _ hcall).symm⟩

/-- A complete finite function belongs to new factors when each coordinate does. -/
theorem cart_of_coordinates {n : ℕ} {A B : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A))
    (h : ∀ i : Fin n, M.mem (F.callValue p (index i)) (B i)) :
    M.mem p (cartValue B) := by
  have hf := ((cart_members A p).mp hp).1
  apply (cart_members B p).mpr
  refine ⟨⟨?_, hf.2⟩, h⟩
  intro edge he
  obtain ⟨x, hx, y, _, rfl⟩ := hf.1 edge he
  obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
  refine ⟨index i, index_mem i, y, ?_, rfl⟩
  rw [(graph_pair_value hf he).2]
  exact (finiteUnion_members _ _).mpr ⟨B i, List.mem_ofFn.mpr ⟨i, rfl⟩, h i⟩

theorem cart_ext {n : ℕ} {A B : Fin n → M.Value} {p q : M.Value}
    (hp : M.mem p (cartValue A)) (hq : M.mem q (cartValue B))
    (h : ∀ i : Fin n, F.callValue p (index i) = F.callValue q (index i)) : p = q := by
  apply F.ext p q (M.member_isSet hp) (M.member_isSet hq)
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := ((cart_members A p).mp hp).1.1 edge he
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    have hy := (graph_pair_value ((cart_members A p).mp hp).1 he).2
    rw [hy, h i]
    exact F.call_graph _ _ _ _ ((cart_members B q).mp hq).1 (index_mem i)
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := ((cart_members B q).mp hq).1.1 edge he
    obtain ⟨i, rfl⟩ := (indexSet_members x).mp hx
    have hy := (graph_pair_value ((cart_members B q).mp hq).1 he).2
    rw [hy, ← h i]
    exact F.call_graph _ _ _ _ ((cart_members A p).mp hp).1 (index_mem i)

theorem reconstruct {n : ℕ} {A : Fin n → M.Value} {p : M.Value}
    (hp : M.mem p (cartValue A)) :
    p = tupleValue (fun i : Fin n => F.callValue p (index i)) := by
  apply cart_ext hp (tuple_inCart _ A (coordinate_mem hp))
  intro i
  rw [call_tuple]

def pack2 (a b : M.Value) : M.Value := tupleValue ![a, b]

def unpack2 (p : M.Value) : M.Value × M.Value :=
  (F.callValue p (M.number 1), F.callValue p (M.number 2))

theorem unpack_pack2 (a b : M.Value) : unpack2 (pack2 a b) = (a, b) := by
  apply Prod.ext
  · simpa [unpack2, pack2, index] using call_tuple ![a, b] (0 : Fin 2)
  · simpa [unpack2, pack2, index] using call_tuple ![a, b] (1 : Fin 2)

theorem pack2_injective : Function.Injective2 (pack2 (M := M)) := by
  intro a b c d h
  have hp := congrArg (unpack2 (M := M)) h
  rw [unpack_pack2, unpack_pack2] at hp
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

theorem cart2_members (A B p : M.Value) :
    M.mem p (cartValue ![A, B]) ↔
      ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧ p = pack2 a b := by
  constructor
  · intro hp
    refine ⟨F.callValue p (M.number 1), by simpa [index] using coordinate_mem hp (0 : Fin 2),
      F.callValue p (M.number 2), by simpa [index] using coordinate_mem hp (1 : Fin 2), ?_⟩
    refine (reconstruct hp).trans (congrArg tupleValue ?_)
    funext i
    fin_cases i <;> simp [index]
  · rintro ⟨a, ha, b, hb, rfl⟩
    apply tuple_inCart
    intro i
    fin_cases i
    · exact ha
    · exact hb

end FiniteFunction

namespace FunctionSemantics

/-- Change a function's return bound while retaining its complete input domain. -/
theorem fnSet_of_returns {M : Semantics.{u}} [F : FunctionSemantics M]
    {D B E f : M.Value} (hf : M.mem f (F.fnSetValue D B))
    (h : ∀ x, M.mem x D → M.mem (F.callValue f x) E) :
    M.mem f (F.fnSetValue D E) := by
  have hg := (F.fnSet_members D B f).mp hf
  apply (F.fnSet_members D E f).mpr
  refine ⟨?_, hg.2⟩
  intro edge he
  obtain ⟨x, hx, y, _, rfl⟩ := hg.1 edge he
  refine ⟨x, hx, y, ?_, rfl⟩
  rw [(FiniteFunction.graph_pair_value hg he).2]
  exact h x hx

end FunctionSemantics

structure TupleObj (M : Semantics.{u}) (n : ℕ) where
  values : Fin n → M.Value

instance tupleRepresentation {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ} :
    Representation M (TupleObj M n) where
  wd t := ∀ i, M.isSet (t.values i)
  denote t := FiniteFunction.tupleValue t.values
  wd_isSet {t} _ := FiniteFunction.tuple_isSet t.values

def tuple {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (values : Fin n → M.Value) (hSets : ∀ i, M.isSet (values i)) :
    Obj (M := M) (TupleObj M n) := ⟨⟨values⟩, hSets⟩

/-- Internal call packing preserves both certified source argument objects. -/
structure CallArguments2 {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  first : Obj (M := M) α
  second : Obj (M := M) β

instance callArguments2Representation {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallArguments2 (M := M) α β) where
  wd _ := True
  denote args := FiniteFunction.tupleValue ![denote args.first, denote args.second]
  wd_isSet {args} _ := FiniteFunction.tuple_isSet ![denote args.first, denote args.second]

def callArguments2 {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    Obj (M := M) (CallArguments2 (M := M) α β) := ⟨⟨a, b⟩, True.intro⟩

theorem callArguments2_denote {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) :
    denote (callArguments2 a b) = FiniteFunction.tupleValue ![denote a, denote b] := rfl

theorem callArguments2_mem_cart {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) {A B : M.Value}
    (ha : M.mem (denote a) A) (hb : M.mem (denote b) B) :
    M.mem (denote (callArguments2 a b)) (FiniteFunction.cartValue ![A, B]) :=
  FiniteFunction.tuple_inCart ![denote a, denote b] ![A, B]
    (Fin.cases ha (Fin.cases hb (fun i => Fin.elim0 i)))

structure CartObj (M : Semantics.{u}) (n : ℕ) where
  factors : Fin n → M.Value

instance cartRepresentation {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ} :
    Representation M (CartObj M n) where
  wd c := ∀ i, M.isSet (c.factors i)
  denote c := FiniteFunction.cartValue c.factors
  wd_isSet {c} h := FiniteFunction.cart_isSet c.factors h

def cart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (factors : Fin n → M.Value) (hSets : ∀ i, M.isSet (factors i)) :
    Obj (M := M) (CartObj M n) := ⟨⟨factors⟩, hSets⟩

theorem cartNonemptyOfFactors {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (c : Obj (M := M) (CartObj M n))
    (h : ∀ i, ∃ x, M.mem x (c.val.factors i)) : IsNonempty c := by
  classical
  refine ⟨FiniteFunction.tupleValue (fun i => Classical.choose (h i)), ?_⟩
  exact FiniteFunction.tuple_inCart _ _ (fun i => Classical.choose_spec (h i))

/-- The return bound can contain the factors in any association/order of unions;
the complete domain and every coordinate condition remain explicit. -/
theorem cartMembersWithReturnBound {M : Semantics.{u}} [F : FunctionSemantics M]
    {n : ℕ} (A : Fin n → M.Value) (B : M.Value)
    (hB : ∀ i x, M.mem x (A i) → M.mem x B) (p : M.Value) :
    M.mem p (FiniteFunction.cartValue A) ↔
      M.mem p (F.fnSetValue (FiniteFunction.indexSet n) B) ∧
      ∀ i, M.mem (F.callValue p (FiniteFunction.index i)) (A i) := by
  constructor
  · intro hp
    obtain ⟨hg, hc⟩ := (F.sep_members _ _ _).mp hp
    refine ⟨F.fnSet_of_returns hg ?_, hc⟩
    intro x hx
    obtain ⟨i, rfl⟩ := (FiniteFunction.indexSet_members (M := M) x).mp hx
    exact hB i _ (hc i)
  · rintro ⟨hg, hc⟩
    apply (F.sep_members _ _ _).mpr
    refine ⟨F.fnSet_of_returns hg ?_, hc⟩
    intro x hx
    obtain ⟨i, rfl⟩ := (FiniteFunction.indexSet_members (M := M) x).mp hx
    exact (FiniteFunction.finiteUnion_members _ _).mpr
      ⟨A i, List.mem_ofFn.mpr ⟨i, rfl⟩, hc i⟩

theorem cartSameSetBuilder {M : Semantics.{u}} [F : FunctionSemantics M]
    {n : ℕ} {β : Type v} [Representation M β]
    (c : Obj (M := M) (CartObj M n)) (D : Obj (M := M) β)
    (P : (x : Obj (M := M) M.Value) → In x D → Prop) (B : M.Value)
    (hD : denote D = F.fnSetValue (FiniteFunction.indexSet n) B)
    (hB : ∀ i x, M.mem x (c.val.factors i) → M.mem x B)
    (hP : ∀ x hx, P x hx ↔
      ∀ i, M.mem (F.callValue (denote x) (FiniteFunction.index i)) (c.val.factors i)) :
    Same c (setBuilder D P) := by
  apply F.ext _ _ (isSet c) (isSet (setBuilder D P))
  intro raw
  change M.mem raw (FiniteFunction.cartValue c.val.factors) ↔
    M.mem raw (F.sepValue (denote D) (SetBuilderObj.condition ⟨D, P⟩))
  rw [F.sep_members]
  constructor
  · intro hc
    obtain ⟨hg, hp⟩ := (cartMembersWithReturnBound _ B hB raw).mp hc
    have hx : M.mem raw (denote D) := by rw [hD]; exact hg
    exact ⟨hx, hx, (hP (semanticObject raw (M.member_isSet hx)) hx).mpr hp⟩
  · rintro ⟨hx, hx', hp⟩
    apply (cartMembersWithReturnBound _ B hB raw).mpr
    exact ⟨by rw [← hD]; exact hx,
      (hP (semanticObject raw (M.member_isSet hx')) hx').mp hp⟩

theorem cartZeroSame {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type v} [Representation M β]
    (c : Obj (M := M) (CartObj M 0)) (D : Obj (M := M) β)
    (hD : denote D = F.fnSetValue (FiniteFunction.indexSet 0) F.emptyValue) :
    Same c D := by
  apply F.ext _ _ (isSet c) (isSet D)
  intro raw
  rw [hD]
  exact (cartMembersWithReturnBound c.val.factors F.emptyValue
    (fun i => Fin.elim0 i) raw).trans
      ⟨And.left, fun h => ⟨h, fun i => Fin.elim0 i⟩⟩

theorem tupleInCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (c : Obj (M := M) (CartObj M n))
    (h : ∀ i, M.mem (t.val.values i) (c.val.factors i)) : In t c :=
  FiniteFunction.tuple_inCart _ _ h


/-- An ordered finite family of field carriers. Each tail can depend only on
members selected for the preceding fields. -/
inductive DependentFields (M : Semantics.{u}) : ℕ → Type u where
  | nil : DependentFields M 0
  | cons {n : ℕ} (carrier : M.Value) (rest : M.Value → DependentFields M n) :
      DependentFields M (n + 1)

namespace DependentFields

variable {M : Semantics.{u}}

def WellFormed : {n : ℕ} → DependentFields M n → Prop
  | _, .nil => True
  | _, .cons A rest => M.isSet A ∧ ∀ x, M.mem x A → WellFormed (rest x)

def Accepts : {n : ℕ} → DependentFields M n → (Fin n → M.Value) → Prop
  | _, .nil, _ => True
  | _, .cons A rest, v => M.mem (v 0) A ∧ Accepts (rest (v 0)) (Fin.tail v)

def factors : {n : ℕ} → DependentFields M n → (Fin n → M.Value) → Fin n → M.Value
  | _, .nil, _ => fun i => Fin.elim0 i
  | _, .cons A rest, v => Fin.cons A (factors (rest (v 0)) (Fin.tail v))

theorem accepts_iff {n : ℕ} (t : DependentFields M n) (v : Fin n → M.Value) :
    t.Accepts v ↔ ∀ i, M.mem (v i) (t.factors v i) := by
  induction t with
  | nil => exact ⟨fun _ i => Fin.elim0 i, fun _ => True.intro⟩
  | cons A rest ih =>
    constructor
    · rintro ⟨h, hs⟩ i
      exact Fin.cases h (fun j => (ih (v 0) (Fin.tail v)).mp hs j) i
    · intro h
      exact ⟨h 0, (ih (v 0) (Fin.tail v)).mpr (fun j => h j.succ)⟩

theorem factors_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed)
    (v : Fin n → M.Value) (hv : t.Accepts v) : ∀ i, M.isSet (t.factors v i) := by
  induction t with
  | nil => exact fun i => Fin.elim0 i
  | cons A rest ih =>
    exact Fin.cases ht.1 (ih (v 0) (ht.2 _ hv.1) (Fin.tail v) hv.2)

variable [F : FunctionSemantics M] [I : IndexedUnionSemantics M]

/-- Enumerate a finite telescope using set-indexed unions. The callback keeps
the existing flat tuple graph representation, including for more than two fields. -/
noncomputable def collect : {n : ℕ} → DependentFields M n →
    ((Fin n → M.Value) → M.Value) → M.Value
  | _, .nil, emit => F.insertValue (emit (fun i => Fin.elim0 i)) F.emptyValue
  | _, .cons A rest, emit => I.indexedUnionValue A
      (fun x => collect (rest x) (fun v => emit (Fin.cons x v)))

theorem collect_members {n : ℕ} (t : DependentFields M n) :
    ∀ (emit : (Fin n → M.Value) → M.Value) (p : M.Value),
      M.mem p (t.collect emit) ↔ ∃ v, t.Accepts v ∧ p = emit v := by
  induction t with
  | nil =>
    intro emit p
    constructor
    · intro hp
      rcases (F.insert_members _ _ _).mp hp with hp | hp
      · exact ⟨fun i => Fin.elim0 i, True.intro, hp⟩
      · exact (F.empty_members p hp).elim
    · rintro ⟨v, _, hp⟩
      have hv : v = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
      subst v
      exact (F.insert_members _ _ _).mpr (Or.inl hp)
  | cons A rest ih =>
    intro emit p
    change M.mem p (I.indexedUnionValue A _) ↔ _
    rw [I.indexedUnion_members]
    constructor
    · rintro ⟨x, hx, hp⟩
      obtain ⟨v, hv, hp⟩ := (ih x _ p).mp hp
      refine ⟨Fin.cons x v, ?_, hp⟩
      simpa only [Accepts, Fin.cons_zero, Fin.tail_cons] using And.intro hx hv
    · rintro ⟨v, hv, hp⟩
      refine ⟨v 0, hv.1, (ih (v 0) _ p).mpr ⟨Fin.tail v, hv.2, ?_⟩⟩
      simpa only [Fin.cons_self_tail] using hp

theorem collect_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed)
    (emit : (Fin n → M.Value) → M.Value)
    (he : ∀ v, t.Accepts v → M.isSet (emit v)) : M.isSet (t.collect emit) := by
  induction t with
  | nil => exact F.insert_isSet _ _ (he _ True.intro) F.empty_isSet
  | cons A rest ih =>
    apply I.indexedUnion_isSet _ _ ht.1
    intro x hx
    apply ih x (ht.2 x hx)
    intro v hv
    apply he (Fin.cons x v)
    simpa only [Accepts, Fin.cons_zero, Fin.tail_cons] using And.intro hx hv

noncomputable def value {n : ℕ} (t : DependentFields M n) : M.Value :=
  t.collect FiniteFunction.tupleValue

theorem value_isSet {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed) :
    M.isSet t.value :=
  t.collect_isSet ht _ (fun v _ => FiniteFunction.tuple_isSet v)

def coordinates {n : ℕ} (p : M.Value) : Fin n → M.Value :=
  fun i => F.callValue p (FiniteFunction.index i)

/-- Source coordinate literals and canonical finite indices have the same values.
The compiler supplies this finite certificate once for each dependent structure. -/
def numberedCoordinates {n : ℕ} (p : M.Value) (indices : Fin n → ℂ) : Fin n → M.Value :=
  fun i => F.callValue p (M.number (indices i))

omit I in
theorem numberedCoordinates_eq {n : ℕ} (p : M.Value) (indices : Fin n → ℂ)
    (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) :
    numberedCoordinates p indices = coordinates p := by
  funext i
  change F.callValue p (M.number (indices i)) = _
  rw [hi i]
  rfl

omit I in
theorem coordinates_tuple {n : ℕ} (v : Fin n → M.Value) :
    coordinates (FiniteFunction.tupleValue v) = v := by
  funext i
  exact FiniteFunction.call_tuple v i

theorem members_iff_cart {n : ℕ} (t : DependentFields M n) (p : M.Value) :
    M.mem p t.value ↔
      M.mem p (FiniteFunction.cartValue (t.factors (coordinates p))) := by
  constructor
  · intro hp
    obtain ⟨v, hv, rfl⟩ := (t.collect_members _ _).mp hp
    rw [coordinates_tuple]
    exact FiniteFunction.tuple_inCart v _ ((t.accepts_iff v).mp hv)
  · intro hp
    exact (t.collect_members _ _).mpr ⟨coordinates p,
      (t.accepts_iff _).mpr (FiniteFunction.coordinate_mem hp),
      FiniteFunction.reconstruct hp⟩

end DependentFields

structure DependentCartObj (M : Semantics.{u}) (n : ℕ) where
  fields : DependentFields M n

noncomputable instance dependentCartRepresentation {M : Semantics.{u}}
    [FunctionSemantics M] [IndexedUnionSemantics M] {n : ℕ} :
    Representation M (DependentCartObj M n) where
  wd c := c.fields.WellFormed
  denote c := c.fields.value
  wd_isSet {c} h := c.fields.value_isSet h

def dependentCart {M : Semantics.{u}} [FunctionSemantics M] [IndexedUnionSemantics M]
    {n : ℕ} (t : DependentFields M n) (ht : t.WellFormed) :
    Obj (M := M) (DependentCartObj M n) := ⟨⟨t⟩, ht⟩

theorem tupleInDependentCart {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} (t : Obj (M := M) (TupleObj M n))
    (c : Obj (M := M) (DependentCartObj M n)) (h : c.val.fields.Accepts t.val.values) :
    In t c :=
  (c.val.fields.collect_members _ _).mpr ⟨t.val.values, h, rfl⟩

theorem inDependentCart_iff {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) :
    In p c ↔ M.mem (denote p) (FiniteFunction.cartValue
      (c.val.fields.factors (DependentFields.numberedCoordinates (denote p) indices))) := by
  rw [DependentFields.numberedCoordinates_eq _ _ hi]
  exact c.val.fields.members_iff_cart (denote p)

def dependentCartAt {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c) :
    Obj (M := M) (CartObj M n) :=
  cart (c.val.fields.factors (DependentFields.numberedCoordinates (denote p) indices))
    (c.val.fields.factors_isSet c.wd _ ((c.val.fields.accepts_iff _).mpr
      (by
        rw [DependentFields.numberedCoordinates_eq _ _ hi]
        exact FiniteFunction.coordinate_mem ((c.val.fields.members_iff_cart (denote p)).mp h))))

theorem inDependentCartAt {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c) :
    In p (dependentCartAt p c indices hi h) :=
  (inDependentCart_iff p c indices hi).mp h

/-- Reuse a carrier whose formation was checked by the structure declaration.
This is a projection of that certified family, not a fresh source constructor. -/
def dependentFieldCarrier {M : Semantics.{u}} [FunctionSemantics M]
    [IndexedUnionSemantics M] {n : ℕ} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (c : Obj (M := M) (DependentCartObj M n))
    (indices : Fin n → ℂ) (hi : ∀ i, indices i = ((i.val + 1 : ℕ) : ℂ)) (h : In p c)
    (i : Fin n) : Obj (M := M) M.Value :=
  let bound := dependentCartAt p c indices hi h
  semanticObject (bound.val.factors i) (bound.wd i)

theorem tuple_coordinate_mem {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (c : Obj (M := M) (CartObj M n))
    (h : In t c) (i : Fin n) : M.mem (t.val.values i) (c.val.factors i) := by
  have hc : M.mem (FunctionSemantics.callValue (FiniteFunction.tupleValue t.val.values)
    (FiniteFunction.index i)) (c.val.factors i) := FiniteFunction.coordinate_mem h i
  simpa only [FiniteFunction.call_tuple] using hc

/-- A tuple's own values provide the singleton factors of its finite contract. -/
def tupleSingletonCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) : Obj (M := M) (CartObj M n) :=
  cart (fun i => FiniteFunction.finiteSetValue [t.val.values i]) (by
    intro i
    apply FiniteFunction.finiteSet_isSet
    intro x hx
    have hx' : x = t.val.values i := List.mem_singleton.mp hx
    subst x
    exact t.wd i)

theorem tupleInSingletonCart {M : Semantics.{u}} [FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) : In t (tupleSingletonCart t) :=
  FiniteFunction.tuple_inCart _ _ (fun _ =>
    (FiniteFunction.finiteSet_members _ _).mpr (List.mem_singleton.mpr rfl))

theorem tuple_coordinate {M : Semantics.{u}} [F : FunctionSemantics M] {n : ℕ}
    (t : Obj (M := M) (TupleObj M n)) (i : Fin n) :
    F.callValue (denote t) (FiniteFunction.index i) = t.val.values i :=
  FiniteFunction.call_tuple _ i

structure ClosedRangeObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  start : Obj (M := M) α
  finish : Obj (M := M) β

def ClosedRangeObj.condition {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (r : ClosedRangeObj (M := M) α β) (value : M.Value) : Prop :=
  ∃ lower upper k : ℤ, denote r.start = M.number (lower : ℂ) ∧
    denote r.finish = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
    lower ≤ k ∧ k ≤ upper

instance closedRangeRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (ClosedRangeObj (M := M) α β) where
  wd r := In r.start Z ∧ In r.finish Z
  denote r := S.sepValue (M.standard .integer) r.condition
  wd_isSet _ := S.sep_isSet _ _ (M.standard_isSet .integer)

def closedRange {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a Z) (hb : In b Z) :
    Obj (M := M) (ClosedRangeObj (M := M) α β) := ⟨⟨a, b⟩, ⟨ha, hb⟩⟩

theorem inClosedRange_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) :
    In p (closedRange a b ha hb) ↔
      ∃ lower upper k : ℤ, denote a = M.number (lower : ℂ) ∧
        denote b = M.number (upper : ℂ) ∧ denote p = M.number (k : ℂ) ∧
        lower ≤ k ∧ k ≤ upper := by
  change M.mem (denote p) (S.sepValue (M.standard .integer) _) ↔ _
  rw [S.sep_members]
  constructor
  · exact fun h => h.2
  · rintro ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩
    exact ⟨(M.integer_members _).mpr ⟨k, hp⟩, lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem inClosedRangeOfDenote {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (lower upper k : ℤ)
    (hl : denote a = M.number (lower : ℂ))
    (hu : denote b = M.number (upper : ℂ))
    (hp : denote p = M.number (k : ℂ)) (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In p (closedRange a b ha hb) :=
  (inClosedRange_iff a b p ha hb).mpr ⟨lower, upper, k, hl, hu, hp, hlo, hhi⟩

theorem numberInClosedRange {M : Semantics.{u}} [SetSemantics M]
    (lower upper k : ℤ) (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In (number (M := M) (k : ℂ))
      (closedRange (number (lower : ℂ)) (number (upper : ℂ))
        (NativeBridge.numberInZ lower) (NativeBridge.numberInZ upper)) :=
  inClosedRangeOfDenote _ _ _ _ _ lower upper k rfl rfl rfl hlo hhi

theorem numberInClosedRangeOfEq {M : Semantics.{u}} [SetSemantics M]
    (a b p : ℂ) (lower upper k : ℤ)
    (ha : a = (lower : ℂ)) (hb : b = (upper : ℂ)) (hp : p = (k : ℂ))
    (hlo : lower ≤ k) (hhi : k ≤ upper) :
    In (number (M := M) p)
      (closedRange (number a) (number b)
        (NativeBridge.numberInZOfEq a lower ha) (NativeBridge.numberInZOfEq b upper hb)) :=
  inClosedRangeOfDenote _ _ _ _ _ lower upper k
    (congrArg M.number ha) (congrArg M.number hb) (congrArg M.number hp) hlo hhi

theorem closedRange_indexSet {M : Semantics.{u}} [F : FunctionSemantics M] (n : ℕ)
    (ha : In (number (M := M) 1) Z) (hb : In (number (M := M) (n : ℂ)) Z) :
    denote (closedRange (number (M := M) 1) (number (n : ℂ)) ha hb) =
      FiniteFunction.indexSet (M := M) n := by
  apply F.ext _ _ (isSet _) (FiniteFunction.indexSet_isSet n)
  intro value
  change M.mem value (F.sepValue (M.standard .integer) _) ↔ _
  rw [F.sep_members, FiniteFunction.indexSet_members]
  constructor
  · rintro ⟨_, lower, upper, k, hl, hu, hv, hlo, hhi⟩
    have hl' : lower = 1 := by
      change M.number 1 = M.number (lower : ℂ) at hl
      have h := M.number_injective hl
      exact_mod_cast h.symm
    have hu' : upper = (n : ℤ) := by
      change M.number (n : ℂ) = M.number (upper : ℂ) at hu
      have h := M.number_injective hu
      exact_mod_cast h.symm
    subst lower
    subst upper
    have hk0 : 0 ≤ k := le_trans (by norm_num) hlo
    have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have hkn : k.toNat ≤ n := by exact_mod_cast (hk.symm ▸ hhi)
    have hkpos : 1 ≤ k.toNat := by exact_mod_cast (hk.symm ▸ hlo)
    let i : Fin n := ⟨k.toNat - 1, by omega⟩
    refine ⟨i, hv.trans ?_⟩
    unfold FiniteFunction.index
    apply congrArg M.number
    have hi : i.val + 1 = k.toNat := by dsimp [i]; omega
    rw [hi]
    exact_mod_cast hk.symm
  · rintro ⟨i, rfl⟩
    have hk : M.mem (FiniteFunction.index (M := M) i) (M.standard .integer) := by
      apply (M.integer_members _).mpr
      refine ⟨(i.val + 1 : ℕ), ?_⟩
      simp [FiniteFunction.index]
    refine ⟨hk, 1, (n : ℤ), ((i.val + 1 : ℕ) : ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · change M.number 1 = M.number ((1 : ℤ) : ℂ)
      norm_num
    · change M.number (n : ℂ) = M.number ((n : ℤ) : ℂ)
      norm_num
    · simp [FiniteFunction.index]
    · exact_mod_cast (Nat.succ_le_succ (Nat.zero_le i.val))
    · exact_mod_cast (Nat.succ_le_of_lt i.isLt)


theorem indexSetMemberOfClosedRange {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] {p : Obj (M := M) α} {n : ℕ}
    {ha : In (number (M := M) 1) Z} {hb : In (number (M := M) (n : ℂ)) Z}
    (h : In p (closedRange (number (M := M) 1) (number (n : ℂ)) ha hb)) :
    M.mem (denote p) (FiniteFunction.indexSet n) := by
  change M.mem (denote p) (denote (closedRange _ _ ha hb)) at h
  rwa [closedRange_indexSet] at h

theorem indexSetMemberOfClosedRangeOfEq {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] {p : Obj (M := M) α} {n : ℕ}
    (z : ℂ) (hz : z = (n : ℂ))
    {ha : In (number (M := M) 1) Z} {hb : In (number (M := M) z) Z}
    (h : In p (closedRange (number (M := M) 1) (number z) ha hb)) :
    M.mem (denote p) (FiniteFunction.indexSet n) := by
  subst z
  exact indexSetMemberOfClosedRange h

structure UnionObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

instance unionRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (UnionObj (M := M) α β) where
  wd _ := True
  denote p := S.unionValue (denote p.left) (denote p.right)
  wd_isSet {p} _ := S.union_isSet _ _ (isSet p.left) (isSet p.right)

def union {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (UnionObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem inUnion_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (B : Obj (M := M) γ) :
    In a (union A B) ↔ In a A ∨ In a B := S.union_members _ _ _

structure PowerSetObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  bound : Obj (M := M) α

instance powerSetRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] : Representation M (PowerSetObj (M := M) α) where
  wd _ := True
  denote p := S.powerValue (denote p.bound)
  wd_isSet {p} _ := S.power_isSet _ (isSet p.bound)

def powerSet {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Obj (M := M) (PowerSetObj (M := M) α) := ⟨⟨A⟩, True.intro⟩

theorem inPowerSet_iff {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : In A (powerSet B) ↔ Subset A B := by
  change M.mem (denote A) (S.powerValue (denote B)) ↔ _
  rw [S.power_members]
  exact ⟨fun h => h.2, fun h => ⟨isSet A, h⟩⟩


/-- A function signature records its exact checked domain and return set. -/
structure FunctionSignature (M : Semantics.{u}) where
  domain : M.Value
  domain_isSet : M.isSet domain
  output : M.Value
  output_isSet : M.isSet output

namespace FunctionSignature

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def ofDomain (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B) : FunctionSignature M :=
  ⟨D, hD, B, hB⟩

def withGuard (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (guard : M.Value → Prop) : FunctionSignature M :=
  ⟨F.sepValue D guard, F.sep_isSet D guard hD, B, hB⟩

theorem withGuard_domain (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B)
    (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (withGuard D B hD hB guard).domain ↔ M.mem x D ∧ guard x :=
  F.sep_members D guard x

def oneTarget (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) : FunctionSignature M :=
  withGuard (M.standard A) B (M.standard_isSet A) hB guard

noncomputable def twoTarget (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) : FunctionSignature M :=
  withGuard (FiniteFunction.cartValue ![M.standard A, M.standard E]) B
    (FiniteFunction.cart_isSet _ (by intro i; fin_cases i <;> exact M.standard_isSet _))
    hB (fun p => guard (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2)

def one (A B : StandardSetValue) (guard : M.Value → Prop) : FunctionSignature M :=
  oneTarget A (M.standard B) (M.standard_isSet B) guard

noncomputable def two (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop) :
    FunctionSignature M := twoTarget A E (M.standard B) (M.standard_isSet B) guard

def target (s : FunctionSignature M) : M.Value := s.output

theorem oneTarget_domain (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (oneTarget A B hB guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  F.sep_members _ _ _

theorem twoTarget_domain (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (a b : M.Value) :
    M.mem (FiniteFunction.pack2 a b) (twoTarget A E B hB guard).domain ↔
      M.mem a (M.standard A) ∧ M.mem b (M.standard E) ∧ guard a b := by
  change M.mem (FiniteFunction.pack2 a b)
    (F.sepValue (FiniteFunction.cartValue ![M.standard A, M.standard E]) _) ↔ _
  rw [F.sep_members]
  simp only [FiniteFunction.unpack_pack2]
  constructor
  · rintro ⟨h, hg⟩
    obtain ⟨x, hx, y, hy, hp⟩ := (FiniteFunction.cart2_members _ _ _).mp h
    obtain ⟨rfl, rfl⟩ := FiniteFunction.pack2_injective hp
    exact ⟨hx, hy, hg⟩
  · rintro ⟨ha, hb, hg⟩
    exact ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨a, ha, b, hb, rfl⟩, hg⟩

theorem one_domain (A B : StandardSetValue) (guard : M.Value → Prop) (x : M.Value) :
    M.mem x (one A B guard).domain ↔ M.mem x (M.standard A) ∧ guard x :=
  oneTarget_domain A (M.standard B) (M.standard_isSet B) guard x

theorem two_domain (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (a b : M.Value) :
    M.mem (FiniteFunction.pack2 a b) (two A E B guard).domain ↔
      M.mem a (M.standard A) ∧ M.mem b (M.standard E) ∧ guard a b :=
  twoTarget_domain A E (M.standard B) (M.standard_isSet B) guard a b

end FunctionSignature

instance functionSignatureRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (FunctionSignature M) where
  wd _ := True
  denote s := F.fnSetValue s.domain s.target
  wd_isSet {s} _ := F.fnSet_isSet _ _ s.domain_isSet s.output_isSet

def fnSet {M : Semantics.{u}} [FunctionSemantics M] (s : FunctionSignature M) :
    Obj (M := M) (FunctionSignature M) := ⟨s, True.intro⟩

/-- Finite sequences retain the source carrier and length objects. Their
complete domain is the one-based integer interval, with no extra guard. -/
structure FiniteSeqSetObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  carrier : Obj (M := M) α
  length : Obj (M := M) β

def finiteSeqDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) : M.Value :=
  F.sepValue (F.sepValue (M.standard .integer)
    (ClosedRangeObj.condition ⟨number 1, length⟩)) (fun _ => True)

theorem finiteSeqDomain_isSet {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) :
    M.isSet (finiteSeqDomain length) :=
  F.sep_isSet _ _ (F.sep_isSet _ _ (M.standard_isSet .integer))

instance finiteSeqSetRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (FiniteSeqSetObj (M := M) α β) where
  wd s := IsSet s.carrier ∧ In s.length N
  denote s := F.fnSetValue (finiteSeqDomain s.length) (denote s.carrier)
  wd_isSet {s} h := F.fnSet_isSet _ _ (finiteSeqDomain_isSet s.length) h.1

def finiteSeq {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (n : Obj (M := M) β) (hA : IsSet A) (hn : In n N) :
    Obj (M := M) (FiniteSeqSetObj (M := M) α β) := ⟨⟨A, n⟩, hA, hn⟩

def finiteSeqSignature {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) : FunctionSignature M :=
  ⟨finiteSeqDomain s.val.length, finiteSeqDomain_isSet s.val.length,
    denote s.val.carrier, s.wd.1⟩

theorem finiteSeq_eq_fnSet {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) :
    Same s (fnSet (finiteSeqSignature s)) := rfl

/-- Injectivity compares semantic values on the requested domain. Callability
and the codomain are checked by the source fact's separate WD evidence. -/
def injectiveValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A _B f : M.Value) : Prop :=
  ∀ x, M.mem x A → ∀ y, M.mem y A → F.callValue f x = F.callValue f y → x = y

def surjectiveValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : Prop :=
  ∀ y, M.mem y B → ∃ x, M.mem x A ∧ y = F.callValue f x

def bijectiveValue {M : Semantics.{u}} [FunctionSemantics M]
    (A B f : M.Value) : Prop := injectiveValue A B f ∧ surjectiveValue A B f

theorem injectiveValue_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : injectiveValue A B f ↔
    (∀ (x : Obj (M := M) M.Value), M.mem (denote x) A →
     ∀ (y : Obj (M := M) M.Value), M.mem (denote y) A →
       F.callValue f (denote x) = F.callValue f (denote y) → denote x = denote y) := by
  constructor
  · intro h x hx y hy eq
    exact h (denote x) hx (denote y) hy eq
  · intro h x hx y hy eq
    exact h (semanticObject x (M.member_isSet hx)) hx
      (semanticObject y (M.member_isSet hy)) hy eq

theorem surjectiveValue_iff {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f : M.Value) : surjectiveValue A B f ↔
    (∀ (y : Obj (M := M) M.Value), M.mem (denote y) B →
      ∃ x : Obj (M := M) M.Value, ∃ (_hx : M.mem (denote x) A), denote y = F.callValue f (denote x)) := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, eq⟩ := h (denote y) hy
    exact ⟨semanticObject x (M.member_isSet hx), hx, eq⟩
  · intro h y hy
    obtain ⟨x, hx, eq⟩ := h (semanticObject y (M.member_isSet hy)) hy
    exact ⟨denote x, hx, eq⟩

theorem bijectiveValue_preimage {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f y : M.Value) (h : bijectiveValue A B f) (hy : M.mem y B) :
    (∃ x : Obj (M := M) M.Value, ∃ (_hx : M.mem (denote x) A), F.callValue f (denote x) = y) ∧
    (∀ (x : Obj (M := M) M.Value), M.mem (denote x) A →
     ∀ (z : Obj (M := M) M.Value), M.mem (denote z) A →
       F.callValue f (denote x) = y → F.callValue f (denote z) = y → denote x = denote z) := by
  constructor
  · obtain ⟨x, hx, eq⟩ := h.2 y hy
    exact ⟨semanticObject x (M.member_isSet hx), hx, eq.symm⟩
  · intro x hx z hz ex ez
    exact h.1 (denote x) hx (denote z) hz (ex.trans ez.symm)

/-- A checked Cartesian member retains its complete finite domain when its
return bound is changed using the supplied return proof. -/
theorem cartMemberInFnSetOfReturns {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] {n : ℕ}
    (f : Obj (M := M) α) (A : Obj (M := M) (CartObj M n))
    (s : FunctionSignature M) (hf : In f A)
    (hd : s.domain = FiniteFunction.indexSet n)
    (hr : ∀ x, M.mem x s.domain → M.mem (F.callValue (denote f) x) s.output) :
    In f (fnSet s) := by
  have graph : M.mem (denote f) (F.fnSetValue (FiniteFunction.indexSet n)
      (FiniteFunction.finiteUnionValue (List.ofFn A.val.factors))) :=
    ((F.sep_members _ _ _).mp hf).1
  rw [← hd] at graph
  exact F.fnSet_of_returns graph hr

theorem finiteSeqDomain_number {M : Semantics.{u}} [F : FunctionSemantics M] (n : ℕ) :
    finiteSeqDomain (number (M := M) (n : ℂ)) = FiniteFunction.indexSet n := by
  let interval := closedRange (number (M := M) 1) (number (n : ℂ))
    (NativeBridge.numberInZOfEq 1 1 (by norm_num)) (naturalToInteger _ (NativeBridge.numberInN n))
  have h : F.sepValue (denote interval) (fun _ => True) = denote interval := by
    apply F.ext _ _ (F.sep_isSet _ _ (isSet interval)) (isSet interval)
    intro x
    exact (F.sep_members _ _ x).trans ⟨And.left, fun h => ⟨h, True.intro⟩⟩
  exact h.trans (closedRange_indexSet n _ _)

theorem finiteSeqDomain_ofDenote {M : Semantics.{u}} [F : FunctionSemantics M]
    {β : Type w} [Representation M β] (length : Obj (M := M) β) (n : ℕ)
    (hn : denote length = M.number (n : ℂ)) :
    finiteSeqDomain length = FiniteFunction.indexSet n := by
  change F.sepValue (F.sepValue (M.standard .integer)
    (fun value => ∃ lower upper k : ℤ, M.number 1 = M.number (lower : ℂ) ∧
      denote length = M.number (upper : ℂ) ∧ value = M.number (k : ℂ) ∧
      lower ≤ k ∧ k ≤ upper)) (fun _ => True) = _
  rw [hn]
  exact finiteSeqDomain_number n

theorem denoteFiniteSeq {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) α β)) (n : ℕ)
    (hn : Same s.val.length (number (n : ℂ))) :
    denote s = F.fnSetValue (FiniteFunction.indexSet n) (denote s.val.carrier) :=
  congrArg (fun D => F.fnSetValue D (denote s.val.carrier))
    (finiteSeqDomain_ofDenote s.val.length n hn)

structure FunctionBranch (M : Semantics.{u}) where
  guard : M.Value → Prop
  body : M.Value → M.Value

noncomputable def piecewiseValue {M : Semantics.{u}} : List (FunctionBranch M) → M.Value → M.Value
  | [], _ => M.number 0
  | branch :: rest, x => by
      classical
      exact if branch.guard x then branch.body x else piecewiseValue rest x

theorem piecewiseValue_eq {M : Semantics.{u}} (branches : List (FunctionBranch M))
    (D : M.Value)
    (disjoint : branches.Pairwise (fun a b => ∀ x, M.mem x D → ¬ (a.guard x ∧ b.guard x)))
    (branch : FunctionBranch M) (member : branch ∈ branches)
    (x : M.Value) (hx : M.mem x D) (guard : branch.guard x) :
    piecewiseValue branches x = branch.body x := by
  classical
  induction branches with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨apart, tail⟩ := List.pairwise_cons.mp disjoint
      rcases List.mem_cons.mp member with rfl | member
      · exact if_pos guard
      · have no_first : ¬ first.guard x := fun h => apart branch member x hx ⟨h, guard⟩
        change (if first.guard x then first.body x else piecewiseValue rest x) = _
        rw [if_neg no_first]
        exact ih tail member

structure PiecewiseFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  branches : List (FunctionBranch M)

def PiecewiseFn.Valid {M : Semantics.{u}} (f : PiecewiseFn M) : Prop :=
  (∀ x, M.mem x f.signature.domain → ∃ b ∈ f.branches, b.guard x) ∧
  f.branches.Pairwise (fun a b => ∀ x, M.mem x f.signature.domain → ¬ (a.guard x ∧ b.guard x)) ∧
  (∀ b ∈ f.branches, ∀ x, M.mem x f.signature.domain → b.guard x → M.mem (b.body x) f.signature.output)

theorem PiecewiseFn.value_mem {M : Semantics.{u}} (f : PiecewiseFn M) (h : f.Valid)
    (x : M.Value) (hx : M.mem x f.signature.domain) :
    M.mem (piecewiseValue f.branches x) f.signature.output := by
  obtain ⟨b, hb, hg⟩ := h.1 x hx
  rw [piecewiseValue_eq f.branches f.signature.domain h.2.1 b hb x hx hg]
  exact h.2.2 b hb x hx hg

noncomputable instance piecewiseFnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (PiecewiseFn M) where
  wd := PiecewiseFn.Valid
  denote f := F.graphValue f.signature.domain f.signature.output (piecewiseValue f.branches)
  wd_isSet {f} h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ (f.value_mem h))

noncomputable def piecewiseFn {M : Semantics.{u}} [FunctionSemantics M]
    (signature : FunctionSignature M) (branches : List (FunctionBranch M))
    (h : (PiecewiseFn.mk signature branches).Valid) : Obj (M := M) (PiecewiseFn M) :=
  ⟨⟨signature, branches⟩, h⟩

theorem piecewiseFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (PiecewiseFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ (f.val.value_mem f.wd)

theorem piecewiseFn_call_eq {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (PiecewiseFn M)) (branch : FunctionBranch M)
    (member : branch ∈ f.val.branches) (x : M.Value)
    (hx : M.mem x f.val.signature.domain) (guard : branch.guard x) :
    F.callValue (denote f) x = branch.body x := by
  have h := FunctionSemantics.call_graphValue f.val.signature.domain f.val.signature.output
    (piecewiseValue f.val.branches) (f.val.value_mem f.wd) x hx
  exact h.trans (piecewiseValue_eq _ _ f.wd.2.1 branch member x hx guard)

/-- A function specified by a unique output, with no formula body to unfold. -/
structure SelectedFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  property : M.Value → M.Value → Prop

/-- Move canonical Litex witnesses to semantic values; uniqueness still compares
denotations, never arbitrary host payloads. -/
theorem existsUniqueValueOfObjects {M : Semantics.{u}} (B : M.Value)
    (P : M.Value → Prop)
    (existsObject : ∃ y : Obj (M := M) M.Value, M.mem (denote y) B ∧ P (denote y))
    (uniqueObject : ∀ a b : Obj (M := M) M.Value,
      M.mem (denote a) B → M.mem (denote b) B → P (denote a) → P (denote b) → Same a b) :
    ∃! y, M.mem y B ∧ P y := by
  obtain ⟨y, hy, hp⟩ := existsObject
  refine ⟨denote y, ⟨hy, hp⟩, ?_⟩
  intro z hz
  exact uniqueObject (semanticObject z (M.member_isSet hz.1)) y hz.1 hy hz.2 hp

/-- The existing selected-function value, also usable under raw lexical
substitution. Construction still requires existence and uniqueness on domain. -/
noncomputable def selectedValue {M : Semantics.{u}}
    (output : M.Value) (property : M.Value → M.Value → Prop) (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ y, M.mem y output ∧ property x y then
    Classical.choose h
  else M.number 0

noncomputable def SelectedFn.value {M : Semantics.{u}}
    (f : SelectedFn M) (x : M.Value) : M.Value :=
  selectedValue (M := M) f.signature.output f.property x

theorem SelectedFn.value_spec {M : Semantics.{u}} (f : SelectedFn M) (x : M.Value)
    (h : ∃! y, M.mem y f.signature.output ∧ f.property x y) :
    M.mem (f.value x) f.signature.output ∧ f.property x (f.value x) := by
  rw [SelectedFn.value, selectedValue, dif_pos h.exists]
  exact Classical.choose_spec h.exists

noncomputable instance selectedFnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] : Representation M (SelectedFn M) where
  wd f := ∀ x, M.mem x f.signature.domain →
    ∃! y, M.mem y f.signature.output ∧ f.property x y
  denote f := F.graphValue f.signature.domain f.signature.output f.value
  wd_isSet h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
      (SelectedFn.value_spec _ x (h x hx)).1))

noncomputable def selectedFn {M : Semantics.{u}} [FunctionSemantics M]
    (s : FunctionSignature M) (property : M.Value → M.Value → Prop)
    (h : ∀ x, M.mem x s.domain → ∃! y, M.mem y s.output ∧ property x y) :
    Obj (M := M) (SelectedFn M) := ⟨⟨s, property⟩, h⟩

theorem selectedFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun x hx =>
    (SelectedFn.value_spec f.val x (f.wd x hx)).1)

theorem selectedFn_call_spec {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) (x : M.Value)
    (hx : M.mem x f.val.signature.domain) :
    M.mem (F.callValue (denote f) x) f.val.signature.output ∧
      f.val.property x (F.callValue (denote f) x) := by
  have value_eq : F.callValue (denote f) x = f.val.value x :=
    FunctionSemantics.call_graphValue _ _ _
      (fun x hx => (SelectedFn.value_spec f.val x (f.wd x hx)).1) x hx
  rw [value_eq]
  exact SelectedFn.value_spec f.val x (f.wd x hx)

theorem selectedFn_unique {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (SelectedFn M)) (x y : M.Value)
    (hx : M.mem x f.val.signature.domain)
    (hy : M.mem y f.val.signature.output ∧ f.val.property x y) :
    y = F.callValue (denote f) x :=
  (f.wd x hx).unique hy (selectedFn_call_spec f x hx)

theorem selectedFn_proofIndependent {M : Semantics.{u}} [FunctionSemantics M]
    (s : FunctionSignature M) (property : M.Value → M.Value → Prop)
    (h k : ∀ x, M.mem x s.domain → ∃! y, M.mem y s.output ∧ property x y) :
    Same (selectedFn s property h) (selectedFn s property k) := rfl

/-- A formula object denotes a set-theoretic graph, not its interpretation callback.
The callback is the compiler's recursive interpretation of the source body AST. -/
structure FormulaFn (M : Semantics.{u}) where
  signature : FunctionSignature M
  bodyValue : M.Value → M.Value

instance formulaFnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M] :
    Representation M (FormulaFn M) where
  wd f := ∀ x, M.mem x f.signature.domain → M.mem (f.bodyValue x) f.signature.target
  denote f := F.graphValue f.signature.domain f.signature.target f.bodyValue
  wd_isSet h := M.member_isSet
    (FunctionSemantics.graph_inFnSet _ _ _ h)

def formulaFnTarget {M : Semantics.{u}} [FunctionSemantics M]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B) :
    Obj (M := M) (FormulaFn M) :=
  ⟨⟨FunctionSignature.oneTarget A B hB guard, body⟩, fun x hx =>
    hReturn x ((FunctionSignature.oneTarget_domain A B hB guard x).mp hx).1
      ((FunctionSignature.oneTarget_domain A B hB guard x).mp hx).2⟩

noncomputable def formulaFn2Target {M : Semantics.{u}} [F : FunctionSemantics M]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B) : Obj (M := M) (FormulaFn M) := by
  let s := FunctionSignature.twoTarget A E B hB guard
  let interpretation := fun p => body (FiniteFunction.unpack2 p).1
    (FiniteFunction.unpack2 p).2
  refine ⟨⟨s, interpretation⟩, ?_⟩
  intro p hp
  obtain ⟨hproduct, hg⟩ := (F.sep_members
    (FiniteFunction.cartValue ![M.standard A, M.standard E])
    (fun p => guard (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2) p).mp hp
  obtain ⟨x, hx, y, hy, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp hproduct
  change M.mem (body _ _) B
  simpa only [FiniteFunction.unpack_pack2] using hReturn x y hx hy
    (by simpa only [s, FunctionSignature.twoTarget, FiniteFunction.unpack_pack2] using hg)

def formulaFn {M : Semantics.{u}} [FunctionSemantics M]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B)) :
    Obj (M := M) (FormulaFn M) :=
  formulaFnTarget A (M.standard B) (M.standard_isSet B) guard body hReturn

noncomputable def formulaFn2 {M : Semantics.{u}} [FunctionSemantics M]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B)) : Obj (M := M) (FormulaFn M) :=
  formulaFn2Target A E (M.standard B) (M.standard_isSet B) guard body hReturn

theorem formulaFnInFnSet {M : Semantics.{u}} [FunctionSemantics M]
    (f : Obj (M := M) (FormulaFn M)) : In f (fnSet f.val.signature) :=
  FunctionSemantics.graph_inFnSet _ _ _ f.wd

def formulaFnOn {M : Semantics.{u}} [FunctionSemantics M]
    (signature : FunctionSignature M) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x signature.domain → M.mem (body x) signature.output) :
    Obj (M := M) (FormulaFn M) := ⟨⟨signature, body⟩, hReturn⟩

structure FamilyUnionObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  family : Obj (M := M) α

instance familyUnionRepresentation {M : Semantics.{u}} [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] : Representation M (FamilyUnionObj (M := M) α) where
  wd _ := True
  denote p := I.indexedUnionValue (denote p.family) id
  wd_isSet {p} _ := I.indexedUnion_isSet _ _ (isSet p.family) (fun _ h => M.member_isSet h)

def familyUnion {M : Semantics.{u}} [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Obj (M := M) (FamilyUnionObj (M := M) α) := ⟨⟨A⟩, True.intro⟩

theorem familyUnion_members {M : Semantics.{u}} [I : IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (x : M.Value) :
    M.mem x (denote (familyUnion A)) ↔ ∃ a, M.mem a (denote A) ∧ M.mem x a :=
  I.indexedUnion_members _ _ _

def IsChoiceFunctionFor {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (index : Obj (M := M) α) (_set : Obj (M := M) β)
    (family : Obj (M := M) γ) (choice : Obj (M := M) δ) : Prop :=
  ∀ x, M.mem x (denote index) →
    M.mem (F.callValue (denote choice) x) (F.callValue (denote family) x)

theorem choiceForIdentity {M : Semantics.{u}} [F : FunctionSemantics M] [IndexedUnionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (S : Obj (M := M) α) (g : Obj (M := M) β)
    (hg : ∀ x, M.mem x (denote S) → F.callValue (denote g) x = x)
    (hS : ∀ a : Obj (M := M) M.Value, In a S → IsNonempty a) :
    ∃ f : Obj (M := M) M.Value,
      ∃ (_ : In f (fnSet (FunctionSignature.withGuard (denote S) (denote (familyUnion S))
        (isSet S) (isSet (familyUnion S)) (fun _ => True)))), IsChoiceFunctionFor S S g f := by
  classical
  let select := fun x : M.Value => if h : ∃ y, M.mem y x then Classical.choose h else F.emptyValue
  have selected : ∀ x, M.mem x (denote S) → M.mem (select x) x := by
    intro x hx
    have h := hS (semanticObject x (M.member_isSet hx)) hx
    change ∃ y, M.mem y x at h
    dsimp only [select]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hreturn : ∀ x, M.mem x (denote S) → M.mem (select x) (denote (familyUnion S)) := by
    intro x hx
    exact (familyUnion_members S _).mpr ⟨x, hx, selected x hx⟩
  let D := F.sepValue (denote S) (fun _ => True)
  have hreturnD : ∀ x, M.mem x D → M.mem (select x) (denote (familyUnion S)) := by
    intro x hx
    exact hreturn x ((F.sep_members _ _ _).mp hx).1
  let value := F.graphValue D (denote (familyUnion S)) select
  have hvalue := FunctionSemantics.graph_inFnSet _ _ _ hreturnD
  let f := semanticObject value (M.member_isSet hvalue)
  refine ⟨f, hvalue, ?_⟩
  intro x hx
  change M.mem (F.callValue value x) (F.callValue (denote g) x)
  have hxD : M.mem x D := (F.sep_members _ _ _).mpr ⟨hx, True.intro⟩
  rw [hg x hx, FunctionSemantics.call_graphValue _ _ _ hreturnD x hxD]
  exact selected x hx

theorem formulaIdentityCall {M : Semantics.{u}} [F : FunctionSemantics M]
    (g : Obj (M := M) (FormulaFn M)) (hg : ∀ x, g.val.bodyValue x = x)
    (x : M.Value) (hx : M.mem x g.val.signature.domain) : F.callValue (denote g) x = x :=
  (FunctionSemantics.call_graphValue _ _ _ g.wd x hx).trans (hg x)


theorem zornMaximal {M : Semantics.{u}} [F : SetSemantics M]
    {α : Type v} [Representation M α] (S : Obj (M := M) α) (r : M.Value → M.Value → Prop)
    (hrefl : ∀ x, M.mem x (denote S) → r x x)
    (htrans : ∀ x y z, M.mem x (denote S) → M.mem y (denote S) → M.mem z (denote S) → r x y → r y z → r x z)
    (hanti : ∀ x y, M.mem x (denote S) → M.mem y (denote S) → r x y → r y x → x = y)
    (hbound : ∀ c : Obj (M := M) M.Value, In c (powerSet S) →
      (∀ x y, M.mem x (denote c) → M.mem y (denote c) → r x y ∨ r y x) →
      ∃ b, M.mem b (denote S) ∧ ∀ x, M.mem x (denote c) → r x b) :
    ∃ m : Obj (M := M) M.Value, ∃ (_ : In m S),
      ∀ x, M.mem x (denote S) → r (denote m) x → x = denote m := by
  classical
  let A := {x : M.Value // M.mem x (denote S)}
  have bounded : ∀ c : Set A, IsChain (fun x y : A => r x.val y.val) c →
      ∃ b : A, ∀ a ∈ c, r a.val b.val := by
    intro c hc
    let C := F.sepValue (denote S) (fun x => ∃ hx, (⟨x, hx⟩ : A) ∈ c)
    let Cobj := semanticObject C (F.sep_isSet _ _ (isSet S))
    have cmem : In Cobj (powerSet S) := by
      apply (F.power_members _ _).mpr
      exact ⟨isSet Cobj, fun x hx => ((F.sep_members _ _ _).mp hx).1⟩
    obtain ⟨b, hb, hub⟩ := hbound Cobj cmem (by
      intro x y hx hy
      obtain ⟨hxS, hxC⟩ := (F.sep_members _ _ _).mp hx
      obtain ⟨hyS, hyC⟩ := (F.sep_members _ _ _).mp hy
      obtain ⟨_, hxC⟩ := hxC
      obtain ⟨_, hyC⟩ := hyC
      by_cases heq : x = y
      · exact Or.inl (heq ▸ hrefl x hxS)
      · exact hc hxC hyC (fun h => heq (congrArg Subtype.val h)))
    refine ⟨⟨b, hb⟩, ?_⟩
    intro a ha
    apply hub a.val
    exact (F.sep_members _ _ _).mpr ⟨a.property, a.property, ha⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded bounded
    (fun {a b c : A} hab hbc => htrans a.val b.val c.val a.property b.property c.property hab hbc)
  refine ⟨semanticObject m.val (M.member_isSet m.property), m.property, ?_⟩
  intro x hx hmx
  exact hanti x m.val hx m.property (hm ⟨x, hx⟩ hmx) hmx


structure CallOnObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  signature : FunctionSignature M
  function : Obj (M := M) α
  argument : Obj (M := M) β

instance callOnRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallOnObj (M := M) α β) where
  wd c := In c.function (fnSet c.signature) ∧ M.mem (denote c.argument) c.signature.domain
  denote c := F.callValue (denote c.function) (denote c.argument)
  wd_isSet h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1 h.2)

def callOn {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (signature : FunctionSignature M) (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet signature)) (ha : M.mem (denote a) signature.domain) :
    Obj (M := M) (CallOnObj (M := M) α β) := ⟨⟨signature, f, a⟩, hf, ha⟩

/-- Use the original base-domain and guard proofs for the same guarded call. -/
def callOnDomain {M : Semantics.{u}} [FunctionSemantics M]
    {δ : Type v} {ε : Type w} {α : Type x} {β : Type t}
    [Representation M δ] [Representation M ε]
    [Representation M α] [Representation M β]
    (D : Obj (M := M) δ) (O : Obj (M := M) ε)
    (guard : M.Value → Prop) (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.withGuard
      (denote D) (denote O) (isSet D) (isSet O) guard)))
    (ha : In a D) (hg : guard (denote a)) :
    Obj (M := M) (CallOnObj (M := M) α β) :=
  callOn (FunctionSignature.withGuard
    (denote D) (denote O) (isSet D) (isSet O) guard) f a hf
    ((FunctionSignature.withGuard_domain
      (denote D) (denote O) (isSet D) (isSet O) guard (denote a)).mpr ⟨ha, hg⟩)

theorem callOnInOutput {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallOnObj (M := M) α β)) :
    In c (semanticObject c.val.signature.output c.val.signature.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1 c.wd.2

/-- Complete equal domains and equal calls identify the graphs. Return upper
bounds may differ, so they are retained independently for the two functions. -/
theorem functionExtOnDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (g : Obj (M := M) β)
    (s t : FunctionSignature M) (hf : In f (fnSet s)) (hg : In g (fnSet t))
    (hD : s.domain = t.domain)
    (h : ∀ x, M.mem x s.domain → F.callValue (denote f) x = F.callValue (denote g) x) :
    Same f g := by
  have hfg := (F.fnSet_members _ _ _).mp hf
  have hgg := (F.fnSet_members _ _ _).mp hg
  apply F.ext _ _ (isSet f) (isSet g)
  intro edge
  constructor
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := hfg.1 edge he
    have hy := (FiniteFunction.graph_pair_value hfg he).2
    rw [hy, h x hx]
    exact F.call_graph _ _ _ _ hgg (hD ▸ hx)
  · intro he
    obtain ⟨x, hx, y, _, rfl⟩ := hgg.1 edge he
    have hy := (FiniteFunction.graph_pair_value hgg he).2
    have hx' : M.mem x s.domain := hD.symm ▸ hx
    rw [hy, ← h x hx']
    exact F.call_graph _ _ _ _ hfg hx'

/-- A Cartesian membership supplies the complete finite function contract. -/
def cartCall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] {n : ℕ}
    (p : Obj (M := M) α) (c : Obj (M := M) (CartObj M n)) (a : Obj (M := M) β)
    (hp : In p c) (ha : M.mem (denote a) (FiniteFunction.indexSet n)) :
    Obj (M := M) (CallOnObj (M := M) α β) :=
  let signature := FunctionSignature.ofDomain (FiniteFunction.indexSet n)
    (FiniteFunction.finiteUnionValue (List.ofFn c.val.factors))
    (FiniteFunction.indexSet_isSet n)
    (FiniteFunction.finiteUnion_isSet _ (by
      intro A hA
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      exact c.wd i))
  callOn signature p a ((F.fnSet_members _ _ _).mpr
    ((FiniteFunction.cart_members _ _).mp hp).1) ha

theorem callOnCongr {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CallOnObj (M := M) α β))
    (d : Obj (M := M) (CallOnObj (M := M) γ δ))
    (hf : Same c.val.function d.val.function) (ha : Same c.val.argument d.val.argument) :
    Same c d := congrArg₂ F.callValue hf ha

theorem callFormulaOn_denote {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α]
    (signature : FunctionSignature M) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x signature.domain → M.mem (body x) signature.output)
    (a : Obj (M := M) α) (ha : M.mem (denote a) signature.domain) :
    denote (callOn signature (formulaFnOn signature body hReturn) a
      (formulaFnInFnSet _) ha) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ hReturn _ ha

structure CallObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  input : StandardSetValue
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → Prop
  function : Obj (M := M) α
  argument : Obj (M := M) β

instance callRepresentation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (CallObj (M := M) α β) where
  wd c := In c.function
    (fnSet (FunctionSignature.oneTarget c.input c.output c.output_isSet c.guard)) ∧
    M.mem (denote c.argument) (M.standard c.input) ∧ c.guard (denote c.argument)
  denote c := F.callValue (denote c.function) (denote c.argument)
  wd_isSet {c} h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1
    ((FunctionSignature.oneTarget_domain c.input c.output c.output_isSet c.guard _).mpr h.2))

def callTarget {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B) (guard : M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.oneTarget A B hB guard)))
    (ha : In a (standardSet A)) (hg : guard (denote a)) :
    Obj (M := M) (CallObj (M := M) α β) := ⟨⟨A, B, hB, guard, f, a⟩, hf, ha, hg⟩

def call {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A B : StandardSetValue) (guard : M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β)
    (hf : In f (fnSet (FunctionSignature.one A B guard)))
    (ha : In a (standardSet A)) (hg : guard (denote a)) :
    Obj (M := M) (CallObj (M := M) α β) :=
  callTarget A (M.standard B) (M.standard_isSet B) guard f a hf ha hg

structure CallObj2 {M : Semantics.{u}} (α : Type v) (β : Type w) (γ : Type t)
    [Representation M α] [Representation M β] [Representation M γ] where
  firstInput : StandardSetValue
  secondInput : StandardSetValue
  output : M.Value
  output_isSet : M.isSet output
  guard : M.Value → M.Value → Prop
  function : Obj (M := M) α
  first : Obj (M := M) β
  second : Obj (M := M) γ

noncomputable instance call2Representation {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ] :
    Representation M (CallObj2 (M := M) α β γ) where
  wd c := In c.function (fnSet (FunctionSignature.twoTarget c.firstInput c.secondInput
    c.output c.output_isSet c.guard)) ∧ M.mem (denote c.first) (M.standard c.firstInput) ∧
    M.mem (denote c.second) (M.standard c.secondInput) ∧ c.guard (denote c.first) (denote c.second)
  denote c := F.callValue (denote c.function) (FiniteFunction.pack2 (denote c.first) (denote c.second))
  wd_isSet {c} h := M.member_isSet (FunctionSemantics.call_mem _ _ _ _ h.1
    ((FunctionSignature.twoTarget_domain c.firstInput c.secondInput c.output
      c.output_isSet c.guard _ _).mpr h.2))

noncomputable def call2Target {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β) (b : Obj (M := M) γ)
    (hf : In f (fnSet (FunctionSignature.twoTarget A E B hB guard)))
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    Obj (M := M) (CallObj2 (M := M) α β γ) :=
  ⟨⟨A, E, B, hB, guard, f, a, b⟩, hf, ha, hb, hg⟩

noncomputable def call2 {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (f : Obj (M := M) α) (a : Obj (M := M) β) (b : Obj (M := M) γ)
    (hf : In f (fnSet (FunctionSignature.two A E B guard)))
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    Obj (M := M) (CallObj2 (M := M) α β γ) :=
  call2Target A E (M.standard B) (M.standard_isSet B) guard f a b hf ha hb hg


section FunctionObjects

variable {M : Semantics.{u}} [F : FunctionSemantics M]

/-- These laws consume the WD proofs stored in the call object. -/
theorem callInOutput {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (c : Obj (M := M) (CallObj (M := M) α β)) :
    In c (semanticObject c.val.output c.val.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1
    ((FunctionSignature.oneTarget_domain c.val.input c.val.output
      c.val.output_isSet c.val.guard _).mpr c.wd.2)

theorem call2InOutput {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ)) :
    In c (semanticObject c.val.output c.val.output_isSet) :=
  FunctionSemantics.call_mem _ _ _ _ c.wd.1
    ((FunctionSignature.twoTarget_domain c.val.firstInput c.val.secondInput c.val.output
      c.val.output_isSet c.val.guard _ _).mpr c.wd.2)

omit F in
theorem functionObject_proofIndependent {α : Type v} [Representation M α]
    (a : α) (h₁ h₂ : WD (M := M) a) :
    denote (⟨a, h₁⟩ : Obj (M := M) α) = denote (⟨a, h₂⟩ : Obj (M := M) α) := rfl

theorem callCongr {α : Type v} {β : Type w} {γ : Type t} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (c : Obj (M := M) (CallObj (M := M) α β))
    (d : Obj (M := M) (CallObj (M := M) γ δ))
    (hf : Same c.val.function d.val.function) (ha : Same c.val.argument d.val.argument) :
    Same c d := congrArg₂ F.callValue hf ha

theorem call2Congr {α : Type v} {β : Type w} {γ : Type t}
    {δ : Type*} {ε : Type*} {ζ : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε] [Representation M ζ]
    (c : Obj (M := M) (CallObj2 (M := M) α β γ))
    (d : Obj (M := M) (CallObj2 (M := M) δ ε ζ))
    (hf : Same c.val.function d.val.function)
    (ha : Same c.val.first d.val.first) (hb : Same c.val.second d.val.second) :
    Same c d := congrArg₂ F.callValue hf (congrArg₂ FiniteFunction.pack2 ha hb)

theorem callFormulaTarget_denote {α : Type v} [Representation M α]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B)
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a)) :
    denote (callTarget A B hB guard (formulaFnTarget A B hB guard body hReturn) a
      (formulaFnInFnSet _) ha hg) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ (formulaFnTarget A B hB guard body hReturn).wd _
    ((FunctionSignature.oneTarget_domain A B hB guard _).mpr ⟨ha, hg⟩)

theorem callFormulaTarget_same {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) B)
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a))
    (b : Obj (M := M) β) (hBody : body (denote a) = denote b) :
    Same (callTarget A B hB guard (formulaFnTarget A B hB guard body hReturn) a
      (formulaFnInFnSet _) ha hg) b :=
  (callFormulaTarget_denote A B hB guard body hReturn a ha hg).trans hBody

theorem callFormula2Target_denote {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B)
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    denote (call2Target A E B hB guard (formulaFn2Target A E B hB guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) = body (denote a) (denote b) := by
  have h := FunctionSemantics.call_graphValue _ _ _
    (formulaFn2Target A E B hB guard body hReturn).wd
    (FiniteFunction.pack2 (denote a) (denote b))
    ((FunctionSignature.twoTarget_domain A E B hB guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.twoTarget A E B hB guard).domain
    (FunctionSignature.twoTarget A E B hB guard).target (fun p => body
      (FiniteFunction.unpack2 p).1 (FiniteFunction.unpack2 p).2))
    (FiniteFunction.pack2 (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2Target, FiniteFunction.unpack_pack2] using h

theorem callFormula2Target_same {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E : StandardSetValue) (B : M.Value) (hB : M.isSet B)
    (guard : M.Value → M.Value → Prop) (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) B)
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b))
    (c : Obj (M := M) γ) (hBody : body (denote a) (denote b) = denote c) :
    Same (call2Target A E B hB guard (formulaFn2Target A E B hB guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) c :=
  (callFormula2Target_denote A E B hB guard body hReturn a b ha hb hg).trans hBody

theorem callFormula_denote {α : Type v} [Representation M α]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B))
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a)) :
    denote (call A B guard (formulaFn A B guard body hReturn) a
      (formulaFnInFnSet _) ha hg) = body (denote a) :=
  FunctionSemantics.call_graphValue _ _ _ (formulaFn A B guard body hReturn).wd _
    ((FunctionSignature.one_domain A B guard _).mpr ⟨ha, hg⟩)

/-- The source body's owned object supplies the correspondence to its template. -/
theorem callFormula_same {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A B : StandardSetValue) (guard : M.Value → Prop) (body : M.Value → M.Value)
    (hReturn : ∀ x, M.mem x (M.standard A) → guard x → M.mem (body x) (M.standard B))
    (a : Obj (M := M) α) (ha : In a (standardSet A)) (hg : guard (denote a))
    (b : Obj (M := M) β) (hBody : body (denote a) = denote b) :
    Same (call A B guard (formulaFn A B guard body hReturn) a
      (formulaFnInFnSet _) ha hg) b :=
  (callFormula_denote A B guard body hReturn a ha hg).trans hBody

theorem callFormula2_denote {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B))
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b)) :
    denote (call2 A E B guard (formulaFn2 A E B guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) = body (denote a) (denote b) := by
  have h := FunctionSemantics.call_graphValue _ _ _ (formulaFn2 A E B guard body hReturn).wd
    (FiniteFunction.pack2 (denote a) (denote b))
    ((FunctionSignature.two_domain A E B guard _ _).mpr ⟨ha, hb, hg⟩)
  change F.callValue (F.graphValue (FunctionSignature.two A E B guard).domain
    (FunctionSignature.two A E B guard).target (fun p => body (FiniteFunction.unpack2 p).1
      (FiniteFunction.unpack2 p).2))
    (FiniteFunction.pack2 (denote a) (denote b)) = body (denote a) (denote b)
  simpa only [formulaFn2, formulaFn2Target, FunctionSignature.two,
    FiniteFunction.unpack_pack2] using h

theorem callFormula2_same {α : Type v} {β : Type w} {γ : Type t}
    [Representation M α] [Representation M β] [Representation M γ]
    (A E B : StandardSetValue) (guard : M.Value → M.Value → Prop)
    (body : M.Value → M.Value → M.Value)
    (hReturn : ∀ x y, M.mem x (M.standard A) → M.mem y (M.standard E) →
      guard x y → M.mem (body x y) (M.standard B))
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a (standardSet A)) (hb : In b (standardSet E)) (hg : guard (denote a) (denote b))
    (c : Obj (M := M) γ) (hBody : body (denote a) (denote b) = denote c) :
    Same (call2 A E B guard (formulaFn2 A E B guard body hReturn) a b
      (formulaFnInFnSet _) ha hb hg) c :=
  (callFormula2_denote A E B guard body hReturn a b ha hb hg).trans hBody

end FunctionObjects

end Litex

namespace Litex

/-- An owned recursive declaration keeps both its source step interpretation
and the exact restricted guard used for recursive self calls. Its denotation
is a function graph; natural recursion is internal to that interpretation. -/
structure RecursiveNatFn (M : Semantics.{u}) where
  output : M.Value
  output_isSet : M.isSet output
  restrictedGuard : ℕ → M.Value → Prop
  baseValue : M.Value
  stepValue : ℕ → M.Value → M.Value

namespace RecursiveNatFn

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def signature (r : RecursiveNatFn M) : FunctionSignature M :=
  FunctionSignature.oneTarget .natural r.output r.output_isSet (fun _ => True)

def prefixSignature (r : RecursiveNatFn M) (n : ℕ) : FunctionSignature M :=
  FunctionSignature.oneTarget .natural r.output r.output_isSet (r.restrictedGuard n)

noncomputable def prefixGraph (r : RecursiveNatFn M) (n : ℕ) (values : ℕ → M.Value) :
    M.Value := F.graphValue (r.prefixSignature n).domain r.output
      (fun x => values (NativeBridge.naturalValue x))

/-- Every stage preserves its completed values. Values outside that stage are
extended with the certified base value, without exposing a native function as
an exported source object. -/
noncomputable def history (r : RecursiveNatFn M) : ℕ → ℕ → M.Value
  | 0 => fun _ => r.baseValue
  | n + 1 => fun k => if k = n + 1 then
      r.stepValue (n + 1) (r.prefixGraph (n + 1) (r.history n)) else r.history n k

noncomputable def value (r : RecursiveNatFn M) (n : ℕ) : M.Value := r.history n n

noncomputable def graph (r : RecursiveNatFn M) : M.Value :=
  F.graphValue r.signature.domain r.output (fun x => r.value (NativeBridge.naturalValue x))

/-- Each obligation is supplied by replaying the source declaration's retained
case guards, body WD, return proof, and recursive-call requirements. -/
structure Certified (r : RecursiveNatFn M) : Prop where
  guardSound : ∀ n x, M.mem x (M.standard .natural) → r.restrictedGuard n x →
    NativeBridge.naturalValue x < n
  baseReturn : M.mem r.baseValue r.output
  stepReturn : ∀ n prefixFn,
    M.mem prefixFn (F.fnSetValue (r.prefixSignature (n + 1)).domain r.output) →
      M.mem (r.stepValue (n + 1) prefixFn) r.output
  stepCongr : ∀ n f g,
    (∀ x, M.mem x (M.standard .natural) → r.restrictedGuard (n + 1) x →
      F.callValue f x = F.callValue g x) →
        r.stepValue (n + 1) f = r.stepValue (n + 1) g

theorem prefixGraph_mem (r : RecursiveNatFn M) (n : ℕ) (values : ℕ → M.Value)
    (hvalues : ∀ k, M.mem (values k) r.output) :
    M.mem (r.prefixGraph n values) (F.fnSetValue (r.prefixSignature n).domain r.output) :=
  FunctionSemantics.graph_inFnSet _ _ _ (fun x _ => hvalues (NativeBridge.naturalValue x))

theorem history_mem (r : RecursiveNatFn M) (h : r.Certified) (n k : ℕ) :
    M.mem (r.history n k) r.output := by
  induction n generalizing k with
  | zero => exact h.baseReturn
  | succ n ih =>
    change M.mem (if k = n + 1 then
      r.stepValue (n + 1) (r.prefixGraph (n + 1) (r.history n)) else r.history n k) r.output
    split
    · exact h.stepReturn n _ (r.prefixGraph_mem _ _ ih)
    · exact ih k

theorem history_completed (r : RecursiveNatFn M) (n k : ℕ) (hk : k ≤ n) :
    r.history n k = r.value k := by
  induction n with
  | zero =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    rfl
  | succ n ih =>
    by_cases he : k = n + 1
    · subst k
      rfl
    · have hkn : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hk he)
      change (if k = n + 1 then _ else r.history n k) = _
      rw [if_neg he]
      exact ih hkn

theorem graph_return (r : RecursiveNatFn M) (h : r.Certified) :
    ∀ x, M.mem x r.signature.domain →
      M.mem (r.value (NativeBridge.naturalValue x)) r.output :=
  fun _ _ => r.history_mem h _ _

theorem graph_mem (r : RecursiveNatFn M) (h : r.Certified) :
    M.mem r.graph (F.fnSetValue r.signature.domain r.output) :=
  FunctionSemantics.graph_inFnSet _ _ _ (r.graph_return h)

theorem call_graph (r : RecursiveNatFn M) (h : r.Certified)
    (x : M.Value) (hx : M.mem x (M.standard .natural)) :
    F.callValue r.graph x = r.value (NativeBridge.naturalValue x) :=
  FunctionSemantics.call_graphValue _ _ _ (r.graph_return h) x
    ((FunctionSignature.oneTarget_domain .natural r.output r.output_isSet
      (fun _ => True) x).mpr ⟨hx, True.intro⟩)

theorem prefix_call_agrees (r : RecursiveNatFn M) (h : r.Certified) (n : ℕ)
    (x : M.Value) (hx : M.mem x (M.standard .natural))
    (hg : r.restrictedGuard (n + 1) x) :
    F.callValue (r.prefixGraph (n + 1) (r.history n)) x = F.callValue r.graph x := by
  have hp := FunctionSemantics.call_graphValue (r.prefixSignature (n + 1)).domain
    r.output (fun x => r.history n (NativeBridge.naturalValue x))
    (fun x _ => r.history_mem h n (NativeBridge.naturalValue x)) x
    ((FunctionSignature.oneTarget_domain .natural r.output r.output_isSet
      (r.restrictedGuard (n + 1)) x).mpr ⟨hx, hg⟩)
  exact hp.trans ((r.history_completed n _ (Nat.le_of_lt_succ (h.guardSound _ _ hx hg))).trans
    (r.call_graph h x hx).symm)

theorem value_zero (r : RecursiveNatFn M) : r.value 0 = r.baseValue := rfl

theorem value_succ (r : RecursiveNatFn M) (h : r.Certified) (n : ℕ) :
    r.value (n + 1) = r.stepValue (n + 1) r.graph := by
  change (if n + 1 = n + 1 then _ else _) = _
  rw [if_pos rfl]
  exact h.stepCongr n _ _ (fun x hx hg => r.prefix_call_agrees h n x hx hg)

end RecursiveNatFn

noncomputable instance recursiveNatFnRepresentation {M : Semantics.{u}}
    [F : FunctionSemantics M] : Representation M (RecursiveNatFn M) where
  wd r := r.Certified
  denote r := r.graph
  wd_isSet {r} h := M.member_isSet (r.graph_mem h)

noncomputable def recursiveNatFnTarget {M : Semantics.{u}} [F : FunctionSemantics M]
    (B : M.Value) (hB : M.isSet B) (guard : ℕ → M.Value → Prop)
    (base : M.Value) (step : ℕ → M.Value → M.Value)
    (hGuard : ∀ n x, M.mem x (M.standard .natural) → guard n x →
      NativeBridge.naturalValue x < n)
    (hBase : M.mem base B)
    (hStep : ∀ n prefixFn,
      M.mem prefixFn (F.fnSetValue (FunctionSignature.oneTarget .natural B hB
        (guard (n + 1))).domain B) → M.mem (step (n + 1) prefixFn) B)
    (hCongr : ∀ n f g,
      (∀ x, M.mem x (M.standard .natural) → guard (n + 1) x →
        F.callValue f x = F.callValue g x) → step (n + 1) f = step (n + 1) g) :
    Obj (M := M) (RecursiveNatFn M) :=
  ⟨⟨B, hB, guard, base, step⟩, ⟨hGuard, hBase, hStep, hCongr⟩⟩

theorem recursiveNatFnInFnSet {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) : In f (fnSet f.val.signature) :=
  f.val.graph_mem f.wd

theorem recursiveNatFn_zero {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) :
    F.callValue (denote f) (M.number 0) = f.val.baseValue := by
  have hx : M.mem (M.number 0) (M.standard .natural) :=
    (M.natural_members _).mpr ⟨0, by simp only [Nat.cast_zero]⟩
  have h := f.val.call_graph f.wd (M.number 0) hx
  have hn : NativeBridge.naturalValue (M.number 0) = 0 := by
    simpa only [Nat.cast_zero] using NativeBridge.naturalValue_number (M := M) 0
  change F.callValue (denote f) (M.number 0) = f.val.value _ at h
  simpa only [hn, RecursiveNatFn.value_zero] using h

theorem recursiveNatFn_succ {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : Obj (M := M) (RecursiveNatFn M)) (n : ℕ) :
    F.callValue (denote f) (M.number ((n + 1 : ℕ) : ℂ)) =
      f.val.stepValue (n + 1) (denote f) := by
  have hx : M.mem (M.number ((n + 1 : ℕ) : ℂ)) (M.standard .natural) :=
    (M.natural_members _).mpr ⟨n + 1, rfl⟩
  exact (f.val.call_graph f.wd _ hx).trans
    (by rw [NativeBridge.naturalValue_number]; exact f.val.value_succ f.wd n)

theorem callRecursiveNat_denote {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α]
    (f : Obj (M := M) (RecursiveNatFn M)) (a : Obj (M := M) α) (ha : In a N) :
    denote (callTarget .natural f.val.output f.val.output_isSet (fun _ => True)
      f a (recursiveNatFnInFnSet f) ha True.intro) =
      f.val.value (NativeBridge.asNat a ha) :=
  f.val.call_graph f.wd (denote a) ha


theorem functionSpaceNonemptyOfCodomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (s : FunctionSignature M) (h : ∃ y : M.Value, M.mem y s.target) :
    IsNonempty (fnSet s) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨F.graphValue s.domain s.target (fun _ => y),
    FunctionSemantics.graph_inFnSet s.domain s.target (fun _ => y) (fun _ _ => hy)⟩

theorem functionSpaceNonemptyOfEmptyDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    (s : FunctionSignature M) (h : ∀ x, ¬ M.mem x s.domain) :
    IsNonempty (fnSet s) := by
  refine ⟨F.graphValue s.domain s.target (fun _ => M.number 0), ?_⟩
  exact FunctionSemantics.graph_inFnSet s.domain s.target (fun _ => M.number 0)
    (fun x hx => (h x hx).elim)


theorem functionGraphNonemptyOfDomain {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α)
    (s : FunctionSignature M) (hf : In f (fnSet s))
    (hd : ∃ x : M.Value, M.mem x s.domain) : IsNonempty f := by
  obtain ⟨x, hx⟩ := hd
  refine ⟨F.pairValue x (F.callValue (denote f) x), ?_⟩
  exact F.call_graph s.domain s.target (denote f) x
    ((F.fnSet_members s.domain s.target (denote f)).mp hf) hx


namespace FiniteFunction

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def orderedUnionValue (As : List M.Value) : M.Value :=
  match As with
  | [] => F.emptyValue
  | A :: As => As.foldl F.unionValue A

theorem foldUnion_members (As : List M.Value) (A x : M.Value) :
    M.mem x (As.foldl F.unionValue A) ↔ M.mem x A ∨ ∃ B ∈ As, M.mem x B := by
  induction As generalizing A with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | cons B Bs ih =>
    rw [List.foldl_cons, ih, F.union_members]
    simp only [List.mem_cons]
    aesop

theorem orderedUnionValue_members (As : List M.Value) (x : M.Value) :
    M.mem x (orderedUnionValue As) ↔ ∃ A ∈ As, M.mem x A := by
  cases As with
  | nil => simp only [orderedUnionValue, List.not_mem_nil, false_and, exists_false]
           exact ⟨fun h => (F.empty_members x) h, False.elim⟩
  | cons A As =>
    rw [orderedUnionValue, foldUnion_members]
    simp only [List.mem_cons]
    aesop

theorem foldUnion_isSet (As : List M.Value) (A : M.Value) (hA : M.isSet A)
    (hAs : ∀ B ∈ As, M.isSet B) : M.isSet (As.foldl F.unionValue A) := by
  induction As generalizing A with
  | nil => exact hA
  | cons B Bs ih =>
    exact ih (F.unionValue A B) (F.union_isSet A B hA (hAs B List.mem_cons_self))
      (fun C hC => hAs C (List.mem_cons_of_mem B hC))

theorem orderedUnionValue_isSet (As : List M.Value) (hAs : ∀ A ∈ As, M.isSet A) :
    M.isSet (orderedUnionValue As) := by
  cases As with
  | nil => exact F.empty_isSet
  | cons A As =>
    exact foldUnion_isSet As A (hAs A List.mem_cons_self)
      (fun B hB => hAs B (List.mem_cons_of_mem A hB))

end FiniteFunction

section FiniteCompleteDomain

variable {M : Semantics.{u}} [F : FunctionSemantics M]

def cartCompleteSignature {n : ℕ} (A : Obj (M := M) (CartObj M n)) : FunctionSignature M :=
  FunctionSignature.ofDomain (finiteSeqDomain (number (n : ℂ)))
    (FiniteFunction.orderedUnionValue (List.ofFn A.val.factors)) (finiteSeqDomain_isSet _)
    (FiniteFunction.orderedUnionValue_isSet _ (by
      intro B hB
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
      exact A.wd i))

theorem cartMemberInCompleteSignature {α : Type v} [Representation M α] {n : ℕ}
    (f : Obj (M := M) α) (A : Obj (M := M) (CartObj M n)) (hf : In f A) :
    In f (fnSet (cartCompleteSignature A)) := by
  have hAs : ∀ B ∈ List.ofFn A.val.factors, M.isSet B := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact A.wd i
  have outputs : FiniteFunction.finiteUnionValue (List.ofFn A.val.factors) =
      FiniteFunction.orderedUnionValue (List.ofFn A.val.factors) := by
    apply F.ext _ _ (FiniteFunction.finiteUnion_isSet _ hAs) (FiniteFunction.orderedUnionValue_isSet _ hAs)
    intro x
    exact (FiniteFunction.finiteUnion_members _ x).trans (FiniteFunction.orderedUnionValue_members _ x).symm
  change M.mem (denote f) (F.fnSetValue (finiteSeqDomain (number (n : ℂ)))
    (FiniteFunction.orderedUnionValue (List.ofFn A.val.factors)))
  rw [finiteSeqDomain_number, ← outputs]
  exact (F.fnSet_members _ _ _).mpr ((FiniteFunction.cart_members A.val.factors (denote f)).mp hf).1

end FiniteCompleteDomain

end Litex

