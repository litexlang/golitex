import Litex.ElementaryFunctions

universe u v w x

namespace Litex

/-- Source proper inclusion uses semantic inequality, not host inequality. -/
def Superset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset B A

def ProperSubset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset A B ∧ ¬ Same A B

def ProperSuperset {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) : Prop := Subset B A ∧ ¬ Same A B

/-- Numeric predicate meanings depend only on semantic denotation. -/
def PrimeValue (M : Semantics.{u}) (a : M.Value) : Prop :=
  ∃ n : ℕ, a = M.number (n : ℂ) ∧ Nat.Prime n

def CoprimeValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ m n : ℕ, a = M.number (m : ℂ) ∧ b = M.number (n : ℂ) ∧ Nat.Coprime m n

/-- Litex puts the dividend first and requires a nonzero integer divisor. -/
def DvdValue (M : Semantics.{u}) (a b : M.Value) : Prop :=
  ∃ m n : ℤ, a = M.number (m : ℂ) ∧ b = M.number (n : ℂ) ∧ n ≠ 0 ∧ n ∣ m

def Prime {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) : Prop := PrimeValue M (denote a)

def Coprime {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop := CoprimeValue M (denote a) (denote b)

def Dvd {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) : Prop := DvdValue M (denote a) (denote b)

theorem prime_iff_of_denote {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (n : ℕ) (ha : denote a = M.number (n : ℂ)) :
    Prime a ↔ Nat.Prime n := by
  constructor
  · rintro ⟨m, hm, hp⟩
    have h : m = n := by exact_mod_cast M.number_injective (hm.symm.trans ha)
    exact h ▸ hp
  · intro hp
    exact ⟨n, ha, hp⟩

theorem coprime_iff_of_denote {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m n : ℕ)
    (ha : denote a = M.number (m : ℂ)) (hb : denote b = M.number (n : ℂ)) :
    Coprime a b ↔ Nat.Coprime m n := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    have h₁ : i = m := by exact_mod_cast M.number_injective (hi.symm.trans ha)
    have h₂ : j = n := by exact_mod_cast M.number_injective (hj.symm.trans hb)
    exact h₁ ▸ h₂ ▸ h
  · intro h
    exact ⟨m, n, ha, hb, h⟩

theorem dvd_iff_of_denote {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (m n : ℤ)
    (ha : denote a = M.number (m : ℂ)) (hb : denote b = M.number (n : ℂ)) :
    Dvd a b ↔ n ≠ 0 ∧ n ∣ m := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    have h₁ : i = m := by exact_mod_cast M.number_injective (hi.symm.trans ha)
    have h₂ : j = n := by exact_mod_cast M.number_injective (hj.symm.trans hb)
    exact h₁ ▸ h₂ ▸ h
  · rintro ⟨hn, h⟩
    exact ⟨m, n, ha, hb, hn, h⟩

theorem emptyNotNonempty {M : Semantics.{u}} [S : SetSemantics M] :
    ¬ IsNonempty (emptySet (M := M)) := by
  rintro ⟨x, hx⟩
  exact S.empty_members x hx

end Litex

namespace Litex

theorem dvdOfModZero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ModObj (M := M) α β)) (h : Same p (number 0)) :
    Dvd p.val.left p.val.right := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  have hb0 : b ≠ 0 := by
    intro hzero
    apply p.wd.2.2
    change denote p.val.right = M.number 0
    simpa only [hzero, Int.cast_zero] using hb
  have hmod : a % b = 0 := by
    have he : ((a % b : ℤ) : ℂ) = 0 := M.number_injective ((modDenoteInt p a b ha hb).symm.trans h)
    exact_mod_cast he
  exact ⟨a, b, ha, hb, hb0, Int.dvd_of_emod_eq_zero hmod⟩

end Litex

namespace Litex

theorem naturalNotFinite {M : Semantics.{u}} : ¬ IsFiniteSet (N (M := M)) := by
  have hi : Function.Injective (fun n : ℕ => M.number (n : ℂ)) := by
    intro a b h
    exact_mod_cast M.number_injective h
  intro h
  apply Set.infinite_range_of_injective hi
  exact h.subset (by
    rintro _ ⟨n, rfl⟩
    exact (M.natural_members _).mpr ⟨n, rfl⟩)

end Litex

namespace Litex

structure SymmetricDifferenceObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

def symmetricDifferenceValue {M : Semantics.{u}} [S : SetSemantics M]
    (A B : M.Value) : M.Value :=
  S.unionValue (S.sepValue A (fun x => ¬ M.mem x B))
    (S.sepValue B (fun x => ¬ M.mem x A))

instance symmetricDifferenceRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (SymmetricDifferenceObj (M := M) α β) where
  wd _ := True
  denote p := symmetricDifferenceValue (denote p.left) (denote p.right)
  wd_isSet {p} _ := S.union_isSet _ _
    (S.sep_isSet _ _ (isSet p.left)) (S.sep_isSet _ _ (isSet p.right))

def symmetricDifference {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Obj (M := M) (SymmetricDifferenceObj (M := M) α β) := ⟨⟨A, B⟩, True.intro⟩

theorem symmetricDifference_members {M : Semantics.{u}} [S : SetSemantics M]
    (A B x : M.Value) : M.mem x (symmetricDifferenceValue A B) ↔
      (M.mem x A ∧ ¬ M.mem x B) ∨ (¬ M.mem x A ∧ M.mem x B) := by
  simp only [symmetricDifferenceValue, S.union_members, S.sep_members]
  exact or_congr Iff.rfl and_comm

theorem inSymmetricDifferenceLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : In a p.val.left) (hb : ¬ In a p.val.right) : In a p :=
  (symmetricDifference_members _ _ _).mpr (Or.inl ⟨ha, hb⟩)

theorem inSymmetricDifferenceRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : ¬ In a p.val.left) (hb : In a p.val.right) : In a p :=
  (symmetricDifference_members _ _ _).mpr (Or.inr ⟨ha, hb⟩)

theorem notInSymmetricDifferenceBoth {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : In a p.val.left) (hb : In a p.val.right) : ¬ In a p := by
  intro h
  rcases (symmetricDifference_members _ _ _).mp h with h | h
  · exact h.2 hb
  · exact h.1 ha

theorem notInSymmetricDifferenceNeither {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SymmetricDifferenceObj (M := M) β γ))
    (ha : ¬ In a p.val.left) (hb : ¬ In a p.val.right) : ¬ In a p := by
  intro h
  rcases (symmetricDifference_members _ _ _).mp h with h | h
  · exact ha h.1
  · exact hb h.2

theorem symmetricDifferenceDefinition {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (symmetricDifference A B) (union (setMinus A B) (setMinus B A)) := rfl

theorem symmetricDifferenceSelf {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Same (symmetricDifference A A) emptySet := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (symmetricDifferenceValue (denote A) (denote A)) ↔ M.mem x S.emptyValue
  rw [symmetricDifference_members]
  simp only [and_not_self, not_and_self, or_self, S.empty_members, iff_self]

end Litex

namespace Litex

section IndexedSets
variable {M : Semantics.{u}} [F : FunctionSemantics M]
variable {α : Type v} {β : Type w} {γ : Type x}
variable [Representation M α] [Representation M β] [Representation M γ]

def indexFamilySignature (I : Obj (M := M) α) (X : Obj (M := M) β) :
    FunctionSignature M :=
  FunctionSignature.withGuard (denote I) (denote X) (isSet I) (isSet X) (fun _ => True)

def indexedFamilyWD (I : Obj (M := M) α) (X : Obj (M := M) β)
    (A : Obj (M := M) γ) : Prop :=
  IsNonempty I ∧ IsSet I ∧ IsSet X ∧ In A (fnSet (indexFamilySignature I (powerSet X)))

def indexUnionValue (I X A : M.Value) : M.Value :=
  F.sepValue X (fun a => ∃ i, M.mem i I ∧ M.mem a (F.callValue A i))

def indexIntersectValue (I X A : M.Value) : M.Value :=
  F.sepValue X (fun a => ∀ i, M.mem i I → M.mem a (F.callValue A i))

structure IndexUnionObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  ambient : Obj (M := M) β
  family : Obj (M := M) γ

instance indexUnionRepresentation : Representation M (IndexUnionObj M α β γ) where
  wd p := indexedFamilyWD p.index p.ambient p.family
  denote p := indexUnionValue (denote p.index) (denote p.ambient) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (isSet p.ambient)

def indexUnion (I : Obj (M := M) α) (X : Obj (M := M) β) (A : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hX : IsSet X)
    (hA : In A (fnSet (indexFamilySignature I (powerSet X)))) :
    Obj (M := M) (IndexUnionObj M α β γ) := ⟨⟨I, X, A⟩, hI, hIs, hX, hA⟩

structure IndexIntersectObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  ambient : Obj (M := M) β
  family : Obj (M := M) γ

instance indexIntersectRepresentation : Representation M (IndexIntersectObj M α β γ) where
  wd p := indexedFamilyWD p.index p.ambient p.family
  denote p := indexIntersectValue (denote p.index) (denote p.ambient) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (isSet p.ambient)

def indexIntersect (I : Obj (M := M) α) (X : Obj (M := M) β) (A : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hX : IsSet X)
    (hA : In A (fnSet (indexFamilySignature I (powerSet X)))) :
    Obj (M := M) (IndexIntersectObj M α β γ) := ⟨⟨I, X, A⟩, hI, hIs, hX, hA⟩

theorem indexUnionMember {δ : Type t} {ε : Type*}
    [Representation M δ] [Representation M ε]
    (p : Obj (M := M) (IndexUnionObj M α β γ))
    (i : Obj (M := M) δ) (a : Obj (M := M) ε)
    (hi : In i p.val.index)
    (ha : M.mem (denote a) (F.callValue (denote p.val.family) (denote i))) : In a p := by
  have hdom : M.mem (denote i) (indexFamilySignature p.val.index (powerSet p.val.ambient)).domain :=
    (F.sep_members _ _ _).mpr ⟨hi, True.intro⟩
  have hfiber := F.call_mem _ _ _ _ p.wd.2.2.2 hdom
  have hx : In a p.val.ambient := ((F.power_members _ _).mp hfiber).2 _ ha
  exact (F.sep_members _ _ _).mpr ⟨hx, denote i, hi, ha⟩

theorem indexIntersectMember {δ : Type t} [Representation M δ]
    (p : Obj (M := M) (IndexIntersectObj M α β γ)) (a : Obj (M := M) δ)
    (ha : In a p.val.ambient)
    (hall : ∀ i, M.mem i (denote p.val.index) →
      M.mem (denote a) (F.callValue (denote p.val.family) i)) : In a p :=
  (F.sep_members _ _ _).mpr ⟨ha, hall⟩

def indexCartValue [IU : IndexedUnionSemantics M] (I S g : M.Value) : M.Value :=
  F.sepValue (F.fnSetValue (F.sepValue I (fun _ => True)) (IU.indexedUnionValue S id))
    (fun f => ∀ i, M.mem i I → M.mem (F.callValue f i) (F.callValue g i))

structure IndexCartObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    [Representation M α] [Representation M β] [Representation M γ] where
  index : Obj (M := M) α
  familySet : Obj (M := M) β
  family : Obj (M := M) γ

instance indexCartRepresentation [IU : IndexedUnionSemantics M] :
    Representation M (IndexCartObj M α β γ) where
  wd p := IsNonempty p.index ∧ IsSet p.index ∧ IsNonempty p.familySet ∧
    In p.family (fnSet (indexFamilySignature p.index p.familySet))
  denote p := indexCartValue (denote p.index) (denote p.familySet) (denote p.family)
  wd_isSet {p} _ := F.sep_isSet _ _ (F.fnSet_isSet _ _
    (F.sep_isSet _ _ (isSet p.index))
    (IU.indexedUnion_isSet _ _ (isSet p.familySet) (fun _ h => M.member_isSet h)))

def indexCart [IndexedUnionSemantics M]
    (I : Obj (M := M) α) (S : Obj (M := M) β) (g : Obj (M := M) γ)
    (hI : IsNonempty I) (hIs : IsSet I) (hS : IsNonempty S)
    (hg : In g (fnSet (indexFamilySignature I S))) :
    Obj (M := M) (IndexCartObj M α β γ) := ⟨⟨I, S, g⟩, hI, hIs, hS, hg⟩

theorem indexCartMember [IndexedUnionSemantics M]
    {δ : Type t} [Representation M δ]
    (p : Obj (M := M) (IndexCartObj M α β γ)) (f : Obj (M := M) δ)
    (hf : In f (fnSet (indexFamilySignature p.val.index (familyUnion p.val.familySet))))
    (hg : IsChoiceFunctionFor p.val.index p.val.familySet p.val.family f) : In f p :=
  (F.sep_members _ _ _).mpr ⟨hf, hg⟩

end IndexedSets
end Litex

namespace Litex

/-- A source forall ranges over all representations. A one-point carrier can
represent any fixed semantic value, even in a smaller host universe. -/
theorem forallMembersOfRepresentations {M : Semantics.{u}} {α : Type v}
    [Representation M α] {P : M.Value → Prop} (A : Obj (M := M) α)
    (h : ∀ {β : Type w} [Representation M β], (x : Obj (M := M) β) →
      In x A → P (denote x)) : ∀ x, M.mem x (denote A) → P x := by
  intro x hx
  letI : Representation M PUnit.{w+1} := {
    wd := fun _ => True
    denote := fun _ => x
    wd_isSet := fun _ => M.member_isSet hx }
  exact h (⟨PUnit.unit, True.intro⟩ : Obj (M := M) PUnit.{w+1}) hx

structure FamilyIntersectObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  family : Obj (M := M) α

def familyIntersectValue {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] (F : M.Value) : M.Value :=
  S.sepValue (I.indexedUnionValue F id) (fun x => ∀ A, M.mem A F → M.mem x A)

instance familyIntersectRepresentation {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] {α : Type v} [Representation M α] :
    Representation M (FamilyIntersectObj (M := M) α) where
  wd p := IsNonempty p.family
  denote p := familyIntersectValue (denote p.family)
  wd_isSet {p} _ := S.sep_isSet _ _ (I.indexedUnion_isSet _ _ (isSet p.family)
    (fun _ h => M.member_isSet h))

def familyIntersect {M : Semantics.{u}} [SetSemantics M] [IndexedUnionSemantics M]
    {α : Type v} [Representation M α] (F : Obj (M := M) α) (h : IsNonempty F) :
    Obj (M := M) (FamilyIntersectObj (M := M) α) := ⟨⟨F⟩, h⟩

theorem familyIntersect_members {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (FamilyIntersectObj (M := M) α)) (x : M.Value) :
    M.mem x (denote p) ↔ ∀ A, M.mem A (denote p.val.family) → M.mem x A := by
  change M.mem x (S.sepValue _ _) ↔ _
  rw [S.sep_members]
  constructor
  · exact And.right
  · intro h
    obtain ⟨A, hA⟩ := p.wd
    exact ⟨(I.indexedUnion_members _ _ _).mpr ⟨A, hA, h A hA⟩, h⟩

theorem familyIntersectMember {M : Semantics.{u}} [SetSemantics M]
    [IndexedUnionSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FamilyIntersectObj (M := M) α)) (x : Obj (M := M) β)
    (h : ∀ A, M.mem A (denote p.val.family) → M.mem (denote x) A) : In x p :=
  (familyIntersect_members p (denote x)).mpr h

end Litex

-- Ordered and finite folds retain their checked functions and domains.
universe r
namespace Litex
section FoldSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def foldApply2 (operation a b : M.Value) : M.Value :=
  F.callValue operation (FiniteFunction.pack2 a b)

noncomputable def foldValue (items : List M.Value) (f operation seed : M.Value) : M.Value :=
  items.foldl (fun acc i => foldApply2 operation acc (F.callValue f i)) seed

noncomputable def homogeneousFoldSignature (E : M.Value) (hE : M.isSet E) :
    FunctionSignature M :=
  FunctionSignature.withGuard (FiniteFunction.cartValue ![E, E]) E
    (FiniteFunction.cart_isSet _ (by intro i; fin_cases i <;> exact hE)) hE (fun _ => True)

theorem homogeneousFoldSignature_member (E : M.Value) (hE : M.isSet E)
    (a b : M.Value) (ha : M.mem a E) (hb : M.mem b E) :
    M.mem (FiniteFunction.pack2 a b) (homogeneousFoldSignature E hE).domain :=
  (F.sep_members _ _ _).mpr ⟨(FiniteFunction.cart2_members _ _ _).mpr
    ⟨a, ha, b, hb, rfl⟩, True.intro⟩

theorem foldApply2_mem (s : FunctionSignature M) (operation a b : M.Value)
    (hop : M.mem operation (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (ha : M.mem a s.output) (hb : M.mem b s.output) :
    M.mem (foldApply2 operation a b) s.output :=
  F.call_mem _ _ _ _ hop (homogeneousFoldSignature_member _ _ _ _ ha hb)

theorem foldValue_mem (s : FunctionSignature M) (items : List M.Value) (f operation seed : M.Value)
    (hf : M.mem f (F.fnSetValue s.domain s.output))
    (hop : M.mem operation (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (hseed : M.mem seed s.output)
    (hitems : ∀ i ∈ items, M.mem i s.domain) : M.mem (foldValue items f operation seed) s.output := by
  induction items generalizing seed with
  | nil => exact hseed
  | cons i rest ih =>
    apply ih
    · exact foldApply2_mem s operation seed (F.callValue f i) hop hseed
        (F.call_mem _ _ _ _ hf (hitems i (List.mem_cons_self)))
    · intro j hj
      exact hitems j (List.mem_cons_of_mem i hj)

def integerFoldIndices (first last : ℤ) : List ℤ :=
  (List.range (last - first + 1).toNat).map (fun (n : ℕ) => first + (n : ℤ))

theorem integerFoldIndices_mem (first last k : ℤ) :
    k ∈ integerFoldIndices first last ↔ first ≤ k ∧ k ≤ last := by
  simp only [integerFoldIndices, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    refine ⟨(k - first).toNat, ?_, ?_⟩ <;> omega

noncomputable def rangeFoldValue (first last f operation seed : M.Value) : M.Value :=
  foldValue ((integerFoldIndices (NativeBridge.integerValue first)
    (NativeBridge.integerValue last)).map (fun (k : ℤ) => M.number (k : ℂ))) f operation seed

structure RangeFoldObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    (δ : Type t) (ε : Type r) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] [Representation M ε] where
  first : Obj (M := M) α
  last : Obj (M := M) β
  function : Obj (M := M) γ
  operation : Obj (M := M) δ
  seed : Obj (M := M) ε
  signature : FunctionSignature M

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

def rangeFoldWD (p : RangeFoldObj M α β γ δ ε) : Prop :=
  In p.first Z ∧ In p.last Z ∧ In p.function (fnSet p.signature) ∧
  In p.operation (fnSet (homogeneousFoldSignature p.signature.output p.signature.output_isSet)) ∧
  M.mem (denote p.seed) p.signature.output ∧
  ∀ k : ℤ, NativeBridge.integerValue (denote p.first) ≤ k →
    k ≤ NativeBridge.integerValue (denote p.last) → M.mem (M.number (k : ℂ)) p.signature.domain

theorem rangeFoldValue_mem (p : RangeFoldObj M α β γ δ ε) (h : rangeFoldWD p) :
    M.mem (rangeFoldValue (denote p.first) (denote p.last) (denote p.function)
      (denote p.operation) (denote p.seed)) p.signature.output := by
  apply foldValue_mem p.signature _ _ _ _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
  intro i hi
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
  obtain ⟨hl, hr⟩ := (integerFoldIndices_mem _ _ _).mp hk
  exact h.2.2.2.2.2 k hl hr

noncomputable instance rangeFoldRepresentation : Representation M (RangeFoldObj M α β γ δ ε) where
  wd := rangeFoldWD
  denote p := rangeFoldValue (denote p.first) (denote p.last) (denote p.function)
    (denote p.operation) (denote p.seed)
  wd_isSet {p} h := M.member_isSet (rangeFoldValue_mem p h)

noncomputable def rangeFold (first : Obj (M := M) α) (last : Obj (M := M) β)
    (f : Obj (M := M) γ) (operation : Obj (M := M) δ) (seed : Obj (M := M) ε)
    (s : FunctionSignature M) (hfirst : In first Z) (hlast : In last Z)
    (hf : In f (fnSet s)) (hop : In operation (fnSet (homogeneousFoldSignature s.output s.output_isSet)))
    (hseed : M.mem (denote seed) s.output)
    (hindices : ∀ k : ℤ, NativeBridge.integerValue (denote first) ≤ k →
      k ≤ NativeBridge.integerValue (denote last) → M.mem (M.number (k : ℂ)) s.domain) :
    Obj (M := M) (RangeFoldObj M α β γ δ ε) :=
  ⟨⟨first, last, f, operation, seed, s⟩, hfirst, hlast, hf, hop, hseed, hindices⟩

theorem rangeFoldInOutput (p : Obj (M := M) (RangeFoldObj M α β γ δ ε)) :
    M.mem (denote p) p.val.signature.output := rangeFoldValue_mem p.val p.wd

theorem rangeFoldEmpty (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : NativeBridge.integerValue (denote p.val.last) < NativeBridge.integerValue (denote p.val.first)) :
    Same p p.val.seed := by
  change foldValue _ _ _ _ = _
  have hz : (NativeBridge.integerValue (denote p.val.last) -
    NativeBridge.integerValue (denote p.val.first) + 1).toNat = 0 := by omega
  simp only [integerFoldIndices, hz, List.range_zero, List.map_nil, foldValue, List.foldl_nil]
theorem rangeFoldEmptyOfLt (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : Lt p.val.last p.val.first) : Same p p.val.seed := by
  apply rangeFoldEmpty p
  have ha : denote p.val.last = M.number ((NativeBridge.integerValue (denote p.val.last) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.2.1
  have hb : denote p.val.first = M.number ((NativeBridge.integerValue (denote p.val.first) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.1
  have hl := (NativeBridge.lt_iff_ofDenoteReal p.val.last p.val.first _ _ ha hb).mp h
  exact_mod_cast hl

end FoldSemantics
end Litex

namespace Litex
section FiniteFoldSemantics
variable {M : Semantics.{u}} [F : FunctionSemantics M]

noncomputable def foldEnumeration (A : M.Value) : List M.Value := by
  classical
  exact if h : (memberSet A).Finite then h.toFinset.toList else []

omit F in
theorem foldEnumeration_mem (A x : M.Value) (h : (memberSet A).Finite) :
    x ∈ foldEnumeration A ↔ M.mem x A := by
  classical
  unfold foldEnumeration
  split_ifs
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset]
  rfl

noncomputable def finiteFoldValue (A f operation seed : M.Value) : M.Value :=
  foldValue (foldEnumeration A) f operation seed

def foldCommutative (E operation : M.Value) : Prop :=
  ∀ a, M.mem a E → ∀ b, M.mem b E → foldApply2 operation a b = foldApply2 operation b a

def foldAssociative (E operation : M.Value) : Prop :=
  ∀ a, M.mem a E → ∀ b, M.mem b E → ∀ c, M.mem c E →
    foldApply2 operation (foldApply2 operation a b) c =
      foldApply2 operation a (foldApply2 operation b c)

structure FiniteFoldObj (M : Semantics.{u}) (α : Type v) (β : Type w) (γ : Type x)
    (δ : Type t) [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ] where
  set : Obj (M := M) α
  function : Obj (M := M) β
  operation : Obj (M := M) γ
  seed : Obj (M := M) δ
  signature : FunctionSignature M

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t}
variable [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]

def finiteFoldWD (p : FiniteFoldObj M α β γ δ) : Prop :=
  IsFiniteSet p.set ∧ In p.function (fnSet p.signature) ∧
  In p.operation (fnSet (homogeneousFoldSignature p.signature.output p.signature.output_isSet)) ∧
  M.mem (denote p.seed) p.signature.output ∧
  (∀ i, M.mem i (denote p.set) → M.mem i p.signature.domain) ∧
  foldCommutative p.signature.output (denote p.operation) ∧
  foldAssociative p.signature.output (denote p.operation)

theorem finiteFoldValue_mem (p : FiniteFoldObj M α β γ δ) (h : finiteFoldWD p) :
    M.mem (finiteFoldValue (denote p.set) (denote p.function)
      (denote p.operation) (denote p.seed)) p.signature.output := by
  apply foldValue_mem p.signature _ _ _ _ h.2.1 h.2.2.1 h.2.2.2.1
  intro i hi
  exact h.2.2.2.2.1 i ((foldEnumeration_mem _ _ h.1).mp hi)

noncomputable instance finiteFoldRepresentation : Representation M (FiniteFoldObj M α β γ δ) where
  wd := finiteFoldWD
  denote p := finiteFoldValue (denote p.set) (denote p.function) (denote p.operation) (denote p.seed)
  wd_isSet {p} h := M.member_isSet (finiteFoldValue_mem p h)

noncomputable def finiteFold (A : Obj (M := M) α) (f : Obj (M := M) β)
    (operation : Obj (M := M) γ) (seed : Obj (M := M) δ) (s : FunctionSignature M)
    (hfinite : IsFiniteSet A) (hf : In f (fnSet s))
    (hop : In operation (fnSet (homogeneousFoldSignature s.output s.output_isSet)))
    (hseed : M.mem (denote seed) s.output)
    (hcover : ∀ i, M.mem i (denote A) → M.mem i s.domain)
    (hcomm : foldCommutative s.output (denote operation))
    (hassoc : foldAssociative s.output (denote operation)) :
    Obj (M := M) (FiniteFoldObj M α β γ δ) :=
  ⟨⟨A, f, operation, seed, s⟩, hfinite, hf, hop, hseed, hcover, hcomm, hassoc⟩

theorem finiteFoldInOutput (p : Obj (M := M) (FiniteFoldObj M α β γ δ)) :
    M.mem (denote p) p.val.signature.output := finiteFoldValue_mem p.val p.wd

omit F in
theorem foldEnumeration_empty (A : M.Value) (h : ∀ x, ¬ M.mem x A) :
    foldEnumeration A = [] := by
  classical
  unfold foldEnumeration
  split_ifs with hf
  · have hz : hf.toFinset = ∅ := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
      exact h x
    rw [hz]
    exact Finset.toList_empty
  · rfl

theorem finiteFoldEmpty (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (h : Same p.val.set emptySet) : Same p p.val.seed := by
  change foldValue (foldEnumeration (denote p.val.set)) _ _ _ = _
  have he : denote p.val.set = F.emptyValue := h
  rw [foldEnumeration_empty _ (fun x hx => (F.empty_members x) (he ▸ hx))]
  rfl

end FiniteFoldSemantics
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem foldValue_perm (s : FunctionSignature M) (f op : M.Value)
    (hf : M.mem f (F.fnSetValue s.domain s.output))
    (hop : M.mem op (F.fnSetValue (homogeneousFoldSignature s.output s.output_isSet).domain s.output))
    (comm : foldCommutative s.output op) (assoc : foldAssociative s.output op)
    {xs ys : List M.Value} (p : xs.Perm ys) (seed : M.Value) (hs : M.mem seed s.output)
    (hx : ∀ x ∈ xs, M.mem x s.domain) : foldValue xs f op seed = foldValue ys f op seed := by
  have exchange (seed a b : M.Value) (hs : M.mem seed s.output)
      (ha : M.mem a s.domain) (hb : M.mem b s.domain) :
      foldApply2 op (foldApply2 op seed (F.callValue f a)) (F.callValue f b) =
      foldApply2 op (foldApply2 op seed (F.callValue f b)) (F.callValue f a) := by
    have hfa := F.call_mem _ _ _ _ hf ha
    have hfb := F.call_mem _ _ _ _ hf hb
    rw [assoc seed hs _ hfa _ hfb, comm _ hfa _ hfb, ← assoc seed hs _ hfb _ hfa]
  induction p generalizing seed with
  | nil => rfl
  | cons a p ih =>
    apply ih
    · exact foldApply2_mem s op seed _ hop hs (F.call_mem _ _ _ _ hf (hx _ (by simp)))
    · intro x h
      exact hx x (List.mem_cons_of_mem a h)
  | swap a b xs =>
    change foldValue xs f op (foldApply2 op (foldApply2 op seed (F.callValue f b)) (F.callValue f a)) = _
    rw [exchange seed b a hs (hx b (by simp)) (hx a (by simp))]
    rfl
  | trans p q ihp ihq =>
    exact (ihp seed hs hx).trans (ihq seed hs (fun x h => hx x (p.mem_iff.mpr h)))

omit F in
theorem foldEnumeration_nodup (A : M.Value) : (foldEnumeration A).Nodup := by
  classical
  unfold foldEnumeration
  split_ifs
  · exact Finset.nodup_toList _
  · exact List.nodup_nil

omit F in
theorem foldEnumeration_singleton (A x : M.Value) (h : (memberSet A).Finite)
    (hm : ∀ y, M.mem y A ↔ y = x) : foldEnumeration A = [x] := by
  classical
  have hp : (foldEnumeration A).Perm [x] :=
    (List.perm_ext_iff_of_nodup (foldEnumeration_nodup A) (by simp)).mpr (fun y => by
      rw [foldEnumeration_mem _ _ h, List.mem_singleton]
      exact hm y)
  exact List.perm_singleton.mp hp

theorem integerFoldIndices_last (a b : ℤ) (h : a ≤ b) :
    integerFoldIndices a b = integerFoldIndices a (b - 1) ++ [b] := by
  have hn : (b-a+1).toNat = (b-a).toNat + 1 := by omega
  have hb : a + ((b-a).toNat : ℤ) = b := by omega
  unfold integerFoldIndices
  rw [hn, List.range_succ, List.map_append]
  simp only [List.map_singleton, hb]
  have he : b - 1 - a + 1 = b - a := by omega
  rw [he]

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

theorem rangeFoldDenote (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (a b : ℤ) (ha : denote p.val.first = M.number (a : ℂ))
    (hb : denote p.val.last = M.number (b : ℂ)) (value : M.Value)
    (h : foldValue ((integerFoldIndices a b).map (fun (k : ℤ) => M.number (k : ℂ)))
      (denote p.val.function) (denote p.val.operation) (denote p.val.seed) = value) :
    denote p = value := by
  change rangeFoldValue _ _ _ _ _ = _
  unfold rangeFoldValue
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  exact h

theorem finiteFoldEnumerate (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (xs : List M.Value) (hd : xs.Nodup)
    (hx : ∀ x, M.mem x (denote p.val.set) ↔ x ∈ xs) :
    denote p = foldValue xs (denote p.val.function) (denote p.val.operation) (denote p.val.seed) := by
  change foldValue (foldEnumeration _) _ _ _ = _
  have hp : (foldEnumeration (denote p.val.set)).Perm xs :=
    (List.perm_ext_iff_of_nodup (foldEnumeration_nodup _) hd).mpr (fun x =>
      (foldEnumeration_mem _ _ p.wd.1).trans (hx x))
  exact foldValue_perm p.val.signature _ _ p.wd.2.1 p.wd.2.2.1
    p.wd.2.2.2.2.2.1 p.wd.2.2.2.2.2.2 hp _ p.wd.2.2.2.1
    (fun x h => p.wd.2.2.2.2.1 x ((foldEnumeration_mem _ _ p.wd.1).mp h))

theorem finiteFoldSingleton (p : Obj (M := M) (FiniteFoldObj M α β γ δ))
    (x : M.Value) (hx : ∀ y, M.mem y (denote p.val.set) ↔ y = x) :
    denote p = foldApply2 (denote p.val.operation) (denote p.val.seed)
      (F.callValue (denote p.val.function) x) := by
  change foldValue (foldEnumeration _) _ _ _ = _
  rw [foldEnumeration_singleton _ _ p.wd.1 hx]
  rfl

end Litex

namespace Litex
variable {M : Semantics.{u}}
theorem integerValue_nonneg_of_natural {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a N) : 0 ≤ NativeBridge.integerValue (denote a) := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp ha
  have hc : (n : ℂ) = ((n : ℤ) : ℂ) := by simp
  rw [hn, hc, NativeBridge.integerValue_number]
  exact Int.natCast_nonneg n

theorem integerInNaturalAbove {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a N) (k : ℤ)
    (hk : NativeBridge.integerValue (denote a) ≤ k) :
    M.mem (M.number (k : ℂ)) (M.standard .natural) := by
  have hn : 0 ≤ k := le_trans (integerValue_nonneg_of_natural a ha) hk
  refine (M.natural_members _).mpr ⟨k.toNat, congrArg M.number ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hn).symm

theorem integerBoundsEmpty {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (i j : ℤ)
    (ha : Same a (number (i : ℂ))) (hb : Same b (number (j : ℂ))) (h : j < i) :
    ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → False := by
  change denote a = M.number (i : ℂ) at ha
  change denote b = M.number (j : ℂ) at hb
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  omega
end Litex

namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
theorem rangeFoldValue_last (a b f op seed : M.Value)
    (hb : M.mem b (M.standard .integer))
    (h : NativeBridge.integerValue a ≤ NativeBridge.integerValue b) :
    rangeFoldValue a b f op seed = foldApply2 op
      (rangeFoldValue a (M.subValue b (M.number 1)) f op seed) (F.callValue f b) := by
  have hbv := NativeBridge.integerValue_spec b hb
  have hsub : M.subValue b (M.number 1) = M.number ((NativeBridge.integerValue b - 1 : ℤ) : ℂ) := by
    conv_lhs => rw [hbv, M.sub_numbers]
    congr 1
    push_cast
    rfl
  have hp : NativeBridge.integerValue (M.subValue b (M.number 1)) = NativeBridge.integerValue b - 1 := by
    rw [hsub, NativeBridge.integerValue_number]
  unfold rangeFoldValue
  rw [hp, integerFoldIndices_last _ _ h, List.map_append]
  simp only [List.map_singleton, foldValue, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← hbv]

variable {α : Type v} {β : Type w} {γ : Type x} {δ : Type t} {ε : Type r}
variable [Representation M α] [Representation M β] [Representation M γ]
variable [Representation M δ] [Representation M ε]

theorem rangeFoldLast (p : Obj (M := M) (RangeFoldObj M α β γ δ ε))
    (h : Le p.val.first p.val.last) :
    denote p = foldApply2 (denote p.val.operation)
      (rangeFoldValue (denote p.val.first) (M.subValue (denote p.val.last) (M.number 1))
        (denote p.val.function) (denote p.val.operation) (denote p.val.seed))
      (F.callValue (denote p.val.function) (denote p.val.last)) := by
  apply rangeFoldValue_last _ _ _ _ _ p.wd.2.1
  have ha : denote p.val.first = M.number ((NativeBridge.integerValue (denote p.val.first) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.1
  have hb : denote p.val.last = M.number ((NativeBridge.integerValue (denote p.val.last) : ℝ) : ℂ) :=
    NativeBridge.integerValue_spec _ p.wd.2.1
  have hl := (NativeBridge.le_iff_ofDenoteReal p.val.first p.val.last _ _ ha hb).mp h
  exact_mod_cast hl
end Litex

namespace Litex
variable {M : Semantics.{u}}
theorem integerLowerBound {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a Z) (k : ℤ)
    (hk : NativeBridge.integerValue (denote a) ≤ k) : Le a (number (k : ℂ)) := by
  refine NativeBridge.leOfDenoteReal a (number (k : ℂ))
    (NativeBridge.integerValue (denote a) : ℝ) (k : ℝ)
    (NativeBridge.integerValue_spec _ ha) ?_ ?_
  · change M.number (k : ℂ) = M.number ((k : ℝ) : ℂ)
    simp only [Complex.ofReal_intCast]
  · exact_mod_cast hk

theorem integerUpperBound {α : Type v} [Representation M α]
    (b : Obj (M := M) α) (hb : In b Z) (k : ℤ)
    (hk : k ≤ NativeBridge.integerValue (denote b)) : Le (number (k : ℂ)) b := by
  refine NativeBridge.leOfDenoteReal (number (k : ℂ)) b
    (k : ℝ) (NativeBridge.integerValue (denote b) : ℝ)
    ?_ (NativeBridge.integerValue_spec _ hb) ?_
  · change M.number (k : ℂ) = M.number ((k : ℝ) : ℂ)
    simp only [Complex.ofReal_intCast]
  · exact_mod_cast hk

theorem integerInPositiveAbove [SetSemantics M]
    {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a NPos) (k : ℤ)
    (hk : NativeBridge.integerValue (denote a) ≤ k) :
    In (number (M := M) (k : ℂ)) NPos := by
  apply (SetSemantics.sep_members _ _ _).mpr
  refine ⟨integerInNaturalAbove a (inNPos_natural a ha) k hk, ?_⟩
  exact (positiveRealPredicate_iff (number (M := M) (k : ℂ))).mpr
    (ltLeTrans (number 0) a (number (k : ℂ)) (inNPos_positive a ha)
      (integerLowerBound a (naturalToInteger a (inNPos_natural a ha)) k hk))

theorem integerInCoveredRange [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (A : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (cover : Subset (closedRange a b ha hb) A)
    (k : ℤ) (hlo : NativeBridge.integerValue (denote a) ≤ k)
    (hhi : k ≤ NativeBridge.integerValue (denote b)) :
    M.mem (M.number (k : ℂ)) (denote A) := by
  exact cover _ (inClosedRangeOfDenote a b (number (k : ℂ)) ha hb
    (NativeBridge.integerValue (denote a)) (NativeBridge.integerValue (denote b)) k
    (NativeBridge.integerValue_spec _ ha) (NativeBridge.integerValue_spec _ hb)
    rfl hlo hhi)

theorem integerRangeGuards {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (i j : ℤ)
    (ha : Same a (number (i : ℂ))) (hb : Same b (number (j : ℂ)))
    (G : M.Value → Prop) (h : ∀ k ∈ integerFoldIndices i j, G (M.number (k : ℂ))) :
    ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → G (M.number (k : ℂ)) := by
  change denote a = M.number (i : ℂ) at ha
  change denote b = M.number (j : ℂ) at hb
  rw [ha, hb, NativeBridge.integerValue_number, NativeBridge.integerValue_number]
  exact fun k hlo hhi => h k ((integerFoldIndices_mem i j k).mpr ⟨hlo, hhi⟩)
end Litex

namespace Litex
variable {M : Semantics.{u}} [S : SetSemantics M]
theorem finiteGuardEmpty (G : M.Value → Prop) :
    ∀ x, M.mem x (denote (emptySet (M := M))) → G x :=
  fun x hx => (S.empty_members x hx).elim

theorem finiteGuardInsert {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (InsertObj (M := M) α β)) (G : M.Value → Prop)
    (head : G (denote p.val.element))
    (tail : ∀ x, M.mem x (denote p.val.tail) → G x) :
    ∀ x, M.mem x (denote p) → G x := by
  intro x hx
  obtain h | h := (S.insert_members _ _ _).mp hx
  · exact h ▸ head
  · exact tail x h
end Litex

namespace Litex
noncomputable def nativeCoth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x
noncomputable def nativeSech (x : ℝ) : ℝ := 1 / Real.cosh x
noncomputable def nativeCsch (x : ℝ) : ℝ := 1 / Real.sinh x

structure SinhObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sinhRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SinhObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.sinh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sinh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sinh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SinhObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSinh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sinh r : ℝ) : ℂ) := by
  change realUnaryValue Real.sinh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sinhInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.sinh (NativeBridge.asReal p.val.arg p.wd),
    denoteSinh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CoshObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance coshRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CoshObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.cosh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.cosh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def cosh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (CoshObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteCosh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.cosh r : ℝ) : ℂ) := by
  change realUnaryValue Real.cosh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem coshInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.cosh (NativeBridge.asReal p.val.arg p.wd),
    denoteCosh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure TanhObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance tanhRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (TanhObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue Real.tanh (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.tanh r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def tanh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (TanhObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteTanh {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanhObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.tanh r : ℝ) : ℂ) := by
  change realUnaryValue Real.tanh (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem tanhInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (TanhObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨Real.tanh (NativeBridge.asReal p.val.arg p.wd),
    denoteTanh p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CothObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cothRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CothObj (M := M) α) where
  wd a := In a.arg R ∧ ¬ Same a.arg (number 0)
  denote a := realUnaryValue nativeCoth (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCoth r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def coth {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hzero : ¬ Same a (number 0)) :
    Obj (M := M) (CothObj (M := M) α) := ⟨⟨a⟩,ha,hzero⟩

theorem denoteCoth {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCoth r : ℝ) : ℂ) := by
  change realUnaryValue nativeCoth (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cothInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCoth (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCoth p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

structure SechObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sechRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SechObj (M := M) α) where
  wd a := In a.arg R
  denote a := realUnaryValue nativeSech (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeSech r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def sech {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    Obj (M := M) (SechObj (M := M) α) := ⟨⟨a⟩,ha⟩

theorem denoteSech {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeSech r : ℝ) : ℂ) := by
  change realUnaryValue nativeSech (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem sechInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeSech (NativeBridge.asReal p.val.arg p.wd),
    denoteSech p _ (NativeBridge.asReal_spec p.val.arg p.wd)⟩

structure CschObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance cschRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (CschObj (M := M) α) where
  wd a := In a.arg R ∧ ¬ Same a.arg (number 0)
  denote a := realUnaryValue nativeCsch (denote a.arg)
  wd_isSet {a} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h.1
    exact M.member_isSet ((M.real_members _).mpr ⟨nativeCsch r, by
      rw [hr, realUnaryValue_number]⟩)

noncomputable def csch {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (hzero : ¬ Same a (number 0)) :
    Obj (M := M) (CschObj (M := M) α) := ⟨⟨a⟩,ha,hzero⟩

theorem denoteCsch {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((nativeCsch r : ℝ) : ℂ) := by
  change realUnaryValue nativeCsch (denote p.val.arg) = _
  rw [hr, realUnaryValue_number]

theorem cschInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : In p R :=
  (M.real_members _).mpr ⟨nativeCsch (NativeBridge.asReal p.val.arg p.wd.1),
    denoteCsch p _ (NativeBridge.asReal_spec p.val.arg p.wd.1)⟩

theorem coshPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : Lt (number 0) p := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.ltOfDenoteReal (number 0) p 0 (Real.cosh x) rfl
    (denoteCosh p x (NativeBridge.asReal_spec p.val.arg p.wd)) (Real.cosh_pos x)

theorem sechPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : Lt (number 0) p := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.ltOfDenoteReal (number 0) p 0 (nativeSech x) rfl
    (denoteSech p x (NativeBridge.asReal_spec p.val.arg p.wd))
    (one_div_pos.mpr (Real.cosh_pos x))

theorem coshInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : In p RPos :=
  inRPos_intro p (coshInR p) (coshPositive p)

theorem sechInRPos {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : In p RPos :=
  inRPos_intro p (sechInR p) (sechPositive p)

theorem sinhNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α))
    (hne : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx hne)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (Real.sinh x : ℂ) 0
    (denoteSinh p x hx) rfl (Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hn))

theorem coshNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (Real.cosh x : ℂ) 0
    (denoteCosh p x (NativeBridge.asReal_spec p.val.arg p.wd)) rfl
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.cosh_pos x)))

theorem sechNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SechObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeSech x : ℂ) 0
    (denoteSech p x (NativeBridge.asReal_spec p.val.arg p.wd)) rfl
    (Complex.ofReal_ne_zero.mpr (one_div_ne_zero (ne_of_gt (Real.cosh_pos x))))

theorem cothNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx p.wd.2)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeCoth x : ℂ) 0
    (denoteCoth p x hx) rfl (Complex.ofReal_ne_zero.mpr
      (div_ne_zero (ne_of_gt (Real.cosh_pos x)) (Real.sinh_ne_zero.mpr hn)))

theorem cschNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : ¬ Same p (number 0) := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hn : x ≠ 0 := Complex.ofReal_ne_zero.mp (NativeBridge.nativeNonzeroOfDenote p.val.arg (x : ℂ) hx p.wd.2)
  exact NativeBridge.notSameOfDenoteNumber p (number 0) (nativeCsch x : ℂ) 0
    (denoteCsch p x hx) rfl (Complex.ofReal_ne_zero.mpr (one_div_ne_zero (Real.sinh_ne_zero.mpr hn)))

theorem cothInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CothObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cothInR p) (cothNonzero p)

theorem cschInRStar {M : Semantics.{u}} [SetSemantics M] {α : Type v} [Representation M α]
    (p : Obj (M := M) (CschObj (M := M) α)) : In p RStar :=
  inRStar_intro p (cschInR p) (cschNonzero p)

end Litex

namespace Litex
@[simp] theorem nativeSech_zero : nativeSech 0 = 1 := by simp [nativeSech]
end Litex

namespace Litex
theorem sinhDefinition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SinhObj (M := M) α)) :
    denote p = M.divValue
      (M.subValue (realUnaryValue Real.exp (denote p.val.arg))
        (realUnaryValue Real.exp (M.negValue (denote p.val.arg)))) (M.number 2) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  rw [denoteSinh p x hx, hx, M.neg_numbers, ← Complex.ofReal_neg,
    realUnaryValue_number, realUnaryValue_number, M.sub_numbers,
    M.div_numbers _ _ (by norm_num)]
  apply congrArg M.number
  rw [Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem coshDefinition {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (CoshObj (M := M) α)) :
    denote p = M.divValue
      (M.addValue (realUnaryValue Real.exp (denote p.val.arg))
        (realUnaryValue Real.exp (M.negValue (denote p.val.arg)))) (M.number 2) := by
  let x := NativeBridge.asReal p.val.arg p.wd
  have hx := NativeBridge.asReal_spec p.val.arg p.wd
  rw [denoteCosh p x hx, hx, M.neg_numbers, ← Complex.ofReal_neg,
    realUnaryValue_number, realUnaryValue_number, M.add_numbers,
    M.div_numbers _ _ (by norm_num)]
  apply congrArg M.number
  rw [Real.cosh_eq, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat]
end Litex

namespace Litex

theorem hyperbolicPythagorean (x : ℝ) :
    (Real.cosh x : ℂ)^2 - (Real.sinh x : ℂ)^2 = 1 := by
  exact_mod_cast Real.cosh_sq_sub_sinh_sq x

theorem sinhDoubleAngle (x : ℝ) :
    (Real.sinh (2*x) : ℂ) = 2 * (Real.sinh x : ℂ) * (Real.cosh x : ℂ) := by
  exact_mod_cast Real.sinh_two_mul x

theorem coshDoubleAngle (x : ℝ) :
    (Real.cosh (2*x) : ℂ) = (Real.cosh x : ℂ)^2 + (Real.sinh x : ℂ)^2 := by
  exact_mod_cast Real.cosh_two_mul x

theorem sinhAddition (x y : ℝ) :
    (Real.sinh (x+y) : ℂ) = (Real.sinh x : ℂ)*(Real.cosh y : ℂ) +
      (Real.cosh x : ℂ)*(Real.sinh y : ℂ) := by
  exact_mod_cast Real.sinh_add x y

theorem coshAddition (x y : ℝ) :
    (Real.cosh (x+y) : ℂ) = (Real.cosh x : ℂ)*(Real.cosh y : ℂ) +
      (Real.sinh x : ℂ)*(Real.sinh y : ℂ) := by
  exact_mod_cast Real.cosh_add x y

theorem tanhReciprocal (x : ℝ) :
    (Real.tanh x : ℂ) * (Real.cosh x : ℂ) = (Real.sinh x : ℂ) := by
  have h : Real.tanh x * Real.cosh x = Real.sinh x := by
    rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos x))]
  exact_mod_cast h

theorem cothReciprocal (x : ℝ) (hx : x ≠ 0) :
    (nativeCoth x : ℂ) * (Real.sinh x : ℂ) = (Real.cosh x : ℂ) := by
  have h : nativeCoth x * Real.sinh x = Real.cosh x := by
    exact div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)
  exact_mod_cast h

theorem sechReciprocal (x : ℝ) :
    (nativeSech x : ℂ) * (Real.cosh x : ℂ) = 1 := by
  have h : nativeSech x * Real.cosh x = 1 := div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos x))
  exact_mod_cast h

theorem cschReciprocal (x : ℝ) (hx : x ≠ 0) :
    (nativeCsch x : ℂ) * (Real.sinh x : ℂ) = 1 := by
  have h : nativeCsch x * Real.sinh x = 1 := div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)
  exact_mod_cast h

theorem tanhThroughSech (x : ℝ) :
    (Real.tanh x : ℂ) = (Real.sinh x : ℂ) * (nativeSech x : ℂ) := by
  simp only [Real.tanh_eq_sinh_div_cosh, nativeSech, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem cothThroughCsch (x : ℝ) :
    (nativeCoth x : ℂ) = (Real.cosh x : ℂ) * (nativeCsch x : ℂ) := by
  rw [nativeCoth, nativeCsch, Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem tanhCothProduct (x : ℝ) (hx : x ≠ 0) :
    (Real.tanh x : ℂ) * (nativeCoth x : ℂ) = 1 := by
  have h : Real.tanh x * nativeCoth x = 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, nativeCoth]
    field_simp
  exact_mod_cast h

theorem tanhSechSquare (x : ℝ) :
    1 - (Real.tanh x : ℂ)^2 = (nativeSech x : ℂ)^2 := by
  have h : 1 - (Real.tanh x)^2 = (nativeSech x)^2 := by
    rw [Real.tanh_eq_sinh_div_cosh, nativeSech]
    have hc := ne_of_gt (Real.cosh_pos x)
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  exact_mod_cast h

theorem cothCschSquare (x : ℝ) (hx : x ≠ 0) :
    (nativeCoth x : ℂ)^2 - 1 = (nativeCsch x : ℂ)^2 := by
  have h : (nativeCoth x)^2 - 1 = (nativeCsch x)^2 := by
    rw [nativeCoth, nativeCsch]
    have hs := Real.sinh_ne_zero.mpr hx
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  exact_mod_cast h

theorem expThroughHyperbolic {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    realUnaryValue Real.exp (denote a) =
      M.addValue (realUnaryValue Real.cosh (denote a)) (realUnaryValue Real.sinh (denote a)) := by
  obtain ⟨x, hx⟩ := (M.real_members _).mp ha
  rw [hx, realUnaryValue_number, realUnaryValue_number, realUnaryValue_number, M.add_numbers]
  apply congrArg M.number
  exact_mod_cast (Real.cosh_add_sinh x).symm

theorem expNegativeThroughHyperbolic {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) :
    realUnaryValue Real.exp (M.negValue (denote a)) =
      M.subValue (realUnaryValue Real.cosh (denote a)) (realUnaryValue Real.sinh (denote a)) := by
  obtain ⟨x, hx⟩ := (M.real_members _).mp ha
  rw [hx, M.neg_numbers, ← Complex.ofReal_neg, realUnaryValue_number,
    realUnaryValue_number, realUnaryValue_number, M.sub_numbers]
  apply congrArg M.number
  exact_mod_cast (Real.cosh_sub_sinh x).symm
end Litex


namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]
theorem positiveFoldDomain :
    (homogeneousFoldSignature (denote (RPos (M := M))) (isSet RPos)).domain =
    (FunctionSignature.twoTarget .real .real (denote (RPos (M := M))) (isSet RPos)
      (fun a b => positiveRealPredicate a ∧ positiveRealPredicate b)).domain := by
  apply F.ext _ _ (homogeneousFoldSignature _ _).domain_isSet
    (FunctionSignature.twoTarget _ _ _ _ _).domain_isSet
  intro p
  change M.mem p (F.sepValue (FiniteFunction.cartValue ![denote RPos, denote RPos]) (fun _ => True)) ↔ _
  rw [F.sep_members]
  unfold FunctionSignature.twoTarget
  rw [FunctionSignature.withGuard_domain]
  constructor
  · rintro ⟨h, _⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp h
    have ha := (positiveReal_members (M := M) a).mp ha
    have hb := (positiveReal_members (M := M) b).mp hb
    refine ⟨(FiniteFunction.cart2_members _ _ _).mpr ⟨a, ha.1, b, hb.1, rfl⟩, ?_⟩
    simpa only [FiniteFunction.unpack_pack2] using And.intro ha.2 hb.2
  · rintro ⟨h, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (FiniteFunction.cart2_members _ _ _).mp h
    simp only [FiniteFunction.unpack_pack2] at hg
    exact ⟨(FiniteFunction.cart2_members _ _ _).mpr
      ⟨a, (positiveReal_members (M := M) a).mpr ⟨ha, hg.1⟩,
       b, (positiveReal_members (M := M) b).mpr ⟨hb, hg.2⟩, rfl⟩, True.intro⟩

theorem positiveFoldOperation {α : Type v} [Representation M α]
    (op : Obj (M := M) α)
    (h : In op (fnSet (FunctionSignature.twoTarget .real .real (denote (RPos (M := M)))
      (isSet RPos) (fun a b => positiveRealPredicate a ∧ positiveRealPredicate b)))) :
    In op (fnSet (homogeneousFoldSignature (denote (RPos (M := M))) (isSet RPos))) := by
  change M.mem (denote op) (F.fnSetValue (homogeneousFoldSignature (denote (RPos (M := M))) (isSet RPos)).domain (denote RPos))
  rw [positiveFoldDomain]
  exact h
end Litex

namespace Litex
theorem positiveRealPredicate_addNumber {M : Semantics.{u}} (a b : ℂ)
    (ha : positiveRealPredicate (M.number a)) (hb : positiveRealPredicate (M.number b)) :
    positiveRealPredicate (M.number (a + b)) := by
  obtain ⟨r, hr, hpr⟩ := ha
  obtain ⟨s, hs, hps⟩ := hb
  have hr := M.number_injective hr
  have hs := M.number_injective hs
  rw [hr, hs, ← Complex.ofReal_add]
  exact ⟨r+s, rfl, add_pos hpr hps⟩


theorem positiveRealPredicate_mulNumber {M : Semantics.{u}} (a b : ℂ)
    (ha : positiveRealPredicate (M.number a)) (hb : positiveRealPredicate (M.number b)) :
    positiveRealPredicate (M.number (a * b)) := by
  obtain ⟨r, hr, hpr⟩ := ha
  obtain ⟨s, hs, hps⟩ := hb
  have hr := M.number_injective hr
  have hs := M.number_injective hs
  rw [hr, hs, ← Complex.ofReal_mul]
  exact ⟨r*s, rfl, mul_pos hpr hps⟩


theorem positiveRealAggregate {M : Semantics.{u}} {ι : Type*}
    (product : Bool) (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, positiveRealPredicate (M.number (f i)))
    (hn : product = true ∨ s.Nonempty) :
    positiveRealPredicate (M.number (if product then ∏ i ∈ s, f i else ∑ i ∈ s, f i)) := by
  classical
  cases product
  · simp only [Bool.false_eq_true, false_or, ↓reduceIte] at hn ⊢
    induction s using Finset.induction_on with
    | empty => exact (Finset.not_nonempty_empty hn).elim
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      by_cases hs : s.Nonempty
      · exact positiveRealPredicate_addNumber _ _ (h i (Finset.mem_insert_self _ _))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hs)
      · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simpa only [he, Finset.sum_empty, add_zero] using h i (Finset.mem_insert_self _ _)
  · clear hn
    simp only [↓reduceIte]
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, zero_lt_one⟩
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact positiveRealPredicate_mulNumber _ _ (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))



theorem inNPos_intro {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α)
    (ha : In a N) (hp : Lt (number 0) a) : In a NPos :=
  (S.sep_members _ _ _).mpr ⟨ha, (positiveRealPredicate_iff a).mpr hp⟩


theorem rangeAggregatePositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) product α β γ))
    (hs : ∀ y, M.mem y p.val.signature.output → positiveRealPredicate y) :
    Lt (number 0) p := by
  apply (positiveRealPredicate_iff p).mp
  change positiveRealPredicate (M.number (nativeRangeAggregate product _ _ _))
  unfold nativeRangeAggregate
  apply positiveRealAggregate
  · intro i hi
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hi
    rw [← NativeBridge.complexValue_spec _ (rangeAggregateCallInC p i ha hb)]
    exact hs _ (F.call_mem _ _ _ _ p.wd.2.2.2.1 (p.wd.2.2.2.2.2 i ha hb))
  · right
    have ha : denote p.val.first = M.number ((NativeBridge.integerValue (denote p.val.first) : ℝ) : ℂ) :=
      NativeBridge.integerValue_spec _ p.wd.1
    have hb : denote p.val.last = M.number ((NativeBridge.integerValue (denote p.val.last) : ℝ) : ℂ) :=
      NativeBridge.integerValue_spec _ p.wd.2.1
    have hl := (NativeBridge.le_iff_ofDenoteReal p.val.first p.val.last _ _ ha hb).mp p.wd.2.2.1
    refine ⟨NativeBridge.integerValue (denote p.val.first), Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    exact_mod_cast hl



theorem finiteAggregatePositive {M : Semantics.{u}} [F : FunctionSemantics M]
    {product : Bool} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteAggregateObj (M := M) product α β))
    (hp : product = true)
    (hs : ∀ y, M.mem y p.val.signature.output → positiveRealPredicate y) :
    Lt (number 0) p := by
  classical
  apply (positiveRealPredicate_iff p).mp
  change positiveRealPredicate (M.number (finiteAggregateValue product _ _))
  unfold finiteAggregateValue
  have hf : (memberSet (denote p.val.set)).Finite := p.wd.1
  rw [dif_pos hf]
  apply positiveRealAggregate
  · intro i hi
    have ho := finiteAggregateCallInOutput p i (p.wd.1.mem_toFinset.mp hi)
    rw [← NativeBridge.complexValue_spec _ (p.wd.2.2.1 _ ho)]
    exact hs _ ho
  · exact Or.inl hp


end Litex
