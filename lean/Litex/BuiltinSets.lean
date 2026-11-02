import Litex.FiniteSets

universe u v w

namespace Litex

theorem finiteSubsetOfFinite {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β)
    (hfinite : IsFiniteSet B) (hsubset : Subset A B) : IsFiniteSet A :=
  hfinite.subset hsubset

theorem unionOfSubsetRight {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset A B) :
    Same (union A B) B := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (S.unionValue (denote A) (denote B)) ↔ M.mem x (denote B)
  rw [S.union_members]
  exact ⟨fun hx => hx.elim (h x) id, Or.inr⟩

theorem unionOfSubsetLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset B A) :
    Same (union A B) A :=
  (unionComm A B).trans (unionOfSubsetRight B A h)

theorem setMinusRecovery {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (h : Subset B A) :
    Same (setMinus A (setMinus A B)) B := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (S.sepValue (denote A) (fun t =>
    ¬ M.mem t (S.sepValue (denote A) (fun s => ¬ M.mem s (denote B))))) ↔ M.mem x (denote B)
  simp only [S.sep_members]
  constructor
  · rintro ⟨ha, hx⟩
    by_contra hb
    exact hx ⟨ha, hb⟩
  · intro hb
    exact ⟨h x hb, fun hx => hx.2 hb⟩

theorem unionSetMinusDecomposition {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (union A (setMinus B A)) (union A B) := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (S.unionValue (denote A) (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A)))) ↔
    M.mem x (S.unionValue (denote A) (denote B))
  simp only [S.union_members, S.sep_members]
  constructor
  · exact fun h => h.elim Or.inl (fun h => Or.inr h.1)
  · intro h
    by_cases ha : M.mem x (denote A)
    · exact Or.inl ha
    · exact Or.inr ⟨h.resolve_left ha, ha⟩

theorem setMinusOfIntersection {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (setMinus B (intersect A B)) (setMinus B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (S.sepValue (denote B) (fun t =>
    ¬ M.mem t (S.sepValue (denote A) (fun s => M.mem s (denote B))))) ↔
    M.mem x (S.sepValue (denote B) (fun t => ¬ M.mem t (denote A)))
  simp only [S.sep_members]
  exact ⟨fun h => ⟨h.1, fun ha => h.2 ⟨ha,h.1⟩⟩,
    fun h => ⟨h.1, fun hab => h.2 hab.1⟩⟩

theorem emptyOfNotNonempty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (h : ¬ IsNonempty A) :
    Same A (emptySet (M := M)) := by
  apply S.ext _ _ (isSet _) S.empty_isSet
  intro x
  exact ⟨fun hx => (h ⟨x,hx⟩).elim, fun hx => (S.empty_members x hx).elim⟩

theorem powerSetIntersection {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (powerSet (intersect A B)) (intersect (powerSet A) (powerSet B)) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (S.powerValue (S.sepValue (denote A) (fun t => M.mem t (denote B)))) ↔
    M.mem x (S.sepValue (S.powerValue (denote A)) (fun t => M.mem t (S.powerValue (denote B))))
  simp only [S.power_members, S.sep_members]
  exact ⟨fun h => ⟨⟨h.1,fun y hy => (h.2 y hy).1⟩,⟨h.1,fun y hy => (h.2 y hy).2⟩⟩,
    fun h => ⟨h.1.1,fun y hy => ⟨h.1.2 y hy,h.2.2 y hy⟩⟩⟩

theorem powerEmptyValue {M : Semantics.{u}} [S : SetSemantics M] :
    S.powerValue S.emptyValue = S.insertValue S.emptyValue S.emptyValue := by
  apply S.ext _ _ (S.power_isSet _ S.empty_isSet)
    (S.insert_isSet _ _ S.empty_isSet S.empty_isSet)
  intro A
  rw [S.power_members, S.insert_members]
  constructor
  · intro h
    exact Or.inl (S.ext _ _ h.1 S.empty_isSet (fun x =>
      ⟨fun hx => (S.empty_members x (h.2 x hx)).elim, fun hx => (S.empty_members x hx).elim⟩))
  · intro h
    rcases h with rfl | h
    · exact ⟨S.empty_isSet, fun _ hx => hx⟩
    · exact (S.empty_members _ h).elim

theorem familyUnionEmptyValue {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] : I.indexedUnionValue S.emptyValue id = S.emptyValue := by
  apply S.ext _ _ (I.indexedUnion_isSet _ _ S.empty_isSet (fun a ha => (S.empty_members a ha).elim)) S.empty_isSet
  intro x
  rw [I.indexedUnion_members]
  exact ⟨fun ⟨a,ha,_⟩ => (S.empty_members a ha).elim, fun hx => (S.empty_members x hx).elim⟩

theorem familyUnionSingletonValue {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] (a : M.Value) (ha : M.isSet a) :
    I.indexedUnionValue (S.insertValue a S.emptyValue) id = a := by
  apply S.ext _ _ (I.indexedUnion_isSet _ _ (S.insert_isSet _ _ ha S.empty_isSet)
    (fun b hb => M.member_isSet hb)) ha
  intro x
  simp only [I.indexedUnion_members, S.insert_members, S.empty_members, or_false]
  exact ⟨fun ⟨b,hb,hx⟩ => hb ▸ hx, fun hx => ⟨a,rfl,hx⟩⟩

theorem familyUnionPowerValue {M : Semantics.{u}} [S : SetSemantics M]
    [I : IndexedUnionSemantics M] {α : Type v} [Representation M α]
    (A : Obj (M := M) α) : Same (familyUnion (powerSet A)) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (I.indexedUnionValue (S.powerValue (denote A)) id) ↔ M.mem x (denote A)
  rw [I.indexedUnion_members]
  constructor
  · rintro ⟨B,hB,hx⟩
    exact ((S.power_members _ _).mp hB).2 x hx
  · intro hx
    refine ⟨S.insertValue x S.emptyValue, (S.power_members _ _).mpr ⟨S.insert_isSet _ _ (M.member_isSet hx) S.empty_isSet, ?_⟩, ?_⟩
    · intro y hy
      rcases (S.insert_members _ _ _).mp hy with rfl | hy
      · exact hx
      · exact (S.empty_members _ hy).elim
    · exact (S.insert_members _ _ _).mpr (Or.inl rfl)

theorem memberEqualityWitness {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (A : Obj (M := M) β) (ha : In a A) :
    ∃ x : Obj (M := M) M.Value, ∃ _ : In x A, Same x a := by
  exact ⟨semanticObject (denote a) (isSet a), ha, rfl⟩

theorem nonemptyMemberWitness {M : Semantics.{u}}
    {α : Type v} [Representation M α] (A : Obj (M := M) α)
    (hA : IsNonempty A) :
    ∃ x : Obj (M := M) M.Value, ∃ _ : In x A, In x A := by
  obtain ⟨value, hvalue⟩ := hA
  exact ⟨semanticObject value (M.member_isSet hvalue), hvalue, hvalue⟩


theorem cartesianUnionValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (S T U : M.Value) (hS : M.isSet S) (hT : M.isSet T) (hU : M.isSet U) :
    FiniteFunction.cartValue ![S, F.unionValue T U] =
      F.unionValue (FiniteFunction.cartValue ![S, T]) (FiniteFunction.cartValue ![S, U]) := by
  have cartSet (A B : M.Value) (hA : M.isSet A) (hB : M.isSet B) :
      M.isSet (FiniteFunction.cartValue ![A, B]) := by
    apply FiniteFunction.cart_isSet
    intro i
    fin_cases i
    · exact hA
    · exact hB
  apply F.ext _ _ (cartSet S _ hS (F.union_isSet T U hT hU))
    (F.union_isSet _ _ (cartSet S T hS hT) (cartSet S U hS hU))
  intro p
  simp only [FiniteFunction.cart2_members, F.union_members]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases hb with hb | hb
    · exact Or.inl ⟨a, ha, b, hb, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact ⟨a, ha, b, Or.inl hb, rfl⟩
    · exact ⟨a, ha, b, Or.inr hb, rfl⟩

end Litex
