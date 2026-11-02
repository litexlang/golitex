import Litex.Folds

universe u v w x

namespace Litex

theorem symmetricDifferenceCommutative {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (symmetricDifference A B) (symmetricDifference B A) := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro x
  change M.mem x (symmetricDifferenceValue (denote A) (denote B)) ↔
    M.mem x (symmetricDifferenceValue (denote B) (denote A))
  rw [symmetricDifference_members, symmetricDifference_members]
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  · rintro (h | h)
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩


theorem symmetricDifferenceEmpty {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Same (symmetricDifference A emptySet) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (symmetricDifferenceValue (denote A) S.emptyValue) ↔ M.mem z (denote A)
  simp only [symmetricDifference_members, S.empty_members, not_false_eq_true, and_true, and_false, or_false]

theorem symmetricDifferenceEmptyLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) :
    Same (symmetricDifference emptySet A) A := by
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (symmetricDifferenceValue S.emptyValue (denote A)) ↔ M.mem z (denote A)
  simp only [symmetricDifference_members, S.empty_members, not_false_eq_true, false_and, true_and, false_or]

theorem symmetricDifferenceCancel {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (symmetricDifference (symmetricDifference A B) B) A := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (symmetricDifferenceValue (symmetricDifferenceValue (denote A) (denote B)) (denote B)) ↔ M.mem z (denote A)
  simp only [symmetricDifference_members]
  tauto

theorem symmetricDifferenceUnionMinusIntersection {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) :
    Same (symmetricDifference A B) (setMinus (union A B) (intersect A B)) := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (symmetricDifferenceValue (denote A) (denote B)) ↔
    M.mem z (S.sepValue (S.unionValue (denote A) (denote B)) (fun t => ¬ M.mem t (S.sepValue (denote A) (fun t => M.mem t (denote B)))))
  simp only [symmetricDifference_members, S.sep_members, S.union_members]
  tauto

theorem symmetricDifferenceAssociative {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) :
    Same (symmetricDifference (symmetricDifference A B) C)
      (symmetricDifference A (symmetricDifference B C)) := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (symmetricDifferenceValue (symmetricDifferenceValue (denote A) (denote B)) (denote C)) ↔
    M.mem z (symmetricDifferenceValue (denote A) (symmetricDifferenceValue (denote B) (denote C)))
  simp only [symmetricDifference_members]
  tauto

theorem intersectDistributesSymmetricDifference {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (C : Obj (M := M) γ) :
    Same (intersect A (symmetricDifference B C))
      (symmetricDifference (intersect A B) (intersect A C)) := by
  classical
  apply S.ext _ _ (isSet _) (isSet _)
  intro z
  change M.mem z (S.sepValue (denote A) (fun t => M.mem t (symmetricDifferenceValue (denote B) (denote C)))) ↔
    M.mem z (symmetricDifferenceValue (S.sepValue (denote A) (fun t => M.mem t (denote B)))
      (S.sepValue (denote A) (fun t => M.mem t (denote C))))
  simp only [symmetricDifference_members, S.sep_members]
  tauto


end Litex
