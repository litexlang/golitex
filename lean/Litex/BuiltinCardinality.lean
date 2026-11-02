import Litex.BuiltinSets
import Litex.Folds

universe u v w

namespace Litex

theorem memberSetUnionValue {M : Semantics.{u}} [S : SetSemantics M] (a b : M.Value) :
    memberSet (S.unionValue a b) = memberSet a ∪ memberSet b :=
  Set.ext (fun x => S.union_members a b x)

theorem memberSetIntersectionValue {M : Semantics.{u}} [S : SetSemantics M] (a b : M.Value) :
    memberSet (S.sepValue a (fun x => M.mem x b)) = memberSet a ∩ memberSet b :=
  Set.ext (fun x => S.sep_members a (fun x => M.mem x b) x)

theorem memberSetDifferenceValue {M : Semantics.{u}} [S : SetSemantics M] (a b : M.Value) :
    memberSet (S.sepValue a (fun x => ¬ M.mem x b)) = memberSet a \ memberSet b :=
  Set.ext (fun x => S.sep_members a (fun x => ¬ M.mem x b) x)

theorem finiteUnionFromBoth {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (ha : IsFiniteSet A) (hb : IsFiniteSet B) :
    IsFiniteSet (union A B) := by
  change (memberSet (S.unionValue (denote A) (denote B))).Finite
  rw [memberSetUnionValue]
  exact ha.union hb

theorem finiteDifferenceFromLeft {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (A : Obj (M := M) α) (B : Obj (M := M) β) (ha : IsFiniteSet A) :
    IsFiniteSet (setMinus A B) := by
  have h : (memberSet (denote A) \ memberSet (denote B)).Finite := ha.subset (fun _ hx => hx.1)
  change (memberSet (S.sepValue (denote A) (fun x => ¬ M.mem x (denote B)))).Finite
  rw [memberSetDifferenceValue]
  exact h

theorem emptyOfCardinalityZero {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) (h : Same p (number 0)) :
    Same p.val.set (emptySet (M := M)) := by
  change M.number ((finiteCard (denote p.val.set) : ℕ) : ℂ) = M.number 0 at h
  have hc : finiteCard (denote p.val.set) = 0 := by exact_mod_cast M.number_injective h
  have he := (Set.ncard_eq_zero p.wd).mp hc
  apply S.ext _ _ (isSet _) S.empty_isSet
  intro x
  apply iff_of_false _ (S.empty_members x)
  intro hx
  have hx : x ∈ (∅ : Set M.Value) := he ▸ hx
  exact hx

theorem sameOfFiniteSubsetCardinality {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α))
    (q : Obj (M := M) (FiniteSetSizeObj (M := M) β))
    (he : Same p q) (hs : Subset p.val.set q.val.set) : Same p.val.set q.val.set := by
  change M.number ((finiteCard (denote p.val.set) : ℕ) : ℂ) =
    M.number ((finiteCard (denote q.val.set) : ℕ) : ℂ) at he
  have hc : finiteCard (denote p.val.set) = finiteCard (denote q.val.set) := by
    exact_mod_cast M.number_injective he
  have hsets := Set.eq_of_subset_of_ncard_le hs hc.symm.le q.wd
  apply S.ext _ _ (isSet _) (isSet _)
  exact Set.ext_iff.mp hsets

theorem finiteCardinalitySubsetLe {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α))
    (q : Obj (M := M) (FiniteSetSizeObj (M := M) β))
    (hs : Subset p.val.set q.val.set) : Le p q := by
  refine NativeBridge.leOfDenoteReal p q (finiteCard (denote p.val.set) : ℝ)
    (finiteCard (denote q.val.set) : ℝ) ?_ ?_ ?_
  · change M.number (_ : ℂ) = M.number ((_ : ℝ) : ℂ)
    rw [Complex.ofReal_natCast]
  · change M.number (_ : ℂ) = M.number ((_ : ℝ) : ℂ)
    rw [Complex.ofReal_natCast]
  · exact_mod_cast Set.ncard_le_ncard hs q.wd

theorem finiteCardinalityProperSubsetLt {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α))
    (q : Obj (M := M) (FiniteSetSizeObj (M := M) β))
    (hs : ProperSubset p.val.set q.val.set) : Lt p q := by
  have strict : memberSet (denote p.val.set) ⊂ memberSet (denote q.val.set) := by
    refine ⟨hs.1, ?_⟩
    intro back
    apply hs.2
    apply S.ext _ _ (isSet _) (isSet _)
    exact fun x => ⟨hs.1 x, @back x⟩
  refine NativeBridge.ltOfDenoteReal p q (finiteCard (denote p.val.set) : ℝ)
    (finiteCard (denote q.val.set) : ℝ) ?_ ?_ ?_
  · change M.number (_ : ℂ) = M.number ((_ : ℝ) : ℂ)
    rw [Complex.ofReal_natCast]
  · change M.number (_ : ℂ) = M.number ((_ : ℝ) : ℂ)
    rw [Complex.ofReal_natCast]
  · exact_mod_cast Set.ncard_lt_ncard strict q.wd

theorem finiteCardinalityUnionValue {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α))
    (q : Obj (M := M) (FiniteSetSizeObj (M := M) β))
    (reverseUnion reverseIntersection : Bool) :
    M.number (finiteCard (if reverseUnion then S.unionValue (denote q.val.set) (denote p.val.set)
      else S.unionValue (denote p.val.set) (denote q.val.set)) : ℂ) =
      M.subValue (M.addValue (denote p) (denote q))
        (M.number (finiteCard (if reverseIntersection then
          S.sepValue (denote q.val.set) (fun x => M.mem x (denote p.val.set))
          else S.sepValue (denote p.val.set) (fun x => M.mem x (denote q.val.set))) : ℂ)) := by
  have hn : (((memberSet (denote p.val.set)) ∪ memberSet (denote q.val.set)).ncard : ℂ) =
      ((memberSet (denote p.val.set)).ncard : ℂ) + ((memberSet (denote q.val.set)).ncard : ℂ) -
      (((memberSet (denote p.val.set)) ∩ memberSet (denote q.val.set)).ncard : ℂ) := by
    apply eq_sub_iff_add_eq.mpr
    exact_mod_cast Set.ncard_union_add_ncard_inter
      (memberSet (denote p.val.set)) (memberSet (denote q.val.set)) p.wd q.wd
  change M.number _ = M.subValue (M.addValue (M.number _) (M.number _)) (M.number _)
  rw [M.add_numbers, M.sub_numbers]
  apply congrArg M.number
  cases reverseUnion <;> cases reverseIntersection <;>
    simpa only [Bool.false_eq_true, if_false, if_true, finiteCard,
      memberSetUnionValue, memberSetIntersectionValue, Set.union_comm, Set.inter_comm] using hn

theorem finiteCardinalityDifferenceValue {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FiniteSetSizeObj (M := M) α)) (B : Obj (M := M) β) :
    M.number (finiteCard (S.sepValue (denote p.val.set) (fun x => ¬ M.mem x (denote B))) : ℂ) =
      M.subValue (denote p)
        (M.number (finiteCard (S.sepValue (denote p.val.set) (fun x => M.mem x (denote B))) : ℂ)) := by
  let a := memberSet (denote p.val.set)
  let b := memberSet (denote B)
  have he : a \ (a ∩ b) = a \ b := by
    ext x
    exact ⟨fun h => ⟨h.1, fun hb => h.2 ⟨h.1,hb⟩⟩,
      fun h => ⟨h.1, fun hab => h.2 hab.2⟩⟩
  have hn := Set.ncard_sdiff_add_ncard_of_subset (show a ∩ b ⊆ a from Set.inter_subset_left)
    (show a.Finite from p.wd)
  rw [he] at hn
  change M.number _ = M.subValue (M.number _) (M.number _)
  rw [M.sub_numbers]
  apply congrArg M.number
  unfold finiteCard
  rw [memberSetDifferenceValue, memberSetIntersectionValue]
  apply eq_sub_iff_add_eq.mpr
  exact_mod_cast hn

end Litex
