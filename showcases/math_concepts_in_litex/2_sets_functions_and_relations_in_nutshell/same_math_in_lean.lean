/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

This file deliberately has no imports. Sets are their characteristic
predicates, a binary relation is a predicate on ordered pairs, and functions
are ordinary Lean functions. It is handwritten comparison code, not generated
Litex-to-Lean compiler output.
-/

universe u v

namespace SetsFunctionsRelationsSameMathInLean

abbrev Set (X : Type u) := X → Prop

def union {X : Type u} (A B : Set X) : Set X :=
  fun x => A x ∨ B x

def intersection {X : Type u} (A B : Set X) : Set X :=
  fun x => A x ∧ B x

def difference {X : Type u} (A B : Set X) : Set X :=
  fun x => A x ∧ ¬ B x

def firstSet : Set Nat :=
  fun n => n = 1 ∨ n = 2 ∨ n = 3

def secondSet : Set Nat :=
  fun n => n = 2 ∨ n = 3 ∨ n = 4

example : union firstSet secondSet 4 := by
  exact Or.inr (Or.inr (Or.inr rfl))

example : intersection firstSet secondSet 2 := by
  exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩

example : difference firstSet secondSet 1 := by
  refine ⟨Or.inl rfl, ?_⟩
  intro h
  cases h with
  | inl h12 => cases h12
  | inr hrest =>
      cases hrest with
      | inl h13 => cases h13
      | inr h14 => cases h14

def successor (n : Nat) : Nat := n + 1

example : successor 4 = 5 := rfl

def InRange {X : Type u} {Y : Type v} (f : X → Y) (y : Y) : Prop :=
  ∃ x, f x = y

example : InRange successor 5 := ⟨4, rfl⟩

abbrev BinaryRelation (X : Type u) := Set (X × X)

def nextRelation : BinaryRelation Nat :=
  fun pair => pair = (1, 2)

example : nextRelation (1, 2) := rfl

theorem successorInjective {x y : Nat}
    (h : successor x = successor y) : x = y := by
  exact Nat.succ.inj h

end SetsFunctionsRelationsSameMathInLean
