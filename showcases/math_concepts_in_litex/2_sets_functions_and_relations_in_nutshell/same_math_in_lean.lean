/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

This file deliberately has no imports. Sets are characteristic predicates;
restricted functions use subtypes for their domains and codomains; a binary
relation is a predicate on ordered pairs. The code is handwritten comparison
material, not generated Litex-to-Lean compiler output.
-/

universe u

namespace SetsFunctionsRelationsSameMathInLean

abbrev Set (X : Type u) := X → Prop

def union {X : Type u} (A B : Set X) : Set X :=
  fun x => A x ∨ B x

def firstSet : Set Nat :=
  fun n => n = 1 ∨ n = 2 ∨ n = 3

def secondSet : Set Nat :=
  fun n => n = 2 ∨ n = 3 ∨ n = 4

def firstUnionSecondSet : Set Nat :=
  fun n => n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/- Set equality is proved extensionally, by following membership in both
directions. This is the Lean analogue of Litex's `by extension` proof. -/
theorem firstUnionSecond :
    union firstSet secondSet = firstUnionSecondSet := by
  funext n
  apply propext
  constructor
  · intro h
    cases h with
    | inl hFirst =>
        cases hFirst with
        | inl h1 => exact Or.inl h1
        | inr h23 =>
            cases h23 with
            | inl h2 => exact Or.inr (Or.inl h2)
            | inr h3 => exact Or.inr (Or.inr (Or.inl h3))
    | inr hSecond =>
        cases hSecond with
        | inl h2 => exact Or.inr (Or.inl h2)
        | inr h34 =>
            cases h34 with
            | inl h3 => exact Or.inr (Or.inr (Or.inl h3))
            | inr h4 => exact Or.inr (Or.inr (Or.inr h4))
  · intro h
    cases h with
    | inl h1 => exact Or.inl (Or.inl h1)
    | inr h234 =>
        cases h234 with
        | inl h2 => exact Or.inl (Or.inr (Or.inl h2))
        | inr h34 =>
            cases h34 with
            | inl h3 => exact Or.inl (Or.inr (Or.inr h3))
            | inr h4 => exact Or.inr (Or.inr (Or.inr h4))

/- Lean does not have Litex's finite-set enumeration proof form here, so the
three possible members of `firstSet` are eliminated explicitly. -/
theorem successorMovesFirstSetToSecondSet {n : Nat}
    (h : firstSet n) : secondSet (n + 1) := by
  cases h with
  | inl h1 =>
      subst n
      exact Or.inl rfl
  | inr h23 =>
      cases h23 with
      | inl h2 =>
          subst n
          exact Or.inr (Or.inl rfl)
      | inr h3 =>
          subst n
          exact Or.inr (Or.inr rfl)

abbrev First := {n : Nat // firstSet n}
abbrev Second := {n : Nat // secondSet n}

/- First presentation: a named restricted function. The result carries the
proof that it lies in `secondSet`. -/
def successorOnFirst (x : First) : Second :=
  ⟨x.1 + 1, successorMovesFirstSetToSecondSet x.2⟩

/- Second presentation: the same restricted map as an anonymous function
value. -/
def successorAsValue : First → Second :=
  fun x => ⟨x.1 + 1, successorMovesFirstSetToSecondSet x.2⟩

/- The graph is a set of ordered pairs satisfying the successor equation. -/
def successorGraph : Set (Nat × Nat) :=
  fun pair => pair.2 = pair.1 + 1

/- Third presentation: prove unique output, then select that output. Pure
Lean's Prelude has no `∃!` notation, so existence and uniqueness are expanded
using `∃`, `∀`, and equality. This is the counterpart of Litex's
`have fn ... by exist!`. -/
theorem uniqueSuccessorOutput (x : Nat) :
    ∃ y : Nat, y = x + 1 ∧
      ∀ candidate : Nat, candidate = x + 1 → candidate = y := by
  refine ⟨x + 1, rfl, ?_⟩
  intro candidate hCandidate
  exact hCandidate

noncomputable def successorFromUniqueOutput (x : Nat) : Nat :=
  Classical.choose (uniqueSuccessorOutput x)

theorem successorFromUniqueOutputSpec (x : Nat) :
    successorFromUniqueOutput x = x + 1 := by
  unfold successorFromUniqueOutput
  exact (Classical.choose_spec (uniqueSuccessorOutput x)).1

/- The selected output lies on the original set-theoretic graph. -/
theorem selectedSuccessorLiesOnGraph (x : Nat) :
    successorGraph (x, successorFromUniqueOutput x) := by
  exact successorFromUniqueOutputSpec x

/- The formula, anonymous value, and unique-selection presentations have the
same underlying output on the common finite domain. -/
theorem threeSuccessorPresentationsAgree (x : First) :
    (successorOnFirst x).1 = (successorAsValue x).1 ∧
      (successorAsValue x).1 = successorFromUniqueOutput x.1 := by
  constructor
  · rfl
  · exact (successorFromUniqueOutputSpec x.1).symm

end SetsFunctionsRelationsSameMathInLean
