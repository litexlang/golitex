import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

theorem validated_prop_definition_witness_term : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

theorem validated_odd_shift_rcases_omega : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

theorem validated_reciprocal_tends_to_zero_archimedean : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

theorem validated_set_union_subset_eq_ext_cases : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

theorem validated_set_union_subset_eq_lemma : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#print axioms validated_prop_definition_witness_term

#print axioms validated_odd_shift_rcases_omega

#print axioms validated_reciprocal_tends_to_zero_archimedean

#print axioms validated_set_union_subset_eq_ext_cases

#print axioms validated_set_union_subset_eq_lemma
