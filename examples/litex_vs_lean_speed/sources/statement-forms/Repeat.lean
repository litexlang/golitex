import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open Lean Elab Command in
elab "#probe " label:str cmd:command : command => do
  let before ← get
  let start ← IO.monoNanosNow
  let mut success := true
  try
    elabCommand cmd
    if (← get).messages.hasErrors then
      success := false
  catch ex =>
    success := false
    IO.println s!"EXCEPTION,{label.getString},{← ex.toMessageData.toString}"
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"PROBE,{label.getString},{success},{elapsed}"
  set before

#probe "prop_definition_witness__term__first" theorem initial_prop_definition_witness_term : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_0 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_1 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_2 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_3 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_4 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_5 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "prop_definition_witness__term" theorem sample_prop_definition_witness_term_6 : ∃ t : Int, (7 : Int) = 2*t + 1 := ⟨3, by norm_num⟩

#probe "odd_shift__rcases_omega__first" theorem initial_odd_shift_rcases_omega : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_0 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_1 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_2 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_3 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_4 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_5 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "odd_shift__rcases_omega" theorem sample_odd_shift_rcases_omega_6 : ∀ n : Int, (∃ t : Int, n = 2*t + 1) → ∃ t : Int, 3*n + 2 = 2*t + 1 := by
  rintro n ⟨k, hk⟩
  exact ⟨3*k + 2, by omega⟩

#probe "reciprocal_tends_to_zero__archimedean__first" theorem initial_reciprocal_tends_to_zero_archimedean : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_0 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_1 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_2 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_3 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_4 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_5 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "reciprocal_tends_to_zero__archimedean" theorem sample_reciprocal_tends_to_zero_archimedean_6 : ∀ ε : Real, 0 < ε → ∃ n : Nat, 0 < n ∧ 1/(n:Real) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n+1, by omega, ?_⟩
  simpa using hn

#probe "set_union_subset_eq__ext_cases__first" theorem initial_set_union_subset_eq_ext_cases : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__lemma__first" theorem initial_set_union_subset_eq_lemma : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_0 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_1 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_2 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_3 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_4 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_5 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__ext_cases" theorem sample_set_union_subset_eq_ext_cases_6 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := by
  intro A B h
  ext x
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx
  · intro hx; exact Or.inr hx

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_0 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_1 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_2 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_3 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_4 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_5 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h

#probe "set_union_subset_eq__lemma" theorem sample_set_union_subset_eq_lemma_6 : ∀ A B : Set Real, A ⊆ B → A ∪ B = B := fun A B h => Set.union_eq_right.mpr h
