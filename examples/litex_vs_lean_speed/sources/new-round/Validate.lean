import Mathlib
import Lean
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

theorem validated_sqrt_two_irrational_mathlib_theorem : Irrational (Real.sqrt 2) := irrational_sqrt_two

theorem validated_sqrt_two_irrational_scratch : Irrational (Real.sqrt 2) := by
  rintro ⟨q, hq⟩
  have h2 : (q : Real) ^ 2 = 2 := by
    rw [hq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  -- 唯一既约分数：p = |num|, m = den, gcd p m = 1
  set p : Nat := q.num.natAbs with hp
  set m : Nat := q.den with hm
  have hden : (m : Real) ≠ 0 := by
    have : (0 : Nat) < m := q.den_pos
    exact_mod_cast this.ne'
  -- 把 (q : ℝ) = num / den 代入
  have hqeq : (q : Real) = (q.num : Real) / (m : Real) := by
    rw [Rat.cast_def, hm]
  -- p² = 2 m²（先把 ℤ 上的等式转成 ℕ）
  have hnat : p ^ 2 = 2 * m ^ 2 := by
    have hreal : (q.num : Real) ^ 2 = 2 * (m : Real) ^ 2 := by
      rw [hqeq] at h2
      field_simp at h2
      nlinarith [h2]
    have hint : q.num ^ 2 = 2 * (m : Int) ^ 2 := by
      exact_mod_cast hreal
    have habs : ((p : Int)) ^ 2 = 2 * (m : Int) ^ 2 := by
      have hnum : q.num ^ 2 = ((p : Int)) ^ 2 := by
        rcases Int.natAbs_eq q.num with h | h
        · rw [h, hp]
        · rw [h, hp]; ring
      rw [← hnum, hint]
    exact_mod_cast habs
  -- p 是偶数
  have hp2 : 2 ∣ p ^ 2 := ⟨m ^ 2, hnat⟩
  have hp_even : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hp2
  -- 于是 q 也是偶数
  obtain ⟨k, hk⟩ := hp_even
  have hm2 : m ^ 2 = 2 * k ^ 2 := by
    rw [hk] at hnat
    nlinarith
  have hm2dvd : 2 ∣ m ^ 2 := ⟨k ^ 2, hm2⟩
  have hm_even : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hm2dvd
  -- 与 gcd(p, m) = 1 矛盾
  have hcop : p.Coprime m := q.reduced
  have hgcd : 2 ∣ p.gcd m := Nat.dvd_gcd ⟨k, hk⟩ hm_even
  rw [hcop] at hgcd
  omega

theorem validated_set_union_inter_distrib_lemma : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

theorem validated_set_union_inter_distrib_ext_simp : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

theorem validated_set_diff_union_ext_simp : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

theorem validated_set_inter_monotone_lemma : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

theorem validated_set_inter_monotone_term : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

theorem validated_function_mem_range_lemma : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

theorem validated_function_comp_assoc_term : ∀ f g h : Real → Real, (f ∘ g) ∘ h = f ∘ (g ∘ h) := fun _ _ _ => rfl

theorem validated_function_comp_assoc_lemma : ∀ f g h : Real → Real, (f ∘ g) ∘ h = f ∘ (g ∘ h) := fun f g h => Function.comp_assoc f g h

theorem validated_integer_division_decomposition_lemma : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

theorem validated_integer_divisibility_lemma : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

theorem validated_finite_cardinality_decide : ({1, 2, 3} : Finset Nat).card = 3 := by decide

theorem validated_finite_cardinality_norm_num : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

theorem validated_powerset_cardinality_lemma : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

theorem validated_factorial_positive_lemma : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

theorem validated_derivative_square_at_three_chain : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

theorem validated_pair_reconstruction_term : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

theorem validated_pair_reconstruction_lemma : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

theorem validated_continuity_square_at_three_lemma : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#print axioms validated_sqrt_two_irrational_mathlib_theorem

#print axioms validated_sqrt_two_irrational_scratch

#print axioms validated_set_union_inter_distrib_lemma

#print axioms validated_set_union_inter_distrib_ext_simp

#print axioms validated_set_diff_union_ext_simp

#print axioms validated_set_inter_monotone_lemma

#print axioms validated_set_inter_monotone_term

#print axioms validated_function_mem_range_lemma

#print axioms validated_function_comp_assoc_term

#print axioms validated_function_comp_assoc_lemma

#print axioms validated_integer_division_decomposition_lemma

#print axioms validated_integer_divisibility_lemma

#print axioms validated_finite_cardinality_decide

#print axioms validated_finite_cardinality_norm_num

#print axioms validated_powerset_cardinality_lemma

#print axioms validated_factorial_positive_lemma

#print axioms validated_derivative_square_at_three_chain

#print axioms validated_pair_reconstruction_term

#print axioms validated_pair_reconstruction_lemma

#print axioms validated_continuity_square_at_three_lemma
