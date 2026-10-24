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

#probe "sqrt_two_irrational__scratch__first" theorem initial_sqrt_two_irrational_scratch : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_0 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_1 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_2 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_3 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_4 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_5 : Irrational (Real.sqrt 2) := by
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

#probe "sqrt_two_irrational__scratch" theorem sample_sqrt_two_irrational_scratch_6 : Irrational (Real.sqrt 2) := by
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

#probe "set_union_inter_distrib__lemma__first" theorem initial_set_union_inter_distrib_lemma : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__ext_simp__first" theorem initial_set_union_inter_distrib_ext_simp : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_0 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_1 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_2 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_3 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_4 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_5 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__lemma" theorem sample_set_union_inter_distrib_lemma_6 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := fun A B D => Set.union_inter_distrib_left A B D

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_0 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_1 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_2 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_3 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_4 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_5 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_union_inter_distrib__ext_simp" theorem sample_set_union_inter_distrib_ext_simp_6 : ∀ A B D : Set Real, A ∪ (B ∩ D) = (A ∪ B) ∩ (A ∪ D) := by intro A B D; ext x; simp [Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp__first" theorem initial_set_diff_union_ext_simp : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_0 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_1 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_2 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_3 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_4 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_5 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_diff_union__ext_simp" theorem sample_set_diff_union_ext_simp_6 : ∀ A B D : Set Real, A \ (B ∪ D) = (A \ B) ∩ (A \ D) := by intro A B D; ext x; simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]; tauto

#probe "set_inter_monotone__lemma__first" theorem initial_set_inter_monotone_lemma : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__term__first" theorem initial_set_inter_monotone_term : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_0 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_1 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_2 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_3 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_4 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_5 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__lemma" theorem sample_set_inter_monotone_lemma_6 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h => Set.inter_subset_inter_left D h

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_0 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_1 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_2 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_3 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_4 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_5 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "set_inter_monotone__term" theorem sample_set_inter_monotone_term_6 : ∀ A B D : Set Real, A ⊆ B → A ∩ D ⊆ B ∩ D := fun A B D h x hx => ⟨h hx.1, hx.2⟩

#probe "function_mem_range__lemma__first" theorem initial_function_mem_range_lemma : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_0 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_1 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_2 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_3 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_4 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_5 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "function_mem_range__lemma" theorem sample_function_mem_range_lemma_6 : ∀ (f : Real → Real) (x : Real), f x ∈ Set.range f := fun f x => Set.mem_range_self x

#probe "integer_division_decomposition__lemma__first" theorem initial_integer_division_decomposition_lemma : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_0 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_1 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_2 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_3 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_4 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_5 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_division_decomposition__lemma" theorem sample_integer_division_decomposition_lemma_6 : ∀ (a : Int) (d : Nat), 0 < d → a = (d : Int) * (a / (d : Int)) + a % (d : Int) := fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

#probe "integer_divisibility__lemma__first" theorem initial_integer_divisibility_lemma : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_0 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_1 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_2 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_3 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_4 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_5 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "integer_divisibility__lemma" theorem sample_integer_divisibility_lemma_6 : ∀ (a : Int) (c : Int), c ≠ 0 → c ∣ a * c := fun a c _ => dvd_mul_left c a

#probe "finite_cardinality__decide__first" theorem initial_finite_cardinality_decide : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__norm_num__first" theorem initial_finite_cardinality_norm_num : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_0 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_1 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_2 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_3 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_4 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_5 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__decide" theorem sample_finite_cardinality_decide_6 : ({1, 2, 3} : Finset Nat).card = 3 := by decide

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_0 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_1 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_2 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_3 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_4 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_5 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "finite_cardinality__norm_num" theorem sample_finite_cardinality_norm_num_6 : ({1, 2, 3} : Finset Nat).card = 3 := by norm_num

#probe "powerset_cardinality__lemma__first" theorem initial_powerset_cardinality_lemma : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_0 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_1 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_2 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_3 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_4 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_5 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "powerset_cardinality__lemma" theorem sample_powerset_cardinality_lemma_6 : ∀ s : Finset Nat, s.powerset.card = 2 ^ s.card := fun s => Finset.card_powerset s

#probe "factorial_positive__lemma__first" theorem initial_factorial_positive_lemma : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_0 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_1 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_2 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_3 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_4 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_5 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "factorial_positive__lemma" theorem sample_factorial_positive_lemma_6 : ∀ n : Nat, 0 < n.factorial := fun n => Nat.factorial_pos n

#probe "derivative_square_at_three__chain__first" theorem initial_derivative_square_at_three_chain : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_0 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_1 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_2 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_3 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_4 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_5 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "derivative_square_at_three__chain" theorem sample_derivative_square_at_three_chain_6 : HasDerivAt (fun t : Real => t ^ 2) 6 3 := by
  have h : HasDerivAt (fun t : Real => t ^ 2) ((2 : Real) * 3 ^ (2 - 1)) 3 := hasDerivAt_pow 2 3
  refine h.congr_deriv ?_
  norm_num

#probe "pair_reconstruction__term__first" theorem initial_pair_reconstruction_term : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__lemma__first" theorem initial_pair_reconstruction_lemma : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_0 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_1 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_2 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_3 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_4 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_5 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__term" theorem sample_pair_reconstruction_term_6 : ∀ p : Real × Real, (p.1, p.2) = p := fun _ => rfl

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_0 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_1 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_2 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_3 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_4 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_5 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "pair_reconstruction__lemma" theorem sample_pair_reconstruction_lemma_6 : ∀ p : Real × Real, (p.1, p.2) = p := fun p => Prod.mk.eta (p := p)

#probe "continuity_square_at_three__lemma__first" theorem initial_continuity_square_at_three_lemma : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_0 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_1 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_2 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_3 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_4 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_5 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2

#probe "continuity_square_at_three__lemma" theorem sample_continuity_square_at_three_lemma_6 : ContinuousAt (fun x : Real => x ^ 2) 3 := continuousAt_pow (3 : Real) 2
