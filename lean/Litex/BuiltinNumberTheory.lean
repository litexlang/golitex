import Litex.Folds
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Lemmas

universe u v w x

namespace Litex

theorem dvdValueNumbers {M : Semantics.{u}} (a b : ℤ) :
    DvdValue M (M.number (a : ℂ)) (M.number (b : ℂ)) ↔ b ≠ 0 ∧ b ∣ a :=
  dvd_iff_of_denote (number (a : ℂ)) (number (b : ℂ)) a b rfl rfl

theorem gcdWithPrimeValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (p : Obj (M := M) β) (ha : In a Z)
    (_hpPos : In p NPos) (hp : Prime p) :
    gcdLcmValue false (denote a) (denote p) = M.number 1 ∨
      gcdLcmValue false (denote a) (denote p) = denote p := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp ha
  obtain ⟨n, hn, hprime⟩ := hp
  have hnI : denote p = M.number ((n : ℤ) : ℂ) := by simpa only [Int.cast_natCast] using hn
  have hdiv : Int.gcd z (n : ℤ) ∣ n := by
    simpa only [Int.natAbs_natCast] using Int.gcd_dvd_natAbs_right z (n : ℤ)
  rcases hprime.eq_one_or_self_of_dvd _ hdiv with hone | hself
  · left
    rw [hz, hnI, gcdLcmValue_numbers]
    change M.number (Int.gcd z (n : ℤ) : ℂ) = M.number 1
    rw [hone, Nat.cast_one]
  · right
    rw [hz, hnI, gcdLcmValue_numbers]
    change M.number (Int.gcd z (n : ℤ) : ℂ) = M.number ((n : ℤ) : ℂ)
    rw [hself, Int.cast_natCast]

theorem primeDividesProductValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hb : In b Z) (_hpPos : In p NPos) (hp : Prime p)
    (hdvd : DvdValue M (M.mulValue (denote a) (denote b)) (denote p)) :
    Dvd a p ∨ Dvd b p := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp ha
  obtain ⟨w, hw⟩ := (M.integer_members _).mp hb
  obtain ⟨n, hn, hprime⟩ := hp
  have hnI : denote p = M.number ((n : ℤ) : ℂ) := by simpa only [Int.cast_natCast] using hn
  have hdiv : (n : ℤ) ∣ z * w := by
    have h := hdvd
    rw [hz, hw, hnI, M.mul_numbers, ← Int.cast_mul, dvdValueNumbers] at h
    exact h.2
  have hprimeI : _root_.Prime (n : ℤ) := Nat.prime_iff_prime_int.mp hprime
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rcases hprimeI.2.2 z w hdiv with left | right
  · exact Or.inl ((dvd_iff_of_denote a p z n hz hnI).mpr ⟨hn0, left⟩)
  · exact Or.inr ((dvd_iff_of_denote b p w n hw hnI).mpr ⟨hn0, right⟩)

theorem primeDividesPowerValue {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (k : Obj (M := M) β) (p : Obj (M := M) γ)
    (ha : In a Z) (hk : In k NPos) (_hpPos : In p NPos) (hp : Prime p)
    (hdvd : DvdValue M (M.powValue (denote a) (denote k)) (denote p)) : Dvd a p := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp ha
  obtain ⟨m, hm⟩ := (M.natural_members _).mp (inNPos_natural k hk)
  obtain ⟨n, hn, hprime⟩ := hp
  have hnI : denote p = M.number ((n : ℤ) : ℂ) := by simpa only [Int.cast_natCast] using hn
  have hdiv : (n : ℤ) ∣ z ^ m := by
    have h := hdvd
    rw [hz, hm, hnI, M.pow_numbers_nat, ← Int.cast_pow, dvdValueNumbers] at h
    exact h.2
  have hprimeI : _root_.Prime (n : ℤ) := Nat.prime_iff_prime_int.mp hprime
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  exact (dvd_iff_of_denote a p z n hz hnI).mpr ⟨hn0, hprimeI.dvd_of_dvd_pow hdiv⟩

theorem primeDivisorWitness {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (m : Obj (M := M) α)
    (hm : In m NPos) (htwo : Le (number 2) m) :
    ∃ p : Obj (M := M) M.Value, ∃ _ : In p NPos, ∃ _ : Prime p,
      integerDivisionValue false (denote m) (denote p) = M.number 0 := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp (inNPos_natural m hm)
  have hnR : denote m = M.number ((n : ℝ) : ℂ) := by simpa only [Complex.ofReal_natCast] using hn
  have hnI : denote m = M.number ((n : ℤ) : ℂ) := by simpa only [Int.cast_natCast] using hn
  have hn2 : 2 ≤ n := by
    exact_mod_cast (NativeBridge.le_iff_ofDenoteReal (number 2) m 2 (n : ℝ) rfl hnR).mp htwo
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hmember := numberInNPosOfEq (M := M) (p : ℂ) p rfl hp.pos
  let value := semanticObject (M.number (p : ℂ)) (M.member_isSet hmember)
  have hprime : Prime value := ⟨p, rfl, hp⟩
  refine ⟨value, hmember, hprime, ?_⟩
  change integerDivisionValue false (denote m) (M.number (p : ℂ)) = M.number 0
  rw [hnI, show (p : ℂ) = ((p : ℤ) : ℂ) by norm_cast, integerDivisionValue_numbers]
  change M.number (((n : ℤ) % (p : ℤ) : ℤ) : ℂ) = M.number 0
  rw [Int.emod_eq_zero_of_dvd (by exact_mod_cast hdiv : (p : ℤ) ∣ (n : ℤ)), Int.cast_zero]


theorem primeInZ {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (hp : Prime p) : In p Z := by
  obtain ⟨n, hn, _⟩ := hp
  exact (M.integer_members _).mpr ⟨(n : ℤ), by simpa only [Int.cast_natCast] using hn⟩

theorem primeLowerBound {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) α) (hp : Prime p) : Le (number 2) p := by
  obtain ⟨n, hn, hprime⟩ := hp
  refine NativeBridge.leOfDenoteReal (number 2) p 2 (n : ℝ) rfl ?_ ?_
  · simpa only [Complex.ofReal_natCast] using hn
  · exact_mod_cast hprime.two_le

theorem primeTrialDivisors {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) α) (hp : Prime p) :
    ∀ d : Obj (M := M) M.Value,
      In d (range (number 2) p (NativeBridge.numberInZOfEq (M := M) 2 2 (by norm_num)) (primeInZ p hp)) →
      ¬ (integerDivisionValue false (denote p) (denote d) = M.number 0) := by
  obtain ⟨n, hn, hprime⟩ := hp
  have hnI : denote p = M.number ((n : ℤ) : ℂ) := by simpa only [Int.cast_natCast] using hn
  intro d hd
  obtain ⟨lower, upper, z, hl, hu, hz, hlo, hhi⟩ :=
    (inRange_iff (number 2) p d (NativeBridge.numberInZOfEq (M := M) 2 2 (by norm_num)) (primeInZ p ⟨n, hn, hprime⟩)).mp hd
  have hlEq : lower = 2 := by
    change M.number (2 : ℂ) = M.number (lower : ℂ) at hl
    exact_mod_cast (M.number_injective hl).symm
  have huEq : upper = (n : ℤ) := by exact_mod_cast M.number_injective (hu.symm.trans hnI)
  rw [hlEq] at hlo
  rw [huEq] at hhi
  intro hzero
  have hmod : (n : ℤ) % z = 0 := by
    rw [hnI, hz, integerDivisionValue_numbers] at hzero
    change M.number (((n : ℤ) % z : ℤ) : ℂ) = M.number 0 at hzero
    exact_mod_cast M.number_injective hzero
  have hdiv : z.natAbs ∣ n := Int.ofNat_dvd_right.mp (Int.dvd_of_emod_eq_zero hmod)
  have hznonneg : 0 ≤ z := le_trans (by decide : (0 : ℤ) ≤ 2) hlo
  have hzAbs : (z.natAbs : ℤ) = z := by rw [Int.natCast_natAbs, abs_of_nonneg hznonneg]
  rcases hprime.eq_one_or_self_of_dvd _ hdiv with hone | hself
  · have hzOne : z = 1 := hzAbs.symm.trans (congrArg (fun n : ℕ => (n : ℤ)) hone)
    omega
  · have hzSelf : z = (n : ℤ) := hzAbs.symm.trans (congrArg (fun n : ℕ => (n : ℤ)) hself)
    omega


theorem dvdFromRemainderAndMultiple {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (ModObj (M := M) α β)) (hzero : Same p (number 0))
    (_multiple : ∃ k : Obj (M := M) M.Value, ∃ _ : In k Z,
      denote p.val.left = M.mulValue (denote k) (denote p.val.right)) :
    Dvd p.val.left p.val.right := dvdOfModZero p hzero


theorem dvdConstructorWD {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Dvd a b) :
    In a Z ∧ In b Z ∧ ¬ Same b (number 0) := by
  obtain ⟨m, n, hm, hn, hn0, _⟩ := h
  refine ⟨(M.integer_members _).mpr ⟨m, hm⟩, (M.integer_members _).mpr ⟨n, hn⟩, ?_⟩
  intro heq
  apply hn0
  have heq : (n : ℂ) = 0 := M.number_injective (hn.symm.trans heq)
  exact_mod_cast heq

theorem dvdRemainderZero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Dvd a b) :
    integerDivisionValue false (denote a) (denote b) = M.number 0 := by
  obtain ⟨m, n, hm, hn, _, hdiv⟩ := h
  rw [hm, hn, integerDivisionValue_numbers]
  simp only [Bool.false_eq_true, if_false, Int.emod_eq_zero_of_dvd hdiv, Int.cast_zero]

theorem dvdIntegerMultiple {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Dvd a b) :
    ∃ k : Obj (M := M) M.Value, ∃ _ : In k Z,
      denote a = M.mulValue (denote k) (denote b) := by
  obtain ⟨m, n, hm, hn, _, hdiv⟩ := h
  obtain ⟨k, hk⟩ := hdiv
  have hmember : M.mem (M.number (k : ℂ)) (M.standard .integer) :=
    (M.integer_members _).mpr ⟨k, rfl⟩
  let value := semanticObject (M.number (k : ℂ)) (M.member_isSet hmember)
  refine ⟨value, hmember, ?_⟩
  change denote a = M.mulValue (M.number (k : ℂ)) (denote b)
  rw [hm, hn, M.mul_numbers]
  congr 1
  exact_mod_cast (show m = k * n by simpa only [mul_comm] using hk)


theorem reducedFractionCoordinates (q : ℚ) (m : ℤ) (d : ℕ)
    (hd : 0 < d) (hfrac : q = (m : ℚ) / (d : ℚ))
    (hred : Int.gcd m (d : ℤ) = 1) : m = q.num ∧ d = q.den := by
  have hdI : 0 < (d : ℤ) := by exact_mod_cast hd
  have hqden : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hdiv : q = Rat.divInt m (d : ℤ) := hfrac.trans (by
    simpa only [Int.cast_natCast] using Rat.intCast_div_eq_divInt m (d : ℤ))
  obtain ⟨c, hm, hdc⟩ := Rat.num_den_mk (ne_of_gt hdI) hdiv
  have hgcd : Int.gcd q.num (q.den : ℤ) = 1 := by
    simpa only [Int.gcd, Int.natAbs_natCast] using q.reduced.gcd_eq_one
  have hcabs : c.natAbs = 1 := by
    rw [hm, hdc, Int.gcd_mul_left, hgcd, mul_one] at hred
    exact hred
  have hcpos : 0 < c := (mul_pos_iff_of_pos_right hqden).mp (hdc ▸ hdI)
  have hc : c = 1 := by
    have h := Int.natAbs_of_nonneg (le_of_lt hcpos)
    rw [hcabs] at h
    exact h.symm
  constructor
  · simpa only [hc, one_mul] using hm
  · exact_mod_cast (show (d : ℤ) = (q.den : ℤ) by simpa only [hc, one_mul] using hdc)

theorem rationalReducedFractionWitness {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (x : Obj (M := M) α) (hx : In x Q) :
    ∃ p : Obj (M := M) M.Value, ∃ _ : In p Z,
      ∃ d : Obj (M := M) M.Value, ∃ _ : In d NPos,
        denote x = M.divValue (denote p) (denote d) ∧
          gcdLcmValue false (denote p) (denote d) = M.number 1 := by
  obtain ⟨q, hq⟩ := (M.rational_members _).mp hx
  have hpZ : M.mem (M.number (q.num : ℂ)) (M.standard .integer) :=
    (M.integer_members _).mpr ⟨q.num, rfl⟩
  have hdPos := numberInNPosOfEq (M := M) (q.den : ℂ) q.den rfl q.den_pos
  let p := semanticObject (M.number (q.num : ℂ)) (M.member_isSet hpZ)
  let d := semanticObject (M.number (q.den : ℂ)) (M.member_isSet hdPos)
  refine ⟨p, hpZ, d, hdPos, ?_, ?_⟩
  · have hd0 : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    change denote x = M.divValue (M.number (q.num : ℂ)) (M.number (q.den : ℂ))
    rw [hq, M.div_numbers _ _ hd0, Rat.cast_def]
  · have hred : Int.gcd q.num (q.den : ℤ) = 1 := by
      simpa only [Int.gcd, Int.natAbs_natCast] using q.reduced.gcd_eq_one
    change gcdLcmValue false (M.number (q.num : ℂ)) (M.number (q.den : ℂ)) = M.number 1
    rw [show (q.den : ℂ) = ((q.den : ℤ) : ℂ) by norm_cast, gcdLcmValue_numbers]
    simp only [Bool.false_eq_true, if_false, hred, Nat.cast_one]

theorem reducedFractionValues {M : Semantics.{u}} [SetSemantics M]
    (q : ℚ) (p d : Obj (M := M) M.Value) (hp : In p Z) (hd : In d NPos)
    (hfrac : M.number (q : ℂ) = M.divValue (denote p) (denote d))
    (hred : gcdLcmValue false (denote p) (denote d) = M.number 1) :
    denote p = M.number (q.num : ℂ) ∧ denote d = M.number (q.den : ℂ) := by
  obtain ⟨m, hm⟩ := (M.integer_members _).mp hp
  obtain ⟨n, hn⟩ := (M.natural_members _).mp (inNPos_natural d hd)
  have hnR : denote d = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hnPos : 0 < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal (number 0) d 0 (n : ℝ) rfl hnR).mp
      (inNPos_positive d hd)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnPos)
  have hcomplex : (q : ℂ) = (m : ℂ) / (n : ℂ) := by
    apply M.number_injective
    simpa only [hm, hn, M.div_numbers _ _ hn0] using hfrac
  have hqfrac : q = (m : ℚ) / (n : ℚ) := by exact_mod_cast hcomplex
  have hcast : (n : ℂ) = ((n : ℤ) : ℂ) := by norm_cast
  rw [hm, hn, hcast, gcdLcmValue_numbers] at hred
  simp only [Bool.false_eq_true, if_false] at hred
  have hredI : Int.gcd m (n : ℤ) = 1 := by exact_mod_cast (M.number_injective hred)
  obtain ⟨hnum, hden⟩ := reducedFractionCoordinates q m n hnPos hqfrac hredI
  exact ⟨by simpa only [hnum] using hm, by simpa only [hden] using hn⟩

theorem rationalReducedFractionUniqueness {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (x : Obj (M := M) α) (hx : In x Q) :
    ∀ (p : Obj (M := M) M.Value) (_hp : In p Z)
      (d : Obj (M := M) M.Value) (_hd : In d NPos)
      (p' : Obj (M := M) M.Value) (_hp' : In p' Z)
      (d' : Obj (M := M) M.Value) (_hd' : In d' NPos)
      (_hfrac : denote x = M.divValue (denote p) (denote d))
      (_hfrac' : denote x = M.divValue (denote p') (denote d'))
      (_hred : gcdLcmValue false (denote p) (denote d) = M.number 1)
      (_hred' : gcdLcmValue false (denote p') (denote d') = M.number 1),
      FiniteFunction.tupleValue (M := M) ![denote p, denote d] =
        FiniteFunction.tupleValue (M := M) ![denote p', denote d'] := by
  intro p hp d hd p' hp' d' hd' hfrac hfrac' hred hred'
  obtain ⟨q, hq⟩ := (M.rational_members _).mp hx
  have left := reducedFractionValues q p d hp hd (hq.symm.trans hfrac) hred
  have right := reducedFractionValues q p' d' hp' hd' (hq.symm.trans hfrac') hred'
  have hpEq : denote p = denote p' := left.1.trans right.1.symm
  have hdEq : denote d = denote d' := left.2.trans right.2.symm
  apply congrArg (FiniteFunction.tupleValue (M := M))
  funext i
  fin_cases i
  · exact hpEq
  · exact hdEq


theorem remainderUnitValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ModObj (M := M) α β))
    (hunit : Same p.val.right (number 1)) : Same p (number 0) := by
  obtain ⟨z,hz⟩ := (M.integer_members _).mp p.wd.1
  change denote p.val.right = M.number 1 at hunit
  change integerDivisionValue false (denote p.val.left) (denote p.val.right) = M.number 0
  rw [hz,hunit,show (1 : ℂ) = ((1 : ℤ) : ℂ) by norm_num,integerDivisionValue_numbers]
  simp


end Litex
