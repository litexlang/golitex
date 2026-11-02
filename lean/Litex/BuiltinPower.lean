import Litex.SetFunctions
universe u v w x
namespace Litex

theorem onePowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hb : Same p.val.base (number 1)) : Same p (number 1) := by
  change denote p.val.base = M.number 1 at hb
  change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 1
  rcases p.wd with ⟨_, n, _, he⟩ | ⟨_, n, _, he⟩ | ⟨_, z, _, _, he⟩
  · change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hb, he, M.pow_numbers_nat, one_pow]
  · change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hb, he, M.pow_numbers_nat, one_pow]
  · change denote p.val.exponent = M.number (z : ℂ) at he
    rw [hb, he, M.pow_numbers_int 1 z one_ne_zero, one_zpow]

theorem zeroPositiveNaturalPowerValue {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hb : Same p.val.base (number 0)) (he : In p.val.exponent NPos) : Same p (number 0) := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp (inNPos_natural p.val.exponent he)
  have hnpos : (0 : ℝ) < n := (NativeBridge.lt_iff_ofDenoteReal
    (number 0) p.val.exponent 0 n rfl (by simpa only [Complex.ofReal_natCast] using hn)).mp
      (inNPos_positive p.val.exponent he)
  have hn0 : n ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  change denote p.val.base = M.number 0 at hb
  change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 0
  rw [hb, hn, M.pow_numbers_nat, zero_pow hn0]

theorem negativeIntegerPowerReciprocalValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β)
    (ha : In a C) (he : In e Z) (ha0 : ¬ Same a (number 0)) :
    M.powValue (denote a) (M.negValue (denote e)) =
      M.divValue (M.number 1) (M.powValue (denote a) (denote e)) := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp he
  obtain ⟨c, hc⟩ := (M.complex_members _).mp ha
  have hc0 : c ≠ 0 := fun h => ha0 (hc.trans (congrArg M.number h))
  rw [hc, hz, M.neg_numbers, ← Int.cast_neg, M.pow_numbers_int c (-z) hc0,
    M.pow_numbers_int c z hc0, M.div_numbers 1 (c ^ z) (zpow_ne_zero _ hc0), zpow_neg, one_div]

theorem reciprocalNegativeOnePowerValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (e : Obj (M := M) β)
    (ha : In a C) (ha0 : ¬ Same a (number 0)) (he : Same e (number (-1))) :
    M.divValue (M.number 1) (denote a) = M.powValue (denote a) (denote e) := by
  obtain ⟨c, hc⟩ := (M.complex_members _).mp ha
  have hc0 : c ≠ 0 := fun h => ha0 (hc.trans (congrArg M.number h))
  change denote e = M.number (-1) at he
  rw [hc, he, M.div_numbers 1 c hc0]
  have hn : (-1 : ℂ) = ((-1 : ℤ) : ℂ) := by norm_num
  rw [hn, M.pow_numbers_int c (-1) hc0, zpow_neg_one, one_div]

theorem quotientNegativeOnePowerValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (e : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hb0 : ¬ Same b (number 0)) (he : Same e (number (-1))) :
    M.divValue (denote a) (denote b) =
      M.mulValue (denote a) (M.powValue (denote b) (denote e)) := by
  obtain ⟨c, hc⟩ := (M.complex_members _).mp ha
  obtain ⟨d, hd⟩ := (M.complex_members _).mp hb
  have hd0 : d ≠ 0 := fun h => hb0 (hd.trans (congrArg M.number h))
  change denote e = M.number (-1) at he
  rw [hc, hd, he, M.div_numbers c d hd0]
  have hn : (-1 : ℂ) = ((-1 : ℤ) : ℂ) := by norm_num
  rw [hn, M.pow_numbers_int d (-1) hd0, M.mul_numbers, zpow_neg_one, div_eq_mul_inv]

theorem naturalPowerProductValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (e : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (he : In e N) :
    M.powValue (M.mulValue (denote a) (denote b)) (denote e) =
      M.mulValue (M.powValue (denote a) (denote e)) (M.powValue (denote b) (denote e)) := by
  obtain ⟨c, hc⟩ := (M.complex_members _).mp ha
  obtain ⟨d, hd⟩ := (M.complex_members _).mp hb
  obtain ⟨n, hn⟩ := (M.natural_members _).mp he
  rw [hc, hd, hn, M.mul_numbers, M.pow_numbers_nat, M.pow_numbers_nat,
    M.pow_numbers_nat, M.mul_numbers, mul_pow]


theorem zeroPositiveExponentPowerValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hb : Same p.val.base (number 0)) (he : In p.val.exponent RPos) : Same p (number 0) := by
  have hpos := inRPos_positive p.val.exponent he
  change denote p.val.base = M.number 0 at hb
  rcases p.wd with ⟨_, n, _, hn⟩ | ⟨_, n, _, hn⟩ | ⟨_, _, _, ha0, _⟩
  · change denote p.val.exponent = M.number (n : ℂ) at hn
    have hnpos : (0 : ℝ) < n := (NativeBridge.lt_iff_ofDenoteReal
      (number 0) p.val.exponent 0 n rfl (by simpa only [Complex.ofReal_natCast] using hn)).mp hpos
    have hn0 : n ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 0
    rw [hb, hn, M.pow_numbers_nat, zero_pow hn0]
  · change denote p.val.exponent = M.number (n : ℂ) at hn
    have hnpos : (0 : ℝ) < n := (NativeBridge.lt_iff_ofDenoteReal
      (number 0) p.val.exponent 0 n rfl (by simpa only [Complex.ofReal_natCast] using hn)).mp hpos
    have hn0 : n ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = M.number 0
    rw [hb, hn, M.pow_numbers_nat, zero_pow hn0]
  · exact False.elim (ha0 hb)



theorem positiveIntegerPowerCancellationValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (e : Obj (M := M) γ)
    (ha : In a RPos) (hb : In b RPos) (he : In e Z) (he0 : ¬ Same e (number 0))
    (hp : M.powValue (denote a) (denote e) = M.powValue (denote b) (denote e)) : Same a b := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp (inRPos_real a ha)
  obtain ⟨s,hs⟩ := (M.real_members _).mp (inRPos_real b hb)
  obtain ⟨z,hz⟩ := (M.integer_members _).mp he
  have hrpos := (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp (inRPos_positive a ha)
  have hspos := (NativeBridge.lt_iff_ofDenoteReal (number 0) b 0 s rfl hs).mp (inRPos_positive b hb)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hspos)
  have hz0 : z ≠ 0 := by
    intro hzero
    apply he0
    change denote e = M.number 0
    simpa only [hzero, Int.cast_zero] using hz
  rw [hr,hs,hz,M.pow_numbers_int _ _ hrC,M.pow_numbers_int _ _ hsC,
    ← Complex.ofReal_zpow, ← Complex.ofReal_zpow] at hp
  have hrs : r ^ z = s ^ z := Complex.ofReal_injective (M.number_injective hp)
  have hsame := (zpow_left_inj₀ (le_of_lt hrpos) (le_of_lt hspos) hz0).mp hrs
  change denote a = denote b
  rw [hr,hs,hsame]



theorem integerPowerProductValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (ha : In a C) (ha0 : ¬ Same a (number 0)) (hm : In m Z) (hn : In n Z) :
    M.mulValue (M.powValue (denote a) (denote m)) (M.powValue (denote a) (denote n)) =
      M.powValue (denote a) (M.addValue (denote m) (denote n)) := by
  obtain ⟨c,hc⟩ := (M.complex_members _).mp ha
  obtain ⟨i,hi⟩ := (M.integer_members _).mp hm
  obtain ⟨j,hj⟩ := (M.integer_members _).mp hn
  have hc0 : c ≠ 0 := fun h => ha0 (hc.trans (congrArg M.number h))
  rw [hc,hi,hj,M.pow_numbers_int c i hc0,M.pow_numbers_int c j hc0,M.mul_numbers,
    M.add_numbers,←Int.cast_add,M.pow_numbers_int c (i+j) hc0]
  exact congrArg M.number (zpow_add₀ hc0 i j).symm

theorem integerPowerOfPowerValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (ha : In a C) (ha0 : ¬ Same a (number 0)) (hm : In m Z) (hn : In n Z) :
    M.powValue (M.powValue (denote a) (denote m)) (denote n) =
      M.powValue (denote a) (M.mulValue (denote m) (denote n)) := by
  obtain ⟨c,hc⟩ := (M.complex_members _).mp ha
  obtain ⟨i,hi⟩ := (M.integer_members _).mp hm
  obtain ⟨j,hj⟩ := (M.integer_members _).mp hn
  have hc0 : c ≠ 0 := fun h => ha0 (hc.trans (congrArg M.number h))
  rw [hc,hi,hj,M.pow_numbers_int c i hc0,M.pow_numbers_int (c^i) j (zpow_ne_zero _ hc0),
    M.mul_numbers,←Int.cast_mul,M.pow_numbers_int c (i*j) hc0]
  exact congrArg M.number (zpow_mul c i j).symm

theorem integerPowerProductDistributionValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (n : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hn : In n Z)
    (ha0 : ¬ Same a (number 0)) (hb0 : ¬ Same b (number 0)) :
    M.powValue (M.mulValue (denote a) (denote b)) (denote n) =
      M.mulValue (M.powValue (denote a) (denote n)) (M.powValue (denote b) (denote n)) := by
  obtain ⟨c,hc⟩ := (M.complex_members _).mp ha
  obtain ⟨d,hd⟩ := (M.complex_members _).mp hb
  obtain ⟨i,hi⟩ := (M.integer_members _).mp hn
  have hc0 : c ≠ 0 := fun h => ha0 (hc.trans (congrArg M.number h))
  have hd0 : d ≠ 0 := fun h => hb0 (hd.trans (congrArg M.number h))
  rw [hc,hd,hi,M.mul_numbers,M.pow_numbers_int (c*d) i (mul_ne_zero hc0 hd0),
    M.pow_numbers_int c i hc0,M.pow_numbers_int d i hd0,M.mul_numbers,mul_zpow]


end Litex
