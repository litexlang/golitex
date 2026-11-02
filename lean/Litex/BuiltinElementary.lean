import Litex.OrderedArithmetic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

universe u

namespace Litex

theorem minMaxAssociativeValue {M : Semantics.{u}} (maximum : Bool) (a b c : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (hc : M.mem c (M.standard .real)) :
    minMaxValue maximum (minMaxValue maximum a b) c =
      minMaxValue maximum a (minMaxValue maximum b c) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  obtain ⟨t, ht⟩ := (M.real_members _).mp hc
  rw [hr, hs, ht]
  cases maximum <;>
    simp only [minMaxValue_number, Bool.false_eq_true, if_false, if_true, min_assoc, max_assoc]

theorem minMaxSumValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (minFirst reverseArgs : Bool) :
    (if minFirst then M.addValue (minMaxValue false a b) (minMaxValue true a b)
      else M.addValue (minMaxValue true a b) (minMaxValue false a b)) =
    (if reverseArgs then M.addValue b a else M.addValue a b) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  rw [hr, hs]
  have h := congrArg (fun x : ℝ => M.number (x : ℂ)) (min_add_max r s)
  cases minFirst <;> cases reverseArgs <;>
    simpa only [minMaxValue_number, Bool.false_eq_true, if_false, if_true,
      M.add_numbers, ← Complex.ofReal_add, add_comm] using h

theorem minMaxProductValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (minFirst reverseArgs : Bool) :
    (if minFirst then M.mulValue (minMaxValue false a b) (minMaxValue true a b)
      else M.mulValue (minMaxValue true a b) (minMaxValue false a b)) =
    (if reverseArgs then M.mulValue b a else M.mulValue a b) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  rw [hr, hs]
  have h := congrArg (fun x : ℝ => M.number (x : ℂ)) (min_mul_max r s)
  cases minFirst <;> cases reverseArgs <;>
    simpa only [minMaxValue_number, Bool.false_eq_true, if_false, if_true,
      M.mul_numbers, ← Complex.ofReal_mul, mul_comm] using h

theorem minTranslationValue {M : Semantics.{u}} (a b c : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (hc : M.mem c (M.standard .real)) :
    minMaxValue false (M.addValue a c) (M.addValue b c) =
      M.addValue (minMaxValue false a b) c := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  obtain ⟨t, ht⟩ := (M.real_members _).mp hc
  rw [hr, hs, ht]
  simp only [M.add_numbers, ← Complex.ofReal_add, minMaxValue_number,
    Bool.false_eq_true, if_false, min_add_add_right]

theorem maxNegationValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real)) :
    minMaxValue true (M.negValue a) (M.negValue b) =
      M.negValue (minMaxValue false a b) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  obtain ⟨s, hs⟩ := (M.real_members _).mp hb
  rw [hr, hs]
  simp only [M.neg_numbers, ← Complex.ofReal_neg, minMaxValue_number,
    Bool.false_eq_true, if_false, if_true, max_neg_neg]


theorem floorFromIntegerBounds {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RoundingObj (M := M) false α)) (n : Obj (M := M) β)
    (hn : In n Z) (hweak : Le n p.val.arg)
    (hstrict : Lt p.val.arg (add n (number 1) (integerToComplex n hn) (numberInC 1))) :
    Same p n := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  obtain ⟨z, hz⟩ := (M.integer_members _).mp hn
  have hzR : denote n = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  have hsum : denote (add n (number 1) (integerToComplex n hn) (numberInC 1)) =
      M.number (((z : ℝ) + 1 : ℝ) : ℂ) := by
    change M.addValue (denote n) (M.number 1) = _
    rw [hz, M.add_numbers, Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_one]
  have hlo : (z : ℝ) ≤ r := (NativeBridge.le_iff_ofDenoteReal _ _ _ _ hzR hr).mp hweak
  have hhi : r < (z : ℝ) + 1 := (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hr hsum).mp hstrict
  have heq : Int.floor r = z := Int.floor_eq_iff.mpr ⟨hlo, hhi⟩
  change denote p = denote n
  rw [roundingDenoteReal p r hr, hz]
  change M.number ((Int.floor r : ℤ) : ℂ) = M.number (z : ℂ)
  rw [heq]

theorem ceilFromIntegerBounds {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RoundingObj (M := M) true α)) (n : Obj (M := M) β)
    (hn : In n Z) (hweak : Le p.val.arg n)
    (hstrict : Lt (sub n (number 1) (integerToComplex n hn) (numberInC 1)) p.val.arg) :
    Same p n := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  obtain ⟨z, hz⟩ := (M.integer_members _).mp hn
  have hzR : denote n = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  have hsub : denote (sub n (number 1) (integerToComplex n hn) (numberInC 1)) =
      M.number (((z : ℝ) - 1 : ℝ) : ℂ) := by
    change M.subValue (denote n) (M.number 1) = _
    rw [hz, M.sub_numbers, Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_one]
  have hlo : (z : ℝ) - 1 < r := (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hsub hr).mp hstrict
  have hhi : r ≤ (z : ℝ) := (NativeBridge.le_iff_ofDenoteReal _ _ _ _ hr hzR).mp hweak
  have heq : Int.ceil r = z := Int.ceil_eq_iff.mpr ⟨hlo, hhi⟩
  change denote p = denote n
  rw [roundingDenoteReal p r hr, hz]
  change M.number ((Int.ceil r : ℤ) : ℂ) = M.number (z : ℂ)
  rw [heq]


theorem gcdAddArgumentValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer))
    (reverse : Bool) :
    gcdLcmValue false (if reverse then M.addValue b a else M.addValue a b) b =
      gcdLcmValue false a b := by
  obtain ⟨x, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨y, rfl⟩ := (M.integer_members _).mp hb
  cases reverse
  · change gcdLcmValue false (M.addValue (M.number (x : ℂ)) (M.number (y : ℂ))) _ = _
    rw [M.add_numbers, ← Int.cast_add, gcdLcmValue_numbers, gcdLcmValue_numbers]
    change M.number (Int.gcd (x + y) y : ℂ) = M.number (Int.gcd x y : ℂ)
    rw [Int.gcd_add_self_left]
  · change gcdLcmValue false (M.addValue (M.number (y : ℂ)) (M.number (x : ℂ))) _ = _
    rw [M.add_numbers, ← Int.cast_add, gcdLcmValue_numbers, gcdLcmValue_numbers]
    change M.number (Int.gcd (y + x) y : ℂ) = M.number (Int.gcd x y : ℂ)
    rw [Int.add_comm y x, Int.gcd_add_self_left]

theorem gcdNegationValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer)) :
    gcdLcmValue false (M.negValue a) b = gcdLcmValue false a b := by
  obtain ⟨x, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨y, rfl⟩ := (M.integer_members _).mp hb
  rw [M.neg_numbers, ← Int.cast_neg, gcdLcmValue_numbers, gcdLcmValue_numbers]
  change M.number (Int.gcd (-x) y : ℂ) = M.number (Int.gcd x y : ℂ)
  rw [Int.neg_gcd]

theorem gcdPositiveScaleValue {M : Semantics.{u}} [S : SetSemantics M]
    (a b k : M.Value) (ha : M.mem a (denote (NPos (M := M))))
    (hb : M.mem b (denote (NPos (M := M))))
    (hk : M.mem k (denote (NPos (M := M)))) :
    gcdLcmValue false (M.mulValue k a) (M.mulValue k b) =
      M.mulValue k (gcdLcmValue false a b) := by
  obtain ⟨x, hx⟩ := (M.natural_members _).mp ((S.sep_members _ _ _).mp ha).1
  obtain ⟨y, hy⟩ := (M.natural_members _).mp ((S.sep_members _ _ _).mp hb).1
  obtain ⟨z, hz⟩ := (M.natural_members _).mp ((S.sep_members _ _ _).mp hk).1
  have castNat (n : ℕ) : (n : ℂ) = ((n : ℤ) : ℂ) := by norm_cast
  rw [hx, hy, hz, M.mul_numbers, M.mul_numbers,
    ← Nat.cast_mul, ← Nat.cast_mul, castNat (z * x), castNat (z * y),
    castNat x, castNat y, gcdLcmValue_numbers, gcdLcmValue_numbers, M.mul_numbers]
  change M.number (Int.gcd ((z * x : ℕ) : ℤ) ((z * y : ℕ) : ℤ) : ℂ) =
    M.number ((z : ℂ) * (Int.gcd (x : ℤ) (y : ℤ) : ℂ))
  rw [Nat.cast_mul, Nat.cast_mul, Int.gcd_mul_left]
  congr 1
  norm_cast

theorem remainderIntegerShiftValue {M : Semantics.{u}} (a k m : M.Value)
    (ha : M.mem a (M.standard .integer)) (hk : M.mem k (M.standard .integer))
    (hm : M.mem m (M.standard .integer)) :
    integerDivisionValue false (M.addValue a (M.mulValue k m)) m =
      integerDivisionValue false a m := by
  obtain ⟨x, rfl⟩ := (M.integer_members _).mp ha
  obtain ⟨y, rfl⟩ := (M.integer_members _).mp hk
  obtain ⟨z, rfl⟩ := (M.integer_members _).mp hm
  rw [M.mul_numbers, ← Int.cast_mul, M.add_numbers, ← Int.cast_add,
    integerDivisionValue_numbers, integerDivisionValue_numbers]
  change M.number (((x + y * z) % z : ℤ) : ℂ) = M.number ((x % z : ℤ) : ℂ)
  rw [Int.add_mul_emod_self_right]


theorem rationalPositiveRatioWitness {M : Semantics.{u}}
    {α : Type v} [Representation M α] (q : Obj (M := M) α) (hq : In q Q) :
    ∃ a : Obj (M := M) M.Value, ∃ _ : In a Z,
      ∃ b : Obj (M := M) M.Value, ∃ _ : In b Z,
        ∃ _ : Lt (number 0) b, denote q = M.divValue (denote a) (denote b) := by
  obtain ⟨r, hr⟩ := (M.rational_members _).mp hq
  have ha := NativeBridge.numberInZOfEq (M := M) (r.num : ℂ) r.num rfl
  have hb := NativeBridge.numberInZOfEq (M := M) (r.den : ℂ) (r.den : ℤ) (by norm_cast)
  let a := semanticObject (M.number (r.num : ℂ)) (M.member_isSet ha)
  let b := semanticObject (M.number (r.den : ℂ)) (M.member_isSet hb)
  have hbR : denote b = M.number ((r.den : ℝ) : ℂ) := by
    change M.number (r.den : ℂ) = M.number ((r.den : ℝ) : ℂ)
    rw [Complex.ofReal_natCast]
  have hpos : Lt (number (M := M) 0) b :=
    NativeBridge.ltOfDenoteReal (number 0) b 0 (r.den : ℝ) rfl hbR (by exact_mod_cast r.den_pos)
  refine ⟨a, ha, b, hb, hpos, ?_⟩
  change denote q = M.divValue (M.number (r.num : ℂ)) (M.number (r.den : ℂ))
  rw [hr, M.div_numbers _ _ (by exact_mod_cast r.den_nz), Rat.cast_def]

theorem rationalIntegerRatioWitness {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (q : Obj (M := M) α) (hq : In q Q) :
    ∃ a : Obj (M := M) M.Value, ∃ _ : In a Z,
      ∃ b : Obj (M := M) M.Value, ∃ _ : In b ZStar,
        denote q = M.divValue (denote a) (denote b) := by
  obtain ⟨a, ha, b, hb, hpos, heq⟩ := rationalPositiveRatioWitness q hq
  have hnonzero : ¬ Same b (number 0) := fun heq => (ltNotSame (number 0) b hpos) heq.symm
  exact ⟨a, ha, b, inZStar_intro b hb hnonzero, heq⟩

theorem integerMultipleFromZeroRemainder {M : Semantics.{u}}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) (_hb0 : ¬ Same b (number 0))
    (hmod : integerDivisionValue false (denote a) (denote b) = M.number 0) (reverse : Bool) :
    ∃ k : Obj (M := M) M.Value, ∃ _ : In k Z,
      denote a = (if reverse then M.mulValue (denote k) (denote b)
        else M.mulValue (denote b) (denote k)) := by
  obtain ⟨x, hx⟩ := (M.integer_members _).mp ha
  obtain ⟨y, hy⟩ := (M.integer_members _).mp hb
  have hzero : x % y = 0 := by
    have h := hmod
    rw [hx, hy, integerDivisionValue_numbers] at h
    change M.number ((x % y : ℤ) : ℂ) = M.number 0 at h
    exact_mod_cast M.number_injective h
  have hmultiple : x = y * (x / y) := by
    have h := Int.emod_add_ediv_mul x y
    rw [hzero, Int.zero_add, Int.mul_comm] at h
    exact h.symm
  have hmember := NativeBridge.numberInZOfEq (M := M) ((x / y : ℤ) : ℂ) (x / y) rfl
  let value := semanticObject (M.number ((x / y : ℤ) : ℂ)) (M.member_isSet hmember)
  refine ⟨value, hmember, ?_⟩
  cases reverse
  · change denote a = M.mulValue (denote b) (M.number ((x / y : ℤ) : ℂ))
    rw [hx, hy, M.mul_numbers, ← Int.cast_mul, ← hmultiple]
  · change denote a = M.mulValue (M.number ((x / y : ℤ) : ℂ)) (denote b)
    rw [hx, hy, M.mul_numbers, ← Int.cast_mul, Int.mul_comm (x / y) y, ← hmultiple]

theorem roundingNegationValue {M : Semantics.{u}} (ceiling : Bool) (a : M.Value)
    (ha : M.mem a (M.standard .real)) :
    roundingValue ceiling (M.negValue a) = M.negValue (roundingValue (!ceiling) a) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  rw [hr,M.neg_numbers,←Complex.ofReal_neg,roundingValue_number,roundingValue_number]
  cases ceiling <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,
    if_false,if_true,Int.floor_neg,Int.ceil_neg,M.neg_numbers,Int.cast_neg]

theorem roundingIntegerTranslationValue {M : Semantics.{u}} (ceiling : Bool)
    (a n : M.Value) (ha : M.mem a (M.standard .real))
    (hn : M.mem n (M.standard .integer)) (reverseInput reverseOutput : Bool) :
    roundingValue ceiling (if reverseInput then M.addValue n a else M.addValue a n) =
      (if reverseOutput then M.addValue n (roundingValue ceiling a)
        else M.addValue (roundingValue ceiling a) n) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  obtain ⟨z,hz⟩ := (M.integer_members _).mp hn
  have hzR : n = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  rw [hr,hzR]
  cases ceiling <;> cases reverseInput <;> cases reverseOutput <;>
    simp only [Bool.false_eq_true,if_false,if_true,M.add_numbers,
      ←Complex.ofReal_add,roundingValue_number] <;>
    simp only [Int.floor_add_intCast,Int.ceil_add_intCast,Int.cast_add,Complex.ofReal_intCast,add_comm]

theorem minMaxAbsorptionValue {M : Semantics.{u}} (maximum : Bool) (a b : M.Value)
    (ha : M.mem a (M.standard .real)) (hb : M.mem b (M.standard .real))
    (reverseOuter reverseInner : Bool) :
    (let nested := minMaxValue (!maximum) (if reverseInner then b else a)
      (if reverseInner then a else b)
     minMaxValue maximum (if reverseOuter then nested else a)
       (if reverseOuter then a else nested)) = a := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  obtain ⟨s,hs⟩ := (M.real_members _).mp hb
  rw [hr,hs]
  cases maximum <;> cases reverseOuter <;> cases reverseInner <;>
    simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      minMaxValue_number,min_comm,max_comm,min_eq_left (le_max_left _ _),max_eq_left (min_le_left _ _)]

theorem lcmZeroValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer))
    (hzero : a = M.number 0 ∨ b = M.number 0) : gcdLcmValue true a b = M.number 0 := by
  obtain ⟨x,hx⟩ := (M.integer_members _).mp ha
  obtain ⟨y,hy⟩ := (M.integer_members _).mp hb
  rw [hx,hy] at hzero ⊢
  rw [gcdLcmValue_numbers]
  rcases hzero with h | h
  · have hz : x = 0 := (Int.cast_eq_zero (α := ℂ)).mp (M.number_injective h)
    simp only [hz,Int.lcm_zero_left,Nat.cast_zero,if_true]
  · have hz : y = 0 := (Int.cast_eq_zero (α := ℂ)).mp (M.number_injective h)
    simp only [hz,Int.lcm_zero_right,Nat.cast_zero,if_true]

theorem absoluteZeroReflectionValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (h : absValue (denote a) = M.number 0) :
    Same a (number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  rw [hr,absValue_number] at h
  have habs : |r| = 0 := Complex.ofReal_injective (by
    simpa only [Complex.ofReal_zero] using M.number_injective h)
  change denote a = M.number 0
  rw [hr,abs_eq_zero.mp habs,Complex.ofReal_zero]

theorem signZeroReflectionValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (h : signValue (denote a) = M.number 0) :
    Same a (number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp ha
  rw [hr,signValue_number] at h
  have hsign : Real.sign r = 0 := Complex.ofReal_injective (by
    simpa only [Complex.ofReal_zero] using M.number_injective h)
  change denote a = M.number 0
  rw [hr,Real.sign_eq_zero_iff.mp hsign,Complex.ofReal_zero]

theorem remainderNegationValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (ha : In a Z) (hm : In m NPos) :
    integerDivisionValue false (M.negValue (denote a)) (denote m) =
      integerDivisionValue false (M.subValue (denote m)
        (integerDivisionValue false (denote a) (denote m))) (denote m) := by
  obtain ⟨z,hz⟩ := (M.integer_members _).mp ha
  obtain ⟨d,hd,_⟩ := integerWitnessOfNPos m hm
  rw [hz,hd,M.neg_numbers,←Int.cast_neg,integerDivisionValue_numbers,
    integerDivisionValue_numbers]
  simp only [Bool.false_eq_true,if_false]
  rw [M.sub_numbers,←Int.cast_sub,integerDivisionValue_numbers]
  simp only [Bool.false_eq_true,if_false]
  rw [Int.sub_emod_emod,←Int.neg_emod_eq_sub_emod]

theorem remainderNaturalPowerValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (m : Obj (M := M) β) (n : Obj (M := M) γ)
    (ha : In a Z) (hm : In m NPos) (hn : In n N) :
    integerDivisionValue false (M.powValue (denote a) (denote n)) (denote m) =
      integerDivisionValue false (M.powValue
        (integerDivisionValue false (denote a) (denote m)) (denote n)) (denote m) := by
  obtain ⟨z,hz⟩ := (M.integer_members _).mp ha
  obtain ⟨d,hd,_⟩ := integerWitnessOfNPos m hm
  obtain ⟨k,hk⟩ := (M.natural_members _).mp hn
  rw [hz,hd,hk,M.pow_numbers_nat,←Int.cast_pow,integerDivisionValue_numbers,
    integerDivisionValue_numbers]
  simp only [Bool.false_eq_true,if_false]
  rw [M.pow_numbers_nat,←Int.cast_pow,integerDivisionValue_numbers]
  simp only [Bool.false_eq_true,if_false]
  exact congrArg (fun t : ℤ => M.number (t : ℂ)) ((Int.mod_modEq z d).pow k).symm

end Litex
