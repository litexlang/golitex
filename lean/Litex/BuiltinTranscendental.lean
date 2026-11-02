import Litex.ElementaryFunctions
import Litex.BuiltinScalar

universe u v w

namespace Litex

theorem exponentialSumValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α))
    (q : Obj (M := M) (ExpObj (M := M) β)) (reverseArgs : Bool) :
    realUnaryValue Real.exp
      (if reverseArgs then M.addValue (denote q.val.arg) (denote p.val.arg)
       else M.addValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd
  change realUnaryValue Real.exp
      (if reverseArgs then M.addValue (denote q.val.arg) (denote p.val.arg)
       else M.addValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (realUnaryValue Real.exp (denote p.val.arg))
        (realUnaryValue Real.exp (denote q.val.arg))
  rw [ha, hb, realUnaryValue_number, realUnaryValue_number]
  cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.add_numbers,
      ← Complex.ofReal_add, realUnaryValue_number, M.mul_numbers,
      Real.exp_add, Complex.ofReal_mul, mul_comm]

theorem sineAdditionComplex (a b : ℝ) :
    (Real.sin (a+b) : ℂ) =
      (Real.sin a : ℂ) * (Real.cos b : ℂ) +
      (Real.cos a : ℂ) * (Real.sin b : ℂ) := by
  rw [Real.sin_add, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]

theorem cosineAdditionComplex (a b : ℝ) :
    (Real.cos (a+b) : ℂ) =
      (Real.cos a : ℂ) * (Real.cos b : ℂ) -
      (Real.sin a : ℂ) * (Real.sin b : ℂ) := by
  rw [Real.cos_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]

theorem absoluteSquareValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (a : Obj (M := M) α) (ha : In a R) :
    absValue (M.powValue (denote a) (M.number ((2 : ℕ) : ℂ))) =
      M.powValue (denote a) (M.number ((2 : ℕ) : ℂ)) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  rw [hr, M.pow_numbers_nat, ← Complex.ofReal_pow, absValue_number,
    abs_of_nonneg (sq_nonneg r)]


theorem exponentialDifferenceValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (ExpObj (M := M) α))
    (q : Obj (M := M) (ExpObj (M := M) β)) :
    realUnaryValue Real.exp (M.subValue (denote p.val.arg) (denote q.val.arg)) =
      M.divValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd
  have hn : (Real.exp b : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero b
  change realUnaryValue Real.exp (M.subValue (denote p.val.arg) (denote q.val.arg)) =
    M.divValue (realUnaryValue Real.exp (denote p.val.arg)) (realUnaryValue Real.exp (denote q.val.arg))
  rw [ha, hb, realUnaryValue_number, realUnaryValue_number, M.sub_numbers,
    ← Complex.ofReal_sub, realUnaryValue_number, M.div_numbers _ _ hn,
    Real.exp_sub, Complex.ofReal_div]

theorem logarithmProductValue {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α))
    (q : Obj (M := M) (LnObj (M := M) β)) :
    realUnaryValue Real.log (M.mulValue (denote p.val.arg) (denote q.val.arg)) =
      M.addValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp (inRPos_real _ p.wd)
  obtain ⟨b, hb⟩ := (M.real_members _).mp (inRPos_real _ q.wd)
  have ha0 : 0 < a := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 a rfl ha).mp (inRPos_positive _ p.wd)
  have hb0 : 0 < b := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 b rfl hb).mp (inRPos_positive _ q.wd)
  change realUnaryValue Real.log (M.mulValue (denote p.val.arg) (denote q.val.arg)) =
    M.addValue (realUnaryValue Real.log (denote p.val.arg)) (realUnaryValue Real.log (denote q.val.arg))
  rw [ha, hb, realUnaryValue_number, realUnaryValue_number, M.mul_numbers,
    ← Complex.ofReal_mul, realUnaryValue_number, M.add_numbers,
    Real.log_mul (ne_of_gt ha0) (ne_of_gt hb0), Complex.ofReal_add]

theorem logarithmQuotientValue {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LnObj (M := M) α))
    (q : Obj (M := M) (LnObj (M := M) β)) :
    realUnaryValue Real.log (M.divValue (denote p.val.arg) (denote q.val.arg)) =
      M.subValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp (inRPos_real _ p.wd)
  obtain ⟨b, hb⟩ := (M.real_members _).mp (inRPos_real _ q.wd)
  have ha0 : 0 < a := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 a rfl ha).mp (inRPos_positive _ p.wd)
  have hb0 : 0 < b := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 b rfl hb).mp (inRPos_positive _ q.wd)
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hb0)
  change realUnaryValue Real.log (M.divValue (denote p.val.arg) (denote q.val.arg)) =
    M.subValue (realUnaryValue Real.log (denote p.val.arg)) (realUnaryValue Real.log (denote q.val.arg))
  rw [ha, hb, realUnaryValue_number, realUnaryValue_number, M.div_numbers _ _ hbC,
    ← Complex.ofReal_div, realUnaryValue_number, M.sub_numbers,
    Real.log_div (ne_of_gt ha0) (ne_of_gt hb0), Complex.ofReal_sub]

theorem exponentialInjectiveValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haR : In a R) (hbR : In b R)
    (himage : realUnaryValue Real.exp (denote a) = realUnaryValue Real.exp (denote b)) :
    Same a b := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp haR
  obtain ⟨s, hs⟩ := (M.real_members _).mp hbR
  rw [hr, hs, realUnaryValue_number, realUnaryValue_number] at himage
  have hequal := Real.exp_injective (Complex.ofReal_injective (M.number_injective himage))
  exact hr.trans (hequal ▸ hs.symm)

theorem logarithmInjectiveValue {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a RPos) (hb : In b RPos)
    (himage : realUnaryValue Real.log (denote a) = realUnaryValue Real.log (denote b)) :
    Same a b := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp (inRPos_real _ ha)
  obtain ⟨s, hs⟩ := (M.real_members _).mp (inRPos_real _ hb)
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp (inRPos_positive _ ha)
  have hs0 : 0 < s := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp (inRPos_positive _ hb)
  rw [hr, hs, realUnaryValue_number, realUnaryValue_number] at himage
  have hequal := Real.log_injOn_pos hr0 hs0 (Complex.ofReal_injective (M.number_injective himage))
  exact hr.trans (hequal ▸ hs.symm)

theorem logarithmFromPowerValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (LogObj (M := M) α β)) (e : Obj (M := M) γ)
    (hbase : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1)) (he : In e Z)
    (hpower : M.powValue (denote p.val.base) (denote e) = denote p.val.arg) : Same p e := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  obtain ⟨z, hz⟩ := (M.integer_members _).mp he
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp hbase.1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr0)
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero _ r hr hbase.1 hbase.2)
  rw [hr, hz, M.pow_numbers_int _ _ hrC, ← Complex.ofReal_zpow, hs] at hpower
  have hp : r ^ z = s := Complex.ofReal_injective (M.number_injective hpower)
  calc
    denote p = M.number ((Real.log s / Real.log r : ℝ) : ℂ) := denoteLog p r s hr hs
    _ = M.number (z : ℂ) := by rw [← hp, Real.log_zpow, mul_div_cancel_right₀ _ hn, Complex.ofReal_intCast]
    _ = denote e := hz.symm

theorem powerFromLogarithmValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (LogObj (M := M) α β)) (e : Obj (M := M) γ)
    (hbase : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1))
    (harg : Lt (number 0) p.val.arg) (he : In e Z)
    (hlogarithm : Same p e) : M.powValue (denote p.val.base) (denote e) = denote p.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  obtain ⟨z, hz⟩ := (M.integer_members _).mp he
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp hbase.1
  have hs0 : 0 < s := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp harg
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr0)
  have hn : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp (logBaseNonzero _ r hr hbase.1 hbase.2)
  have hratio : Real.log s / Real.log r = (z : ℝ) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_intCast]
    exact M.number_injective ((denoteLog p r s hr hs).symm.trans (hlogarithm.trans hz))
  have hlogs : Real.log (r ^ z) = Real.log s := by
    rw [Real.log_zpow]
    exact ((div_eq_iff hn).mp hratio).symm
  have hp : r ^ z = s := Real.log_injOn_pos (zpow_pos hr0 z) hs0 hlogs
  rw [hr, hz, M.pow_numbers_int _ _ hrC, ← Complex.ofReal_zpow, hp, hs]


theorem naturalLogPositiveAboveOneValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (LnObj (M := M) α))
    (h : Lt (number 1) p.val.arg) : Lt (number 0) p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp (inRPos_real p.val.arg p.wd)
  have hgt := (NativeBridge.lt_iff_ofDenoteReal (number 1) p.val.arg 1 r rfl hr).mp h
  exact NativeBridge.ltOfDenoteReal _ _ 0 (Real.log r) rfl (denoteLn p r hr) (Real.log_pos hgt)

theorem naturalLogNegativeBelowOneValue {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} [Representation M α] (p : Obj (M := M) (LnObj (M := M) α))
    (h : Lt p.val.arg (number 1)) : Lt p (number 0) := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp (inRPos_real p.val.arg p.wd)
  have hlt := (NativeBridge.lt_iff_ofDenoteReal p.val.arg (number 1) r 1 hr rfl).mp h
  have hpos := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 r rfl hr).mp
    (inRPos_positive p.val.arg p.wd)
  exact NativeBridge.ltOfDenoteReal _ _ (Real.log r) 0 (denoteLn p r hr) rfl (Real.log_neg hpos hlt)

theorem positiveNegativeProductValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β)) (reverse : Bool)
    (hp : if reverse then Lt (number 0) p.val.right else Lt (number 0) p.val.left)
    (hn : if reverse then Lt p.val.left (number 0) else Lt p.val.right (number 0)) : Lt p (number 0) := by
  cases reverse
  · obtain ⟨r0,r,hr0,hr,hpos⟩ := hp
    obtain ⟨s,s0,hs,hs0,hneg⟩ := hn
    have hr0z : r0=0 := Complex.ofReal_injective (M.number_injective hr0).symm
    have hs0z : s0=0 := Complex.ofReal_injective (M.number_injective hs0).symm
    subst r0; subst s0
    refine NativeBridge.ltOfDenoteReal p (number 0) (r*s) 0 ?_ rfl (mul_neg_of_pos_of_neg hpos hneg)
    change M.mulValue _ _ = _
    rw [hr,hs,M.mul_numbers,Complex.ofReal_mul]
  · obtain ⟨r0,r,hr0,hr,hpos⟩ := hp
    obtain ⟨s,s0,hs,hs0,hneg⟩ := hn
    have hr0z : r0=0 := Complex.ofReal_injective (M.number_injective hr0).symm
    have hs0z : s0=0 := Complex.ofReal_injective (M.number_injective hs0).symm
    subst r0; subst s0
    refine NativeBridge.ltOfDenoteReal p (number 0) (s*r) 0 ?_ rfl (mul_neg_of_neg_of_pos hneg hpos)
    change M.mulValue _ _ = _
    rw [hr,hs,M.mul_numbers,Complex.ofReal_mul]

theorem nonnegativeNegativeProductValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β)) (reverse : Bool)
    (hp : if reverse then Le (number 0) p.val.right else Le (number 0) p.val.left)
    (hn : if reverse then Lt p.val.left (number 0) else Lt p.val.right (number 0)) : Le p (number 0) := by
  cases reverse
  · obtain ⟨r0,r,hr0,hr,hpos⟩ := hp
    obtain ⟨s,s0,hs,hs0,hneg⟩ := hn
    have hr0z : r0=0 := Complex.ofReal_injective (M.number_injective hr0).symm
    have hs0z : s0=0 := Complex.ofReal_injective (M.number_injective hs0).symm
    subst r0; subst s0
    refine NativeBridge.leOfDenoteReal p (number 0) (r*s) 0 ?_ rfl (mul_nonpos_of_nonneg_of_nonpos hpos hneg.le)
    change M.mulValue _ _ = _
    rw [hr,hs,M.mul_numbers,Complex.ofReal_mul]
  · obtain ⟨r0,r,hr0,hr,hpos⟩ := hp
    obtain ⟨s,s0,hs,hs0,hneg⟩ := hn
    have hr0z : r0=0 := Complex.ofReal_injective (M.number_injective hr0).symm
    have hs0z : s0=0 := Complex.ofReal_injective (M.number_injective hs0).symm
    subst r0; subst s0
    refine NativeBridge.leOfDenoteReal p (number 0) (s*r) 0 ?_ rfl (mul_nonpos_of_nonpos_of_nonneg hneg.le hpos)
    change M.mulValue _ _ = _
    rw [hr,hs,M.mul_numbers,Complex.ofReal_mul]


end Litex
