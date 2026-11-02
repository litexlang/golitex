import Litex.Scalar

universe u v w x

namespace Litex

/-- Absolute-value builtin adapters use the original real-domain certificate. -/
theorem absIdempotent {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α)) :
    absValue (denote p) = denote p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  change absValue (absValue (denote p.val.arg)) = absValue (denote p.val.arg)
  rw [hr, absValue_number, absValue_number, abs_abs]

theorem absNegation {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α)) :
    absValue (M.negValue (denote p.val.arg)) = denote p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  change absValue (M.negValue (denote p.val.arg)) = absValue (denote p.val.arg)
  rw [hr, M.neg_numbers, ← Complex.ofReal_neg, absValue_number, absValue_number, abs_neg]

theorem absProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AbsObj (M := M) α))
    (q : Obj (M := M) (AbsObj (M := M) β)) (reverseArgs : Bool) :
    absValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
      else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd
  change absValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
    else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
    M.mulValue (absValue (denote p.val.arg)) (absValue (denote q.val.arg))
  rw [ha, hb, absValue_number, absValue_number]
  cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, absValue_number, abs_mul, mul_comm]

theorem absOfNonpositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α))
    (h : Le p.val.arg (number 0)) : denote p = M.negValue (denote p.val.arg) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  have ha0 : a ≤ 0 :=
    (NativeBridge.le_iff_ofDenoteReal p.val.arg (number 0) a 0 ha rfl).mp h
  change absValue (denote p.val.arg) = M.negValue (denote p.val.arg)
  rw [ha, absValue_number, abs_of_nonpos ha0, M.neg_numbers, Complex.ofReal_neg]

end Litex

namespace Litex

theorem sqrtOfSquareAbsolute {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α)) :
    sqrtValue (M.powValue (denote p.val.arg) (M.number ((2 : ℕ) : ℂ))) = denote p := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  change sqrtValue (M.powValue (denote p.val.arg) (M.number ((2 : ℕ) : ℂ))) =
    absValue (denote p.val.arg)
  rw [ha, M.pow_numbers_nat, ← Complex.ofReal_pow, sqrtValue_number,
    Real.sqrt_sq_eq_abs, absValue_number]

theorem sqrtOfNonnegativeSquare {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a R) (h : Le (number 0) a) :
    sqrtValue (M.powValue (denote a) (M.number ((2 : ℕ) : ℂ))) = denote a := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp ha
  have hr0 : 0 ≤ r :=
    (NativeBridge.le_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp h
  rw [hr, M.pow_numbers_nat, ← Complex.ofReal_pow, sqrtValue_number, Real.sqrt_sq hr0]

theorem sqrtProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β)) (reverseArgs : Bool)
    (hp : Le (number 0) p.val.arg) (hq : Le (number 0) q.val.arg) :
    sqrtValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
      else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd.1
  have ha0 : 0 ≤ a := (NativeBridge.le_iff_ofDenoteReal (number 0) p.val.arg 0 a rfl ha).mp hp
  have hb0 : 0 ≤ b := (NativeBridge.le_iff_ofDenoteReal (number 0) q.val.arg 0 b rfl hb).mp hq
  change sqrtValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
    else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
    M.mulValue (sqrtValue (denote p.val.arg)) (sqrtValue (denote q.val.arg))
  rw [ha, hb, sqrtValue_number, sqrtValue_number]
  cases reverseArgs with
  | false =>
    simp only [Bool.false_eq_true, if_false, M.mul_numbers,
      ← Complex.ofReal_mul, sqrtValue_number, Real.sqrt_mul ha0]
  | true =>
    simp only [if_true, M.mul_numbers,
      ← Complex.ofReal_mul, sqrtValue_number]
    rw [Real.sqrt_mul hb0, mul_comm (Real.sqrt b) (Real.sqrt a)]

theorem sqrtQuotient {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β))
    (hp : Le (number 0) p.val.arg) (hq : Lt (number 0) q.val.arg) :
    sqrtValue (M.divValue (denote p.val.arg) (denote q.val.arg)) =
      M.divValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd.1
  have ha0 : 0 ≤ a := (NativeBridge.le_iff_ofDenoteReal (number 0) p.val.arg 0 a rfl ha).mp hp
  have hb0 : 0 < b := (NativeBridge.lt_iff_ofDenoteReal (number 0) q.val.arg 0 b rfl hb).mp hq
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hb0)
  have hrootC : ((Real.sqrt b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hb0))
  change sqrtValue (M.divValue (denote p.val.arg) (denote q.val.arg)) =
    M.divValue (sqrtValue (denote p.val.arg)) (sqrtValue (denote q.val.arg))
  rw [ha, hb, M.div_numbers a b hbC, ← Complex.ofReal_div, sqrtValue_number,
    sqrtValue_number, sqrtValue_number, M.div_numbers _ _ hrootC,
    Real.sqrt_div ha0, Complex.ofReal_div]


theorem sqrtArgumentPositiveFromRootNonzero {M : Semantics.{u}} {α : Type v}
    [Representation M α] (p : Obj (M := M) (SqrtObj (M := M) α))
    (hp : ¬ Same p (number 0)) : Lt (number 0) p.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  have hroot : Real.sqrt r ≠ 0 := by
    intro heq
    apply hp
    change sqrtValue (denote p.val.arg) = M.number 0
    rw [hr, sqrtValue_number, heq, Complex.ofReal_zero]
  have hrpos : 0 < r := Real.sqrt_pos.mp
    (lt_of_le_of_ne (Real.sqrt_nonneg r) (Ne.symm hroot))
  exact NativeBridge.ltOfDenoteReal (number 0) p.val.arg 0 r rfl hr hrpos

theorem sqrtProductFromArgumentEquality {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (MulObj (M := M) (SqrtObj (M := M) β) (SqrtObj (M := M) γ)))
    (harg : denote p.val.arg = M.mulValue (denote q.val.left.val.arg) (denote q.val.right.val.arg)) :
    Same p q := by
  exact (congrArg (sqrtValue (M := M)) harg).trans
    (sqrtProduct q.val.left q.val.right false q.val.left.wd.2 q.val.right.wd.2)

theorem sqrtQuotientFromArgumentEquality {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (DivObj (M := M) (SqrtObj (M := M) β) (SqrtObj (M := M) γ)))
    (harg : denote p.val.arg = M.divValue (denote q.val.left.val.arg) (denote q.val.right.val.arg)) :
    Same p q := by
  exact (congrArg (sqrtValue (M := M)) harg).trans
    (sqrtQuotient q.val.left q.val.right q.val.left.wd.2
      (sqrtArgumentPositiveFromRootNonzero q.val.right q.wd.2.2))

universe y

private theorem denoteAbsoluteValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α)) (r : ℝ) (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((|r| : ℝ) : ℂ) := by
  change absValue (denote p.val.arg) = _
  rw [hr, absValue_number]

theorem absSelfUpperValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α)) : Le p.val.arg p := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  exact NativeBridge.leOfDenoteReal _ _ r |r| hr (denoteAbsoluteValue p r hr) (le_abs_self r)

theorem absSelfLowerValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) β (AbsObj (M := M) α)))
    (hzero : denote p.val.left = M.number 0) : Le p p.val.right.val.arg := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.val.right.wd
  have hp : denote p = M.number ((0 - |r| : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [hzero,denoteAbsoluteValue p.val.right r hr,M.sub_numbers,Complex.ofReal_sub,Complex.ofReal_zero]
  exact NativeBridge.leOfDenoteReal _ _ (0 - |r|) r hp hr (by simpa only [zero_sub] using neg_abs_le r)

theorem absTriangleValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AbsObj (M := M) (AddObj (M := M) α β)))
    (q : Obj (M := M) (AddObj (M := M) (AbsObj (M := M) γ) (AbsObj (M := M) δ)))
    (ha : Same p.val.arg.val.left q.val.left.val.arg)
    (hb : Same p.val.arg.val.right q.val.right.val.arg) : Le p q := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp q.val.left.wd
  obtain ⟨s,hs⟩ := (M.real_members _).mp q.val.right.wd
  have hsum : denote p.val.arg = M.number ((r+s : ℝ) : ℂ) := by
    change M.addValue _ _ = _
    rw [ha.trans hr,hb.trans hs,M.add_numbers,Complex.ofReal_add]
  have hq : denote q = M.number ((|r|+|s| : ℝ) : ℂ) := by
    change M.addValue _ _ = _
    rw [denoteAbsoluteValue q.val.left r hr,denoteAbsoluteValue q.val.right s hs,M.add_numbers,Complex.ofReal_add]
  exact NativeBridge.leOfDenoteReal _ _ |r+s| (|r|+|s|) (denoteAbsoluteValue p (r+s) hsum) hq (abs_add_le r s)

theorem absReverseTriangleAddValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (SubObj (M := M) (AbsObj (M := M) α) (AbsObj (M := M) β)))
    (q : Obj (M := M) (AbsObj (M := M) (AddObj (M := M) γ δ)))
    (ha : Same q.val.arg.val.left p.val.left.val.arg)
    (hb : Same q.val.arg.val.right p.val.right.val.arg) : Le p q := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.val.left.wd
  obtain ⟨s,hs⟩ := (M.real_members _).mp p.val.right.wd
  have hsum : denote q.val.arg = M.number ((r+s : ℝ) : ℂ) := by
    change M.addValue _ _ = _
    rw [ha.trans hr,hb.trans hs,M.add_numbers,Complex.ofReal_add]
  have hp : denote p = M.number ((|r|-|s| : ℝ) : ℂ) := by
    change M.subValue _ _ = _
    rw [denoteAbsoluteValue p.val.left r hr,denoteAbsoluteValue p.val.right s hs,M.sub_numbers,Complex.ofReal_sub]
  apply NativeBridge.leOfDenoteReal _ _ (|r|-|s|) |r+s| hp (denoteAbsoluteValue q (r+s) hsum)
  have h := abs_add_le (r+s) (-s)
  have he : (r+s)+(-s)=r := by ring
  rw [he,abs_neg] at h
  linarith

theorem absReverseTriangleSubValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (SubObj (M := M) (AbsObj (M := M) α) (AbsObj (M := M) β)))
    (q : Obj (M := M) (AbsObj (M := M) (SubObj (M := M) γ δ)))
    (ha : Same q.val.arg.val.left p.val.left.val.arg)
    (hb : Same q.val.arg.val.right p.val.right.val.arg) : Le p q := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.val.left.wd
  obtain ⟨s,hs⟩ := (M.real_members _).mp p.val.right.wd
  have hsub : denote q.val.arg = M.number ((r-s : ℝ) : ℂ) := by
    change M.subValue _ _ = _
    rw [ha.trans hr,hb.trans hs,M.sub_numbers,Complex.ofReal_sub]
  have hp : denote p = M.number ((|r|-|s| : ℝ) : ℂ) := by
    change M.subValue _ _ = _
    rw [denoteAbsoluteValue p.val.left r hr,denoteAbsoluteValue p.val.right s hs,M.sub_numbers,Complex.ofReal_sub]
  apply NativeBridge.leOfDenoteReal _ _ (|r|-|s|) |r-s| hp (denoteAbsoluteValue q (r-s) hsub)
  have h := abs_add_le (r-s) s
  have he : (r-s)+s=r := by ring
  rw [he] at h
  linarith

theorem absBoundUpperProjectionValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AbsObj (M := M) α)) (bound : Obj (M := M) β)
    (h : Le p bound) : Le p.val.arg bound := leTrans _ _ _ (absSelfUpperValue p) h

theorem absBoundNegativeProjectionValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AbsObj (M := M) α)) (q : Obj (M := M) (SubObj (M := M) β γ))
    (bound : Obj (M := M) δ) (hzero : denote q.val.left = M.number 0)
    (harg : Same q.val.right p.val.arg) (h : Le p bound) : Le q bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  have hq : denote q = M.number ((0-r : ℝ) : ℂ) := by
    change M.subValue _ _ = _
    rw [hzero,harg.trans hr,M.sub_numbers,Complex.ofReal_sub,Complex.ofReal_zero]
  have hle : Le q p := NativeBridge.leOfDenoteReal _ _ (0-r) |r| hq (denoteAbsoluteValue p r hr)
    (by simpa only [zero_sub] using neg_le_abs r)
  exact leTrans _ _ _ hle h

theorem absFromSymmetricBoundsValue {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AbsObj (M := M) α)) (q : Obj (M := M) (SubObj (M := M) β γ))
    (bound : Obj (M := M) δ) (hzero : denote q.val.left = M.number 0)
    (harg : Same q.val.right p.val.arg) (hu : Le p.val.arg bound) (hn : Le q bound) : Le p bound := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp p.wd
  have hu_copy := hu
  obtain ⟨_,b,_,hb,_⟩ := hu_copy
  have hupper := (NativeBridge.le_iff_ofDenoteReal p.val.arg bound r b hr hb).mp hu
  have hq : denote q = M.number ((0-r : ℝ) : ℂ) := by
    change M.subValue _ _ = _
    rw [hzero,harg.trans hr,M.sub_numbers,Complex.ofReal_sub,Complex.ofReal_zero]
  have hnegative := (NativeBridge.le_iff_ofDenoteReal q bound (0-r) b hq hb).mp hn
  exact NativeBridge.leOfDenoteReal p bound |r| b (denoteAbsoluteValue p r hr) hb
    (abs_le.mpr ⟨by linarith,hupper⟩)


theorem absDifferenceSymmetryValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AbsObj (M := M) (SubObj (M := M) α β))) :
    absValue (M.subValue (denote p.val.arg.val.right) (denote p.val.arg.val.left)) = denote p := by
  obtain ⟨a,ha⟩ := (M.complex_members _).mp p.val.arg.wd.1
  obtain ⟨b,hb⟩ := (M.complex_members _).mp p.val.arg.wd.2
  have hd : M.subValue (denote p.val.arg.val.right) (denote p.val.arg.val.left) =
      M.negValue (denote p.val.arg) := by
    change M.subValue _ _ = M.negValue (M.subValue _ _)
    rw [ha,hb,M.sub_numbers,M.sub_numbers,M.neg_numbers,neg_sub]
  exact (congrArg (absValue (M := M)) hd).trans (absNegation p)


theorem sqrtOfNonpositiveSquareValue {M : Semantics.{u}} {α : Type v}
    [Representation M α] (a : Obj (M := M) α) (h : Le a (number 0)) :
    sqrtValue (M.powValue (denote a) (M.number ((2 : ℕ) : ℂ))) = M.negValue (denote a) := by
  obtain ⟨r,s,hr,hs,hrs⟩ := h
  change M.number (0 : ℂ) = M.number (s : ℂ) at hs
  have hs0 : s = 0 := Complex.ofReal_injective (by
    simpa only [Complex.ofReal_zero] using (M.number_injective hs).symm)
  subst s
  rw [hr,M.pow_numbers_nat,←Complex.ofReal_pow,sqrtValue_number,
    Real.sqrt_sq_eq_abs,abs_of_nonpos hrs,M.neg_numbers,Complex.ofReal_neg]


theorem sqrtQuotientSquareValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (root : Obj (M := M) (SqrtObj (M := M) α))
    (ratio : Obj (M := M) (DivObj (M := M) β γ))
    (heq : Same root ratio) (reverseProduct : Bool) :
    M.powValue (denote ratio.val.left) (M.number ((2 : ℕ) : ℂ)) =
      (if reverseProduct then M.mulValue
        (M.powValue (denote ratio.val.right) (M.number ((2 : ℕ) : ℂ))) (denote root.val.arg)
      else M.mulValue (denote root.val.arg)
        (M.powValue (denote ratio.val.right) (M.number ((2 : ℕ) : ℂ)))) := by
  obtain ⟨a,ha⟩ := (M.real_members _).mp root.wd.1
  obtain ⟨p,hp⟩ := (M.complex_members _).mp ratio.wd.1
  obtain ⟨q,hq⟩ := (M.complex_members _).mp ratio.wd.2.1
  have hq0 : q ≠ 0 := NativeBridge.nativeNonzeroOfDenote ratio.val.right q hq ratio.wd.2.2
  have ha0 : 0 ≤ a := (NativeBridge.le_iff_ofDenoteReal (number 0) root.val.arg 0 a rfl ha).mp root.wd.2
  change sqrtValue (denote root.val.arg) = M.divValue (denote ratio.val.left) (denote ratio.val.right) at heq
  rw [ha,hp,hq,sqrtValue_number,M.div_numbers p q hq0] at heq
  have hquot : ((Real.sqrt a : ℝ) : ℂ) = p / q := M.number_injective heq
  have hp' : p = ((Real.sqrt a : ℝ) : ℂ) * q := ((eq_div_iff hq0).mp hquot).symm
  have hsquare : p ^ 2 = (a : ℂ) * q ^ 2 := by
    rw [hp',mul_pow,←Complex.ofReal_pow,Real.sq_sqrt ha0]
  rw [hp,hq,ha,M.pow_numbers_nat,M.pow_numbers_nat]
  cases reverseProduct <;> simp only [Bool.false_eq_true,if_false,if_true,M.mul_numbers]
  · exact congrArg M.number hsquare
  · exact congrArg M.number (hsquare.trans (mul_comm _ _))

end Litex
