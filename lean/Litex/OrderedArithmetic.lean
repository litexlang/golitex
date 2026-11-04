import Litex.SetFunctions

universe u v w x

namespace Litex.NativeBridge

variable {M : Semantics.{u}}

theorem realWitnessOfNonnegative {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : Le (number 0) a) :
    ∃ r : ℝ, denote a = M.number (r : ℂ) ∧ 0 ≤ r := by
  obtain ⟨r₀, r, hz, hr, hle⟩ := h
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have h0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  exact ⟨r, hr, h0 ▸ hle⟩

theorem realWitnessOfPositive {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : Lt (number 0) a) :
    ∃ r : ℝ, denote a = M.number (r : ℂ) ∧ 0 < r := by
  obtain ⟨r₀, r, hz, hr, hlt⟩ := h
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have h0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  exact ⟨r, hr, h0 ▸ hlt⟩

end Litex.NativeBridge

namespace Litex

theorem addNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Le (number 0) b) : Le (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.leOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_nonneg hposR hposS)
  change M.addValue (denote a) (denote b) = _
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

theorem addPositiveLeft {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Le (number 0) b) : Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfPositive a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos_of_pos_of_nonneg hposR hposS)
  change M.addValue (denote a) (denote b) = _
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

theorem addPositiveRight {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Lt (number 0) b) : Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfPositive b hb
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos_of_nonneg_of_pos hposR hposS)
  change M.addValue (denote a) (denote b) = _
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

theorem mulNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Le (number 0) a) (hb : Le (number 0) b) : Le (number 0) (mul a b haC hbC) := by
  obtain ⟨r, hr, hposR⟩ := NativeBridge.realWitnessOfNonnegative a ha
  obtain ⟨s, hs, hposS⟩ := NativeBridge.realWitnessOfNonnegative b hb
  refine NativeBridge.leOfDenoteReal (number 0) (mul a b haC hbC) 0 (r * s)
    rfl ?_ (mul_nonneg hposR hposS)
  change M.mulValue (denote a) (denote b) = _
  rw [hr, hs, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLeLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorNonnegative : Le (number 0) lhs.val.left)
    (hOperandsLe : Le lhs.val.right rhs.val.right)
    (hFactorSame : Same lhs.val.left rhs.val.left) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfNonnegative lhs.val.left hFactorNonnegative
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLe
  refine NativeBridge.leOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_ (mul_le_mul_of_nonneg_left hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hFactorSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLeRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorNonnegative : Le (number 0) lhs.val.right)
    (hOperandsLe : Le lhs.val.left rhs.val.left)
    (hFactorSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfNonnegative lhs.val.right hFactorNonnegative
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLe
  refine NativeBridge.leOfDenoteReal lhs rhs (a * c) (b * c) ?_ ?_ (mul_le_mul_of_nonneg_right hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hFactorSame.symm.trans hc, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorPositive : Lt (number 0) lhs.val.left)
    (hOperandsLt : Lt lhs.val.right rhs.val.right)
    (hFactorSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.left hFactorPositive
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLt
  refine NativeBridge.ltOfDenoteReal lhs rhs (c * a) (c * b) ?_ ?_ (mul_lt_mul_of_pos_left hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hFactorSame.symm.trans hc, hb, M.mul_numbers, Complex.ofReal_mul]

theorem mulStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (MulObj (M := M) α β))
    (rhs : Obj (M := M) (MulObj (M := M) γ δ))
    (hFactorPositive : Lt (number 0) lhs.val.right)
    (hOperandsLt : Lt lhs.val.left rhs.val.left)
    (hFactorSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.right hFactorPositive
  obtain ⟨a, b, ha, hb, hab⟩ := hOperandsLt
  refine NativeBridge.ltOfDenoteReal lhs rhs (a * c) (b * c) ?_ ?_ (mul_lt_mul_of_pos_right hab hc0)
  · change M.mulValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.mul_numbers, Complex.ofReal_mul]
  · change M.mulValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hFactorSame.symm.trans hc, M.mul_numbers, Complex.ofReal_mul]

theorem mulMinusOneNegativeLeft {M : Semantics.{u}} {α β : Type*}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (hFactor : denote p.val.left = M.number (-1))
    (hPositive : Lt (number 0) p.val.right) : Lt p (number 0) := by
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfPositive p.val.right hPositive
  refine NativeBridge.ltOfDenoteReal p (number 0) ((-1) * a) 0 ?_ rfl ?_
  · change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor, ha, M.mul_numbers, Complex.ofReal_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
  · simpa only [neg_one_mul] using neg_neg_of_pos ha0

theorem mulMinusOneNegativeRight {M : Semantics.{u}} {α β : Type*}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (hFactor : denote p.val.right = M.number (-1))
    (hPositive : Lt (number 0) p.val.left) : Lt p (number 0) := by
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfPositive p.val.left hPositive
  refine NativeBridge.ltOfDenoteReal p (number 0) (a * (-1)) 0 ?_ rfl ?_
  · change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor, ha, M.mul_numbers, Complex.ofReal_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
  · simpa only [mul_neg_one] using neg_neg_of_pos ha0

theorem divStructuralLe {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (DivObj (M := M) α β))
    (rhs : Obj (M := M) (DivObj (M := M) γ δ))
    (hDivisorPos : Lt (number 0) lhs.val.right)
    (hNumeratorsLe : Le lhs.val.left rhs.val.left)
    (hDivisorSame : Same lhs.val.right rhs.val.right) : Le lhs rhs := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive lhs.val.right hDivisorPos
  obtain ⟨a, b, ha, hb, hab⟩ := hNumeratorsLe
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal lhs rhs (a / c) (b / c) ?_ ?_ (div_le_div_of_nonneg_right hab (le_of_lt hc0))
  · change M.divValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]
  · change M.divValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hb, hDivisorSame.symm.trans hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

theorem subNonnegativeToLe {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (haR : In p.val.left R) (hbR : In p.val.right R)
    (h : Le (number 0) p) : Le p.val.right p.val.left := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  have hp : denote p = M.number ((a - b : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]
  exact NativeBridge.leOfDenoteReal _ _ b a hb ha
    (sub_nonneg.mp ((NativeBridge.le_iff_ofDenoteReal (number 0) p 0 (a - b) rfl hp).mp h))

theorem subPositiveToLt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (haR : In p.val.left R) (hbR : In p.val.right R)
    (h : Lt (number 0) p) : Lt p.val.right p.val.left := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  have hp : denote p = M.number ((a - b : ℝ) : ℂ) := by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hb, M.sub_numbers, Complex.ofReal_sub]
  exact NativeBridge.ltOfDenoteReal _ _ b a hb ha
    (sub_pos.mp ((NativeBridge.lt_iff_ofDenoteReal (number 0) p 0 (a - b) rfl hp).mp h))

theorem leDivOfProductBound {M : Semantics.{u}} {α β γ δ ε : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (a : Obj (M := M) α) (q : Obj (M := M) (DivObj (M := M) β γ))
    (p : Obj (M := M) (MulObj (M := M) δ ε)) (haR : In a R)
    (hDivisorPos : Lt (number 0) q.val.right) (hBound : Le p q.val.left)
    (hFactor : Same p.val.left q.val.right) (hArgument : Same p.val.right a) : Le a q := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨r, hr⟩ := (M.real_members _).mp haR
  obtain ⟨s, b, hs, hb, hsb⟩ := hBound
  have hproduct : denote p = M.number ((c * r : ℝ) : ℂ) := by
    change M.mulValue (denote p.val.left) (denote p.val.right) = _
    rw [hFactor.trans hc, hArgument.trans hr, M.mul_numbers, Complex.ofReal_mul]
  have hsProduct : s = c * r :=
    Complex.ofReal_injective (M.number_injective (hs.symm.trans hproduct))
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal a q r (b / c) hr ?_ ?_
  · change M.divValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]
  · apply (le_div_iff₀ hc0).mpr
    simpa only [hsProduct, mul_comm] using hsb

end Litex

namespace Litex

/-- Literal-zero specialization of the selected shared positive divisor rule.
The original quotient and its constructor WD remain the subject. -/
theorem divStructuralNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (DivObj (M := M) α β))
    (hDivisorPos : Lt (number 0) q.val.right)
    (hNumeratorNonnegative : Le (number 0) q.val.left) : Le (number 0) q := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨a, ha, ha0⟩ := NativeBridge.realWitnessOfNonnegative q.val.left hNumeratorNonnegative
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal (number 0) q 0 (a / c) rfl ?_
    (div_nonneg ha0 (le_of_lt hc0))
  change M.divValue (denote q.val.left) (denote q.val.right) = _
  rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

theorem divStructuralNonpositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (DivObj (M := M) α β))
    (hDivisorPos : Lt (number 0) q.val.right)
    (hNumeratorNonpositive : Le q.val.left (number 0)) : Le q (number 0) := by
  obtain ⟨c, hc, hc0⟩ := NativeBridge.realWitnessOfPositive q.val.right hDivisorPos
  obtain ⟨a, r₀, ha, hz, ha0⟩ := hNumeratorNonpositive
  change M.number 0 = M.number (r₀ : ℂ) at hz
  have hr0 : r₀ = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  subst r₀
  have hc0C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
  refine NativeBridge.leOfDenoteReal q (number 0) (a / c) 0 ?_ rfl
    (div_nonpos_of_nonpos_of_nonneg ha0 (le_of_lt hc0))
  change M.divValue (denote q.val.left) (denote q.val.right) = _
  rw [ha, hc, M.div_numbers _ _ hc0C, Complex.ofReal_div]

end Litex

namespace Litex

/-- The denotation chooses one original value; WD does not choose the meaning. -/
noncomputable def minMaxValue {M : Semantics.{u}} (maximum : Bool)
    (a b : M.Value) : M.Value := by
  classical
  exact if (∃ r s : ℝ, a = M.number (r : ℂ) ∧ b = M.number (s : ℂ) ∧ r ≤ s)
    then (if maximum then b else a) else (if maximum then a else b)

theorem minMaxValue_number {M : Semantics.{u}} (maximum : Bool) (r s : ℝ) :
    minMaxValue maximum (M.number (r : ℂ)) (M.number (s : ℂ)) =
      M.number ((if maximum then Max.max r s else Min.min r s : ℝ) : ℂ) := by
  classical
  have iff_le : (∃ x y : ℝ, M.number (r : ℂ) = M.number (x : ℂ) ∧
      M.number (s : ℂ) = M.number (y : ℂ) ∧ x ≤ y) ↔ r ≤ s := by
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      have hr := Complex.ofReal_injective (M.number_injective hx)
      have hs := Complex.ofReal_injective (M.number_injective hy)
      exact hr.symm ▸ hs.symm ▸ hxy
    · intro h; exact ⟨r, s, rfl, rfl, h⟩
  unfold minMaxValue
  simp only [iff_le]
  cases maximum <;> by_cases h : r ≤ s
  · simp only [h, if_true, Bool.false_eq_true, if_false, min_eq_left h]
  · simp only [h, if_false, Bool.false_eq_true, min_eq_right (le_of_not_ge h)]
  · simp only [h, if_true, max_eq_right h]
  · simp only [h, if_false, if_true, max_eq_left (le_of_not_ge h)]

structure MinMaxObj {M : Semantics.{u}} (maximum : Bool)
    (α : Type v) (β : Type w) [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance minMaxRepresentation {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (MinMaxObj (M := M) maximum α β) where
  wd p := In p.left R ∧ In p.right R
  denote p := minMaxValue maximum (denote p.left) (denote p.right)
  wd_isSet {p} _ := by
    classical
    unfold minMaxValue
    split <;> cases maximum <;> first | exact isSet p.left | exact isSet p.right

noncomputable def min {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) : Obj (M := M) (MinMaxObj (M := M) false α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

noncomputable def max {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a R) (hb : In b R) : Obj (M := M) (MinMaxObj (M := M) true α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

theorem minMaxMember {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β)) (A : Obj (M := M) γ)
    (ha : In p.val.left A) (hb : In p.val.right A) : In p A := by
  classical
  change M.mem (minMaxValue maximum (denote p.val.left) (denote p.val.right)) (denote A)
  unfold minMaxValue
  split <;> cases maximum <;> first | exact ha | exact hb

theorem naturalMaxDifference {M : Semantics.{u}} {α β γ : Type*}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (SubObj (M := M) (MinMaxObj (M := M) true α β) γ))
    (rightOperand : Bool)
    (hselected : denote p.val.right =
      if rightOperand then denote p.val.left.val.right else denote p.val.left.val.left)
    (hmax : In p.val.left N) (hsub : In p.val.right N) : In p N := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.val.left.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.val.left.wd.2
  have hmaxReal : denote p.val.left = M.number ((Max.max r s : ℝ) : ℂ) := by
    change minMaxValue true (denote p.val.left.val.left) (denote p.val.left.val.right) = _
    rw [hr, hs, minMaxValue_number]
    rfl
  have hbound : Le p.val.right p.val.left := by
    cases rightOperand
    · refine ⟨r, Max.max r s, ?_, hmaxReal, le_max_left r s⟩
      exact hselected.trans hr
    · refine ⟨s, Max.max r s, ?_, hmaxReal, le_max_right r s⟩
      exact hselected.trans hs
  obtain ⟨m, hm⟩ := (M.natural_members _).mp hmax
  obtain ⟨n, hn⟩ := (M.natural_members _).mp hsub
  have hmr : denote p.val.left = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hm
  have hnr : denote p.val.right = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hnm : n ≤ m := by
    exact_mod_cast (NativeBridge.le_iff_ofDenoteReal _ _ _ _ hnr hmr).mp hbound
  refine (M.natural_members _).mpr ⟨m - n, ?_⟩
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  rw [hm, hn, M.sub_numbers, Nat.cast_sub hnm]

theorem minMaxIdempotent {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (h : Same p.val.left p.val.right) : Same p p.val.left := by
  classical
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) = denote p.val.left
  change denote p.val.left = denote p.val.right at h
  rw [← h]
  unfold minMaxValue
  split <;> cases maximum <;> rfl

theorem minMaxCommutative {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (q : Obj (M := M) (MinMaxObj (M := M) maximum γ δ))
    (h₁ : Same p.val.left q.val.right) (h₂ : Same p.val.right q.val.left) : Same p q := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  change denote p.val.left = denote q.val.right at h₁
  change denote p.val.right = denote q.val.left at h₂
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) =
    minMaxValue maximum (denote q.val.left) (denote q.val.right)
  rw [← h₁, ← h₂, hr, hs, minMaxValue_number, minMaxValue_number]
  cases maximum
  · exact congrArg (fun x : ℝ => M.number (x : ℂ)) (min_comm r s)
  · exact congrArg (fun x : ℝ => M.number (x : ℂ)) (max_comm r s)

end Litex

namespace Litex

theorem minMaxDenoteReal {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β)) (r s : ℝ)
    (hr : denote p.val.left = M.number (r : ℂ))
    (hs : denote p.val.right = M.number (s : ℂ)) :
    denote p = M.number ((if maximum then Max.max r s else Min.min r s : ℝ) : ℂ) := by
  change minMaxValue maximum (denote p.val.left) (denote p.val.right) = _
  rw [hr, hs, minMaxValue_number]

theorem minLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β)) :
    Le p p.val.left ∧ Le p p.val.right := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  have hp : denote p = M.number ((Min.min r s : ℝ) : ℂ) := minMaxDenoteReal p r s hr hs
  exact ⟨⟨_, _, hp, hr, min_le_left r s⟩, ⟨_, _, hp, hs, min_le_right r s⟩⟩

theorem operandsLeMax {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β)) :
    Le p.val.left p ∧ Le p.val.right p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2
  have hp : denote p = M.number ((Max.max r s : ℝ) : ℂ) := minMaxDenoteReal p r s hr hs
  exact ⟨⟨_, _, hr, hp, le_max_left r s⟩, ⟨_, _, hs, hp, le_max_right r s⟩⟩

theorem minOfLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β))
    (h : Le p.val.left p.val.right) : Same p p.val.left := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  change minMaxValue false (denote p.val.left) (denote p.val.right) = denote p.val.left
  rw [ha, hb, minMaxValue_number]
  simp only [Bool.false_eq_true, if_false, min_eq_left hab]

theorem minOfGeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) false α β))
    (h : Le p.val.right p.val.left) : Same p p.val.right := by
  obtain ⟨b, a, hb, ha, hba⟩ := h
  change minMaxValue false (denote p.val.left) (denote p.val.right) = denote p.val.right
  rw [ha, hb, minMaxValue_number]
  simp only [Bool.false_eq_true, if_false, min_eq_right hba]

theorem maxOfLeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β))
    (h : Le p.val.left p.val.right) : Same p p.val.right := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  change minMaxValue true (denote p.val.left) (denote p.val.right) = denote p.val.right
  rw [ha, hb, minMaxValue_number]
  simp only [if_true, max_eq_right hab]

theorem maxOfGeOperands {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MinMaxObj (M := M) true α β))
    (h : Le p.val.right p.val.left) : Same p p.val.left := by
  obtain ⟨b, a, hb, ha, hba⟩ := h
  change minMaxValue true (denote p.val.left) (denote p.val.right) = denote p.val.left
  rw [ha, hb, minMaxValue_number]
  simp only [if_true, max_eq_left hba]

theorem minMaxMonotone {M : Semantics.{u}} {maximum : Bool}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (MinMaxObj (M := M) maximum α β))
    (q : Obj (M := M) (MinMaxObj (M := M) maximum γ δ))
    (ha : Le p.val.left q.val.left) (hb : Le p.val.right q.val.right) : Le p q := by
  obtain ⟨a, c, ha, hc, hac⟩ := ha
  obtain ⟨b, d, hb, hd, hbd⟩ := hb
  refine ⟨_, _, minMaxDenoteReal p a b ha hb, minMaxDenoteReal q c d hc hd, ?_⟩
  cases maximum
  · exact min_le_min hac hbd
  · exact max_le_max hac hbd

end Litex

namespace Litex

/-- The native real sign, observed through the fixed numeric embedding. -/
noncomputable def signValue {M : Semantics.{u}} (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, a = M.number (r : ℂ)
    then M.number ((Real.sign (Classical.choose h) : ℝ) : ℂ)
    else M.number 0

theorem signValue_number {M : Semantics.{u}} (r : ℝ) :
    signValue (M.number (r : ℂ)) = M.number ((Real.sign r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold signValue
  rw [dif_pos h, hr]

structure SignObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance signRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SignObj (M := M) α) where
  wd p := In p.arg R
  denote p := signValue (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sign r, by
      rw [hr, signValue_number]⟩)

noncomputable def sign {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (SignObj (M := M) α) :=
  ⟨⟨a⟩, h⟩

theorem signDenoteReal {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((Real.sign r : ℝ) : ℂ) := by
  change signValue (denote p.val.arg) = _
  rw [hr, signValue_number]

/-- A real number and its sign vanish together. -/
theorem signZeroIffArgZero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (haR : In p.val.arg R) :
    Same p (number 0) ↔ Same p.val.arg (number 0) := by
  let r := NativeBridge.asReal p.val.arg haR
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg haR
  have hp : denote p = M.number ((Real.sign r : ℝ) : ℂ) := signDenoteReal p r hr
  constructor
  · intro h
    have hs : Real.sign r = 0 := by
      have hc : ((Real.sign r : ℝ) : ℂ) = 0 := M.number_injective (hp.symm.trans h)
      exact_mod_cast hc
    have h0 : r = 0 := Real.sign_eq_zero_iff.mp hs
    change denote p.val.arg = M.number 0
    exact hr.trans (congrArg M.number (by exact_mod_cast h0))
  · intro h
    have h0 : r = 0 := by
      have hc : (r : ℂ) = 0 := M.number_injective (hr.symm.trans h)
      exact_mod_cast hc
    have hs : Real.sign r = 0 := Real.sign_eq_zero_iff.mpr h0
    change denote p = M.number 0
    exact hp.trans (congrArg M.number (by exact_mod_cast hs))

theorem signInZ {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) : In p Z := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  have hp := signDenoteReal p r hr
  rcases Real.sign_apply_eq r with hn | hz | ho
  · exact (M.integer_members _).mpr ⟨-1, by rw [hp, hn]; norm_num⟩
  · exact (M.integer_members _).mpr ⟨0, by rw [hp, hz]; norm_num⟩
  · exact (M.integer_members _).mpr ⟨1, by rw [hp, ho]; norm_num⟩

theorem signOfPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α))
    (h : Lt (number 0) p.val.arg) : Same p (number 1) := by
  obtain ⟨r, hr, hpos⟩ := NativeBridge.realWitnessOfPositive p.val.arg h
  change denote p = M.number 1
  rw [signDenoteReal p r hr, Real.sign_of_pos hpos, Complex.ofReal_one]

theorem signOfNegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α))
    (h : Lt p.val.arg (number 0)) : Same p (number (-1)) := by
  obtain ⟨r, z, hr, hz, hneg⟩ := h
  change M.number 0 = M.number (z : ℂ) at hz
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  subst z
  change denote p = M.number (-1)
  rw [signDenoteReal p r hr, Real.sign_of_neg hneg, Complex.ofReal_neg, Complex.ofReal_one]

theorem realSignMul (a b : ℝ) : Real.sign (a * b) = Real.sign a * Real.sign b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [Real.sign_of_neg ha, Real.sign_of_neg hb,
        Real.sign_of_pos (mul_pos_of_neg_of_neg ha hb)]
      norm_num
    · rw [mul_zero, Real.sign_zero, mul_zero]
    · rw [Real.sign_of_neg ha, Real.sign_of_pos hb,
        Real.sign_of_neg (mul_neg_of_neg_of_pos ha hb), mul_one]
  · rw [zero_mul, Real.sign_zero, zero_mul]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · rw [Real.sign_of_pos ha, Real.sign_of_neg hb,
        Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), one_mul]
    · rw [mul_zero, Real.sign_zero, mul_zero]
    · rw [Real.sign_of_pos ha, Real.sign_of_pos hb,
        Real.sign_of_pos (mul_pos ha hb), one_mul]

theorem realSignMulAbs (a : ℝ) : Real.sign a * |a| = a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, neg_one_mul, neg_neg]
  · rw [Real.sign_zero, zero_mul]
  · rw [Real.sign_of_pos ha, abs_of_pos ha, one_mul]

theorem realAbsEqSignMul (a : ℝ) : |a| = Real.sign a * a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [Real.sign_of_neg ha, abs_of_neg ha, neg_one_mul]
  · rw [Real.sign_zero, zero_mul, abs_zero]
  · rw [Real.sign_of_pos ha, abs_of_pos ha, one_mul]

theorem signNegation {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) :
    signValue (M.negValue (denote p.val.arg)) = M.negValue (denote p) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  simp only [signDenoteReal p r hr, hr, M.neg_numbers, ← Complex.ofReal_neg,
    signValue_number, Real.sign_neg]

theorem signProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SignObj (M := M) α))
    (q : Obj (M := M) (SignObj (M := M) β)) (reverseArgs : Bool) :
    signValue (if reverseArgs then M.mulValue (denote q.val.arg) (denote p.val.arg)
      else M.mulValue (denote p.val.arg) (denote q.val.arg)) =
      M.mulValue (denote p) (denote q) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd
  rw [signDenoteReal p a ha, signDenoteReal q b hb, ha, hb]
  cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, signValue_number, realSignMul, mul_comm]

theorem signTimesAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (signFirst : Bool) :
    (if signFirst then M.mulValue (denote p) (absValue (denote p.val.arg))
      else M.mulValue (absValue (denote p.val.arg)) (denote p)) = denote p.val.arg := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  rw [signDenoteReal p a ha, ha, absValue_number]
  cases signFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, mul_comm (|a|) (Real.sign a), realSignMulAbs]

theorem absEqualsSignTimes {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SignObj (M := M) α)) (signFirst : Bool) :
    absValue (denote p.val.arg) =
      (if signFirst then M.mulValue (denote p) (denote p.val.arg)
        else M.mulValue (denote p.val.arg) (denote p)) := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp p.wd
  rw [signDenoteReal p a ha, ha, absValue_number]
  cases signFirst <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers,
      ← Complex.ofReal_mul, mul_comm a (Real.sign a), ← realAbsEqSignMul]

theorem zeroSubValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.subValue (M.number 0) (denote a) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.sub_numbers, M.neg_numbers, zero_sub]

theorem negOneMulValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.mulValue (M.number (-1)) (denote a) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.mul_numbers, M.neg_numbers, neg_one_mul]

theorem mulNegOneValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (ha : In a C) :
    M.mulValue (denote a) (M.number (-1)) = M.negValue (denote a) := by
  obtain ⟨z, hz⟩ := (M.complex_members _).mp ha
  rw [hz, M.mul_numbers, M.neg_numbers, mul_neg_one]

end Litex

namespace Litex

noncomputable def roundingValue {M : Semantics.{u}} (ceiling : Bool)
    (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, a = M.number (r : ℂ)
    then M.number ((if ceiling then Int.ceil (Classical.choose h)
      else Int.floor (Classical.choose h) : ℤ) : ℂ)
    else M.number 0

theorem roundingValue_number {M : Semantics.{u}} (ceiling : Bool) (r : ℝ) :
    roundingValue ceiling (M.number (r : ℂ)) =
      M.number ((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold roundingValue
  rw [dif_pos h, hr]

structure RoundingObj {M : Semantics.{u}} (ceiling : Bool)
    (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance roundingRepresentation {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α] :
    Representation M (RoundingObj (M := M) ceiling α) where
  wd p := In p.arg R
  denote p := roundingValue ceiling (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨r, hr⟩ := (M.real_members _).mp h
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨if ceiling then Int.ceil r else Int.floor r, by rw [hr, roundingValue_number]⟩)

noncomputable def floor {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (RoundingObj (M := M) false α) :=
  ⟨⟨a⟩, h⟩

noncomputable def ceil {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a R) : Obj (M := M) (RoundingObj (M := M) true α) :=
  ⟨⟨a⟩, h⟩

theorem roundingDenoteReal {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α)) (r : ℝ)
    (hr : denote p.val.arg = M.number (r : ℂ)) :
    denote p = M.number ((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℂ) := by
  change roundingValue ceiling (denote p.val.arg) = _
  rw [hr, roundingValue_number]

theorem roundingInZ {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α)) : In p Z := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact (M.integer_members _).mpr ⟨_, roundingDenoteReal p r hr⟩

theorem roundingOfInteger {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α))
    (h : In p.val.arg Z) : Same p p.val.arg := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp h
  have hr : denote p.val.arg = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  change denote p = denote p.val.arg
  rw [roundingDenoteReal p (z : ℝ) hr, Int.ceil_intCast, Int.floor_intCast, ite_self, hz]

theorem floorLeArgument {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) false α)) : Le p p.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact ⟨(Int.floor r : ℝ), r, by
    simpa only [Complex.ofReal_intCast, Bool.false_eq_true, if_false] using roundingDenoteReal p r hr,
    hr, Int.floor_le r⟩

theorem argumentLeCeil {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (RoundingObj (M := M) true α)) : Le p.val.arg p := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd
  exact ⟨r, (Int.ceil r : ℝ), hr, by
    simpa only [Complex.ofReal_intCast, if_true] using roundingDenoteReal p r hr,
    Int.le_ceil r⟩

theorem floorStrictUpper {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (AddObj (M := M) (RoundingObj (M := M) false α) β))
    (h : Same q.val.right (number 1)) : Lt q.val.left.val.arg q := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.val.left.wd
  change denote q.val.right = M.number 1 at h
  refine ⟨r, (Int.floor r : ℝ) + 1, hr, ?_, Int.lt_floor_add_one r⟩
  change M.addValue (denote q.val.left) (denote q.val.right) = _
  rw [roundingDenoteReal q.val.left r hr, h, M.add_numbers,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_one]
  rfl

theorem ceilStrictLower {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (q : Obj (M := M) (SubObj (M := M) (RoundingObj (M := M) true α) β))
    (h : Same q.val.right (number 1)) : Lt q q.val.left.val.arg := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.val.left.wd
  change denote q.val.right = M.number 1 at h
  refine ⟨(Int.ceil r : ℝ) - 1, r, ?_, hr,
    (sub_lt_iff_lt_add).mpr (Int.ceil_lt_add_one r)⟩
  change M.subValue (denote q.val.left) (denote q.val.right) = _
  rw [roundingDenoteReal q.val.left r hr, h, M.sub_numbers,
    Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_one]
  rfl

theorem roundingMonotone {M : Semantics.{u}} {ceiling : Bool}
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (RoundingObj (M := M) ceiling α))
    (q : Obj (M := M) (RoundingObj (M := M) ceiling β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  obtain ⟨r, s, hr, hs, hrs⟩ := h
  refine ⟨((if ceiling then Int.ceil r else Int.floor r : ℤ) : ℝ),
    ((if ceiling then Int.ceil s else Int.floor s : ℤ) : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_intCast] using roundingDenoteReal p r hr
  · simpa only [Complex.ofReal_intCast] using roundingDenoteReal q s hs
  · cases ceiling
    · exact_mod_cast Int.floor_mono hrs
    · exact_mod_cast Int.ceil_mono hrs

end Litex

namespace Litex

/-- Fixed integer denotation; domain evidence is carried by each constructor. -/
noncomputable def integerDivisionValue {M : Semantics.{u}} (quotient : Bool)
    (a b : M.Value) : M.Value := by
  classical
  exact if h : ∃ p : ℤ × ℤ, a = M.number (p.1 : ℂ) ∧ b = M.number (p.2 : ℂ)
    then M.number ((if quotient then (Classical.choose h).1 / (Classical.choose h).2
      else (Classical.choose h).1 % (Classical.choose h).2 : ℤ) : ℂ)
    else M.number 0

theorem integerDivisionValue_numbers {M : Semantics.{u}} (quotient : Bool) (a b : ℤ) :
    integerDivisionValue quotient (M.number (a : ℂ)) (M.number (b : ℂ)) =
      M.number ((if quotient then a / b else a % b : ℤ) : ℂ) := by
  classical
  have h : ∃ p : ℤ × ℤ,
      M.number (a : ℂ) = M.number (p.1 : ℂ) ∧ M.number (b : ℂ) = M.number (p.2 : ℂ) :=
    ⟨(a, b), rfl, rfl⟩
  have hp : Classical.choose h = (a, b) := Prod.ext
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).1)).symm
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).2)).symm
  unfold integerDivisionValue
  rw [dif_pos h, hp]

structure ModObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure QuotObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance modRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (ModObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z ∧ ¬ Same p.right (number 0)
  denote p := integerDivisionValue false (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2.1
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨a % b, by rw [ha, hb, integerDivisionValue_numbers]; rfl⟩)

noncomputable instance quotRepresentation {M : Semantics.{u}} [SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β] :
    Representation M (QuotObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right NPos
  denote p := integerDivisionValue true (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ h.2))
    exact M.member_isSet ((M.integer_members _).mpr
      ⟨a / b, by rw [ha, hb, integerDivisionValue_numbers]; rfl⟩)

noncomputable def mod {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) (h0 : ¬ Same b (number 0)) : Obj (M := M) (ModObj (M := M) α β) :=
  ⟨⟨a, b⟩, ha, hb, h0⟩

noncomputable def quot {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b NPos) : Obj (M := M) (QuotObj (M := M) α β) :=
  ⟨⟨a, b⟩, ha, hb⟩

theorem modDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number ((a % b : ℤ) : ℂ) := by
  change integerDivisionValue false _ _ = _
  rw [ha, hb, integerDivisionValue_numbers]; rfl

theorem quotDenoteInt {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number ((a / b : ℤ) : ℂ) := by
  change integerDivisionValue true _ _ = _
  rw [ha, hb, integerDivisionValue_numbers]; rfl

theorem modInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β)) : In p Z := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  exact (M.integer_members _).mpr ⟨_, modDenoteInt p a b ha hb⟩

theorem quotInZ {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β)) : In p Z := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ p.wd.2))
  exact (M.integer_members _).mpr ⟨_, quotDenoteInt p a b ha hb⟩

theorem integerWitnessOfNPos {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α] (a : Obj (M := M) α) (h : In a NPos) :
    ∃ z : ℤ, denote a = M.number (z : ℂ) ∧ 0 < z := by
  obtain ⟨z, hz⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ h))
  obtain ⟨r, hr, hpos⟩ := ((S.sep_members _ _ _).mp h).2
  have heq : (z : ℝ) = r := Complex.ofReal_injective (by
    simpa only [Complex.ofReal_intCast] using M.number_injective (hz.symm.trans hr))
  refine ⟨z, hz, ?_⟩
  rw [← heq] at hpos
  exact_mod_cast hpos

theorem quotDecomposition {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (quotientFirst : Bool) :
    denote p.val.left = M.addValue
      (if quotientFirst then M.mulValue (denote p) (denote p.val.right)
       else M.mulValue (denote p.val.right) (denote p))
      (integerDivisionValue false (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp (naturalToInteger _ (inNPos_natural _ p.wd.2))
  rw [quotDenoteInt p a b ha hb, ha, hb, integerDivisionValue_numbers]
  cases quotientFirst <;> simp only [Bool.false_eq_true, if_false, if_true,
    M.mul_numbers, M.add_numbers]
  · exact congrArg M.number (by exact_mod_cast (Int.mul_ediv_add_emod a b).symm)
  · exact congrArg M.number (by exact_mod_cast (Int.ediv_mul_add_emod a b).symm)

theorem quotByOne {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (h : Same p.val.right (number 1)) : Same p p.val.left := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  change denote p.val.right = M.number 1 at h
  change denote p = denote p.val.left
  rw [quotDenoteInt p a 1 ha (by simpa only [Int.cast_one] using h), Int.ediv_one, ha]

theorem quotSelfOne {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (QuotObj (M := M) α β))
    (h : Same p.val.left p.val.right) (hp : In p.val.right NPos) : Same p (number 1) := by
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hp
  change denote p = M.number 1
  rw [quotDenoteInt p b b (h.trans hb) hb, Int.ediv_self (ne_of_gt hpos), Int.cast_one]

theorem modNonnegative {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (ha : In p.val.left Z) (hb : In p.val.right NPos) : Le (number 0) p := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp ha
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hb
  refine ⟨0, ((a % b : ℤ) : ℝ), ?_, ?_, ?_⟩
  · change M.number (0 : ℂ) = M.number ((0 : ℝ) : ℂ)
    rw [Complex.ofReal_zero]
  · simpa only [Complex.ofReal_intCast] using modDenoteInt p a b ha hb
  · exact_mod_cast Int.emod_nonneg a (ne_of_gt hpos)

theorem modStrictUpper {M : Semantics.{u}} [SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (ModObj (M := M) α β))
    (ha : In p.val.left Z) (hb : In p.val.right NPos) : Lt p p.val.right := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp ha
  obtain ⟨b, hb, hpos⟩ := integerWitnessOfNPos p.val.right hb
  refine ⟨((a % b : ℤ) : ℝ), (b : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_intCast] using modDenoteInt p a b ha hb
  · simpa only [Complex.ofReal_intCast] using hb
  · exact_mod_cast Int.emod_lt_of_pos a hpos

end Litex

namespace Litex

noncomputable def gcdLcmValue {M : Semantics.{u}} (least : Bool) (a b : M.Value) : M.Value := by
  classical
  exact if h : ∃ p : ℤ × ℤ, a = M.number (p.1 : ℂ) ∧ b = M.number (p.2 : ℂ)
    then M.number ((if least then Int.lcm (Classical.choose h).1 (Classical.choose h).2
      else Int.gcd (Classical.choose h).1 (Classical.choose h).2 : ℕ) : ℂ)
    else M.number 0

theorem gcdLcmValue_numbers {M : Semantics.{u}} (least : Bool) (a b : ℤ) :
    gcdLcmValue least (M.number (a : ℂ)) (M.number (b : ℂ)) =
      M.number ((if least then Int.lcm a b else Int.gcd a b : ℕ) : ℂ) := by
  classical
  have h : ∃ p : ℤ × ℤ,
      M.number (a : ℂ) = M.number (p.1 : ℂ) ∧ M.number (b : ℂ) = M.number (p.2 : ℂ) :=
    ⟨(a, b), rfl, rfl⟩
  have hp : Classical.choose h = (a, b) := Prod.ext
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).1)).symm
    (Int.cast_injective (M.number_injective (Classical.choose_spec h).2)).symm
  unfold gcdLcmValue
  rw [dif_pos h, hp]

structure GcdObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

structure LcmObj {M : Semantics.{u}} (α : Type v) (β : Type w)
    [Representation M α] [Representation M β] where
  left : Obj (M := M) α
  right : Obj (M := M) β

noncomputable instance gcdRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (GcdObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z ∧ (¬ Same p.left (number 0) ∨ ¬ Same p.right (number 0))
  denote p := gcdLcmValue false (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2.1
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨Int.gcd a b, by rw [ha, hb, gcdLcmValue_numbers]; rfl⟩)

noncomputable instance lcmRepresentation {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] : Representation M (LcmObj (M := M) α β) where
  wd p := In p.left Z ∧ In p.right Z
  denote p := gcdLcmValue true (denote p.left) (denote p.right)
  wd_isSet {p} h := by
    obtain ⟨a, ha⟩ := (M.integer_members _).mp h.1
    obtain ⟨b, hb⟩ := (M.integer_members _).mp h.2
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨Int.lcm a b, by rw [ha, hb, gcdLcmValue_numbers]; rfl⟩)

noncomputable def gcd {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) (h0 : ¬ Same a (number 0) ∨ ¬ Same b (number 0)) :
    Obj (M := M) (GcdObj (M := M) α β) := ⟨⟨a, b⟩, ha, hb, h0⟩

noncomputable def lcm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a Z) (hb : In b Z) : Obj (M := M) (LcmObj (M := M) α β) := ⟨⟨a, b⟩, ha, hb⟩

theorem gcdDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number (Int.gcd a b : ℂ) := by
  change gcdLcmValue false _ _ = _
  rw [ha, hb, gcdLcmValue_numbers]; rfl

theorem lcmDenoteInt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (a b : ℤ) (ha : denote p.val.left = M.number (a : ℂ))
    (hb : denote p.val.right = M.number (b : ℂ)) : denote p = M.number (Int.lcm a b : ℂ) := by
  change gcdLcmValue true _ _ = _
  rw [ha, hb, gcdLcmValue_numbers]; rfl

theorem lcmNonzeroOfArgs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (hla : ¬ Same p.val.left (number 0)) (hlb : ¬ Same p.val.right (number 0)) : ¬ Same p (number 0) := by
  obtain ⟨a,ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b,hb⟩ := (M.integer_members _).mp p.wd.2
  have ha0 : a ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.left (a : ℂ) ha hla
    exact_mod_cast h
  have hb0 : b ≠ 0 := by
    have h := NativeBridge.nativeNonzeroOfDenote p.val.right (b : ℂ) hb hlb
    exact_mod_cast h
  have hn : Int.lcm a b ≠ 0 := by
    rw [Int.lcm_eq_natAbs_lcm_natAbs]
    exact Nat.lcm_ne_zero (Int.natAbs_ne_zero.mpr ha0) (Int.natAbs_ne_zero.mpr hb0)
  apply NativeBridge.notSameOfNativeNonzero p (Int.lcm a b : ℂ) (lcmDenoteInt p a b ha hb)
  exact_mod_cast hn

theorem gcdInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) : In p N := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  exact (M.natural_members _).mpr ⟨_, gcdDenoteInt p a b ha hb⟩

theorem lcmInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β)) : In p N := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2
  exact (M.natural_members _).mpr ⟨_, lcmDenoteInt p a b ha hb⟩

theorem gcdPositiveWitness {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    ∃ n : ℕ, denote p = M.number (n : ℂ) ∧ 0 < n := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  refine ⟨Int.gcd a b, gcdDenoteInt p a b ha hb, Int.gcd_pos_iff.mpr ?_⟩
  rcases p.wd.2.2 with h | h
  · exact Or.inl (fun h0 => h (by change denote p.val.left = M.number 0; rw [ha, h0, Int.cast_zero]))
  · exact Or.inr (fun h0 => h (by change denote p.val.right = M.number 0; rw [hb, h0, Int.cast_zero]))

theorem gcdNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    ¬ Same p (number 0) := by
  obtain ⟨n, hn, hp⟩ := gcdPositiveWitness p
  intro h
  have hz : (n : ℂ) = 0 := M.number_injective (hn.symm.trans h)
  exact (Nat.ne_of_gt hp) (by exact_mod_cast hz)

theorem gcdInNPos {M : Semantics.{u}} [S : SetSemantics M] {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) : In p NPos := by
  obtain ⟨n, hn, hp⟩ := gcdPositiveWitness p
  apply (S.sep_members _ _ _).mpr
  refine ⟨gcdInN p, (n : ℝ), ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using hn
  · exact_mod_cast hp

theorem absValue_int {M : Semantics.{u}} (a : ℤ) :
    absValue (M.number (a : ℂ)) = M.number (a.natAbs : ℂ) := by
  rw [← Complex.ofReal_intCast, absValue_number]
  have h : |(a : ℝ)| = (a.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [h, Complex.ofReal_natCast]

theorem gcdCommutative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    denote p = gcdLcmValue false (denote p.val.right) (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers, Int.gcd_comm a b]; rfl

theorem lcmCommutative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β)) :
    denote p = gcdLcmValue true (denote p.val.right) (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2
  rw [lcmDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers, Int.lcm_comm a b]; rfl

theorem gcdSelfAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (h : Same p.val.left p.val.right) : denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  rw [gcdDenoteInt p a a ha (h.symm.trans ha), Int.gcd_self, ha, absValue_int]

theorem lcmSelfAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (LcmObj (M := M) α β))
    (h : Same p.val.left p.val.right) : denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  rw [lcmDenoteInt p a a ha (h.symm.trans ha), Int.lcm_self, ha, absValue_int]

theorem gcdRightZeroAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (hz : Same p.val.right (number 0)) (_hn : ¬ Same p.val.left (number 0)) :
    denote p = absValue (denote p.val.left) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  change denote p.val.right = M.number 0 at hz
  rw [gcdDenoteInt p a 0 ha (by simpa only [Int.cast_zero] using hz), Int.gcd_zero, ha, absValue_int]

theorem gcdLeftZeroAbs {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (hz : Same p.val.left (number 0)) (_hn : ¬ Same p.val.right (number 0)) :
    denote p = absValue (denote p.val.right) := by
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  change denote p.val.left = M.number 0 at hz
  rw [gcdDenoteInt p 0 b (by simpa only [Int.cast_zero] using hz) hb, Int.gcd_zero_left, hb, absValue_int]

theorem gcdEuclideanStep {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β)) :
    denote p = gcdLcmValue false (denote p.val.right)
      (integerDivisionValue false (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, integerDivisionValue_numbers]
  change M.number (Int.gcd a b : ℂ) = gcdLcmValue false (M.number (b : ℂ)) (M.number ((a % b : ℤ) : ℂ))
  rw [gcdLcmValue_numbers, Int.gcd_comm b (a % b), Int.gcd_emod]; rfl

theorem gcdLcmProduct {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β] (p : Obj (M := M) (GcdObj (M := M) α β))
    (gcdFirst reverseArgs : Bool) :
    (if gcdFirst then M.mulValue (denote p) (gcdLcmValue true (denote p.val.left) (denote p.val.right))
     else M.mulValue (gcdLcmValue true (denote p.val.left) (denote p.val.right)) (denote p)) =
    absValue (if reverseArgs then M.mulValue (denote p.val.right) (denote p.val.left)
      else M.mulValue (denote p.val.left) (denote p.val.right)) := by
  obtain ⟨a, ha⟩ := (M.integer_members _).mp p.wd.1
  obtain ⟨b, hb⟩ := (M.integer_members _).mp p.wd.2.1
  rw [gcdDenoteInt p a b ha hb, ha, hb, gcdLcmValue_numbers]
  cases gcdFirst <;> cases reverseArgs <;>
    simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers, ← Int.cast_mul, absValue_int]
  all_goals
    apply congrArg M.number
    norm_cast
    simp only [Int.gcd_mul_lcm, Int.natAbs_mul, Nat.mul_comm]

end Litex

namespace Litex

noncomputable def factorialValue {M : Semantics.{u}} (a : M.Value) : M.Value := by
  classical
  exact if h : ∃ n : ℕ, a = M.number (n : ℂ)
    then M.number ((Classical.choose h).factorial : ℂ) else M.number 0

theorem factorialValue_number {M : Semantics.{u}} (n : ℕ) :
    factorialValue (M.number (n : ℂ)) = M.number (n.factorial : ℂ) := by
  classical
  have h : ∃ k : ℕ, M.number (n : ℂ) = M.number (k : ℂ) := ⟨n, rfl⟩
  have hk : Classical.choose h = n :=
    (Nat.cast_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold factorialValue
  rw [dif_pos h, hk]

structure FactorialObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance factorialRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (FactorialObj (M := M) α) where
  wd p := In p.arg N
  denote p := factorialValue (denote p.arg)
  wd_isSet {p} h := by
    obtain ⟨n, hn⟩ := (M.natural_members _).mp h
    exact M.member_isSet ((M.natural_members _).mpr
      ⟨n.factorial, by rw [hn, factorialValue_number]⟩)

noncomputable def factorial {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h : In a N) : Obj (M := M) (FactorialObj (M := M) α) :=
  ⟨⟨a⟩, h⟩

theorem factorialDenoteNat {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) (n : ℕ)
    (hn : denote p.val.arg = M.number (n : ℂ)) : denote p = M.number (n.factorial : ℂ) := by
  change factorialValue _ = _
  rw [hn, factorialValue_number]

theorem factorialInN {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : In p N := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  exact (M.natural_members _).mpr ⟨_, factorialDenoteNat p n hn⟩

theorem factorialInNPos {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : In p NPos := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  apply (S.sep_members _ _ _).mpr
  refine ⟨factorialInN p, (n.factorial : ℝ), ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p n hn
  · exact_mod_cast Nat.factorial_pos n

theorem factorialNonzero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (FactorialObj (M := M) α)) : ¬ Same p (number 0) := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp p.wd
  intro h
  have hz : (n.factorial : ℂ) = 0 :=
    M.number_injective ((factorialDenoteNat p n hn).symm.trans h)
  exact Nat.factorial_ne_zero n (by exact_mod_cast hz)

/-- The two original certified factorial arguments differ by one. -/
theorem factorialStep {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (h : denote p.val.arg = M.addValue (denote q.val.arg) (M.number 1))
    (coefficientFirst : Bool) : denote p =
      (if coefficientFirst then M.mulValue (denote p.val.arg) (denote q)
       else M.mulValue (denote q) (denote p.val.arg)) := by
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hs : denote p.val.arg = M.number ((n + 1 : ℕ) : ℂ) := by
    rw [h, hn, M.add_numbers, Nat.cast_add, Nat.cast_one]
  rw [factorialDenoteNat p (n + 1) hs, factorialDenoteNat q n hn, hs]
  cases coefficientFirst <;> simp only [Bool.false_eq_true, if_false, if_true, M.mul_numbers]
  · rw [Nat.factorial_succ, Nat.cast_mul, mul_comm]
  · rw [Nat.factorial_succ, Nat.cast_mul]

theorem factorialMonotone {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  obtain ⟨m, hm⟩ := (M.natural_members _).mp p.wd
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hmr : denote p.val.arg = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hm
  have hnr : denote q.val.arg = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hmn : m ≤ n := by
    exact_mod_cast (NativeBridge.le_iff_ofDenoteReal _ _ _ _ hmr hnr).mp h
  refine ⟨(m.factorial : ℝ), (n.factorial : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p m hm
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat q n hn
  · exact_mod_cast Nat.factorial_le hmn

theorem factorialStrictMonotone {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (p : Obj (M := M) (FactorialObj (M := M) α))
    (q : Obj (M := M) (FactorialObj (M := M) β))
    (hp : In p.val.arg NPos) (h : Lt p.val.arg q.val.arg) : Lt p q := by
  obtain ⟨m, hm⟩ := (M.natural_members _).mp p.wd
  obtain ⟨n, hn⟩ := (M.natural_members _).mp q.wd
  have hmr : denote p.val.arg = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hm
  have hnr : denote q.val.arg = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hn
  have hmn : m < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hmr hnr).mp h
  have hm0 : 0 < m := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ 0 _ rfl hmr).mp (inNPos_positive _ hp)
  refine ⟨(m.factorial : ℝ), (n.factorial : ℝ), ?_, ?_, ?_⟩
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat p m hm
  · simpa only [Complex.ofReal_natCast] using factorialDenoteNat q n hn
  · exact_mod_cast Nat.factorial_lt_of_lt hm0 hmn

end Litex

namespace Litex

-- Replay the two endpoint alignments selected by the integer-gap rule.
-- The numeric observations belong to the original objects; they do not
-- replace their representations or introduce a new membership assumption.
theorem integerGapLe {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (l : Obj (M := M) γ) (r : Obj (M := M) δ)
    (ha : In a Z) (hb : In b Z) (hlt : Lt a b)
    (z w s t : ℂ)
    (hz : denote a = M.number z) (hw : denote b = M.number w)
    (hs : denote l = M.number s) (ht : denote r = M.number t)
    (h : (s = z + 1 ∧ t = w) ∨ (s = z ∧ t = w - 1)) : Le l r := by
  obtain ⟨m, hm⟩ := (M.integer_members _).mp ha
  obtain ⟨n, hn⟩ := (M.integer_members _).mp hb
  have hmr : denote a = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hm
  have hnr : denote b = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hn
  have hmn : m < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hmr hnr).mp hlt
  have hz' : z = ((m : ℝ) : ℂ) := M.number_injective (hz.symm.trans hmr)
  have hw' : w = ((n : ℝ) : ℂ) := M.number_injective (hw.symm.trans hnr)
  rcases h with ⟨hs', ht'⟩ | ⟨hs', ht'⟩
  · refine ⟨(m : ℝ) + 1, (n : ℝ), ?_, ?_, ?_⟩
    · simpa only [hs', hz', Complex.ofReal_add, Complex.ofReal_one] using hs
    · simpa only [ht', hw'] using ht
    · exact_mod_cast (show m + 1 ≤ n by omega)
  · refine ⟨(m : ℝ), (n : ℝ) - 1, ?_, ?_, ?_⟩
    · simpa only [hs', hz'] using hs
    · simpa only [ht', hw', Complex.ofReal_sub, Complex.ofReal_one] using ht
    · exact_mod_cast (show m ≤ n - 1 by omega)

theorem integerPredecessorLe {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (SubObj (M := M) β γ))
    (ha : In a Z) (hb : In p.val.left Z) (h1 : Same p.val.right (number 1))
    (hlt : Lt a p.val.left) : Le a p := by
  obtain ⟨m, hm⟩ := (M.integer_members _).mp ha
  obtain ⟨n, hn⟩ := (M.integer_members _).mp hb
  have hmr : denote a = M.number ((m : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hm
  have hnr : denote p.val.left = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hn
  have hmn : m < n := by
    exact_mod_cast (NativeBridge.lt_iff_ofDenoteReal _ _ _ _ hmr hnr).mp hlt
  have hpred : m ≤ n - 1 := by omega
  refine ⟨(m : ℝ), (n : ℝ) - 1, hmr, ?_, ?_⟩
  · change M.subValue (denote p.val.left) (denote p.val.right) = _
    change denote p.val.right = M.number 1 at h1
    rw [hnr, h1, M.sub_numbers, Complex.ofReal_sub, Complex.ofReal_one]
  · exact_mod_cast hpred

end Litex

