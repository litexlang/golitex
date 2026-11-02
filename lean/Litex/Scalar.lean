import Litex.Core

universe u v w x

namespace Litex

/-- The selected division/product conversion observes only its three operands. -/
theorem sameDivIffSameMul {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hc : In c C) (hb0 : ¬ Same b (number 0)) :
    Same (div a b ha hb hb0) c ↔ Same a (mul c b hc hb) := by
  have hb0' := NativeBridge.nativeNonzeroOfDenote b (NativeBridge.asComplex b hb)
    (NativeBridge.asComplex_spec b hb) hb0
  change M.divValue (denote a) (denote b) = denote c ↔
    denote a = M.mulValue (denote c) (denote b)
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec c hc, M.div_numbers _ _ hb0', M.mul_numbers,
    M.number_injective.eq_iff, M.number_injective.eq_iff]
  exact div_eq_iff hb0'

theorem sameMulComm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a C) (hb : In b C) :
    Same (mul a b ha hb) (mul b a hb ha) := by
  change M.mulValue (denote a) (denote b) = M.mulValue (denote b) (denote a)
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.mul_numbers, M.mul_numbers, mul_comm]

/-- A total raw interpretation is used only through an owned absolute-value
object whose original argument is certified real. -/
noncomputable def absValue {M : Semantics.{u}} (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((|Classical.choose h| : ℝ) : ℂ) else M.number 0

theorem absValue_number {M : Semantics.{u}} (r : ℝ) :
    absValue (M.number (r : ℂ)) = M.number ((|r| : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold absValue
  rw [dif_pos h, hr]

structure AbsObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance absRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (AbsObj (M := M) α) where
  wd a := In a.arg R
  denote a := absValue (denote a.arg)
  wd_isSet {a} ha := by
    obtain ⟨r, hr⟩ := (M.real_members (denote a.arg)).mp ha
    exact M.member_isSet ((M.real_members _).mpr ⟨|r|, by
      rw [hr, absValue_number]⟩)

noncomputable def abs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Obj (M := M) (AbsObj (M := M) α) :=
  ⟨⟨a⟩, haR⟩

namespace NativeBridge

theorem denoteAbs {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (r : ℝ)
    (hr : denote a = M.number (r : ℂ)) :
    denote (abs a haR) = M.number ((|r| : ℝ) : ℂ) := by
  change absValue (denote a) = _
  rw [hr, absValue_number]

end NativeBridge

theorem absInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In (abs a haR) R :=
  (M.real_members _).mpr ⟨|NativeBridge.asReal a haR|,
    NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)⟩

theorem absInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In (abs a haR) C :=
  realToComplex _ (absInR a haR)

/-- The absolute value of a nonzero real is nonzero. -/
theorem absNonzeroOfArg {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (AbsObj (M := M) α))
    (ha : ¬ Same p.val.arg (number 0)) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd
  have hr : denote p.val.arg = M.number ((r : ℝ) : ℂ) := NativeBridge.asReal_spec p.val.arg p.wd
  have hr0 : r ≠ 0 := by
    intro h
    apply ha
    change denote p.val.arg = M.number 0
    have hcast : (r : ℂ) = 0 := by exact_mod_cast h
    exact hr.trans (congrArg M.number hcast)
  have hroot : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr hr0)
  have hp : denote p = M.number ((|r| : ℝ) : ℂ) :=
    NativeBridge.denoteAbs p.val.arg p.wd r hr
  intro h
  exact hroot (M.number_injective (hp.symm.trans h))

theorem absNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Le (number 0) (abs a haR) :=
  NativeBridge.leOfDenoteReal _ _ 0 |NativeBridge.asReal a haR| rfl
    (NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)) (abs_nonneg _)

theorem absOfNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Same (abs a haR) a := by
  have h := (NativeBridge.le_iff_ofDenoteReal (number 0) a 0
    (NativeBridge.asReal a haR) rfl (NativeBridge.asReal_spec a haR)).mp ha0
  exact (NativeBridge.denoteAbs a haR _ (NativeBridge.asReal_spec a haR)).trans
    ((congrArg (fun r : ℝ => M.number (r : ℂ)) (abs_of_nonneg h)).trans
      (NativeBridge.asReal_spec a haR).symm)

/-- Principal real square root. Its total raw denotation is independent of WD;
the owned constructor below requires a real, nonnegative argument. -/
noncomputable def sqrtValue {M : Semantics.{u}} (x : M.Value) : M.Value := by
  classical
  exact if h : ∃ r : ℝ, x = M.number (r : ℂ) then
    M.number ((Real.sqrt (Classical.choose h) : ℝ) : ℂ) else M.number 0

theorem sqrtValue_number {M : Semantics.{u}} (r : ℝ) :
    sqrtValue (M.number (r : ℂ)) = M.number ((Real.sqrt r : ℝ) : ℂ) := by
  classical
  have h : ∃ s : ℝ, M.number (r : ℂ) = M.number (s : ℂ) := ⟨r, rfl⟩
  have hr : Classical.choose h = r :=
    (Complex.ofReal_injective (M.number_injective (Classical.choose_spec h))).symm
  unfold sqrtValue
  rw [dif_pos h, hr]

structure SqrtObj {M : Semantics.{u}} (α : Type v) [Representation M α] where
  arg : Obj (M := M) α

noncomputable instance sqrtRepresentation {M : Semantics.{u}} {α : Type v}
    [Representation M α] : Representation M (SqrtObj (M := M) α) where
  wd a := In a.arg R ∧ Le (number 0) a.arg
  denote a := sqrtValue (denote a.arg)
  wd_isSet {a} ha := by
    obtain ⟨r, hr⟩ := (M.real_members (denote a.arg)).mp ha.1
    exact M.member_isSet ((M.real_members _).mpr ⟨Real.sqrt r, by
      rw [hr, sqrtValue_number]⟩)

noncomputable def sqrt {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Obj (M := M) (SqrtObj (M := M) α) := ⟨⟨a⟩, haR, ha0⟩

namespace NativeBridge

theorem denoteSqrt {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) (r : ℝ)
    (hr : denote a = M.number (r : ℂ)) :
    denote (sqrt a haR ha0) = M.number ((Real.sqrt r : ℝ) : ℂ) := by
  change sqrtValue (denote a) = _
  rw [hr, sqrtValue_number]

end NativeBridge

theorem sqrtInR {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    In (sqrt a haR ha0) R :=
  (M.real_members _).mpr ⟨Real.sqrt (NativeBridge.asReal a haR),
    NativeBridge.denoteSqrt a haR ha0 _ (NativeBridge.asReal_spec a haR)⟩

theorem sqrtInC {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    In (sqrt a haR ha0) C := realToComplex _ (sqrtInR a haR ha0)

theorem sqrtNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    Le (number 0) (sqrt a haR ha0) :=
  NativeBridge.leOfDenoteReal _ _ 0 (Real.sqrt (NativeBridge.asReal a haR)) rfl
    (NativeBridge.denoteSqrt a haR ha0 _ (NativeBridge.asReal_spec a haR))
    (Real.sqrt_nonneg _)

/-- Defined principal square roots preserve the order of their arguments. -/
theorem sqrtMonotone {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (q : Obj (M := M) (SqrtObj (M := M) β))
    (h : Le p.val.arg q.val.arg) : Le p q := by
  let x := NativeBridge.asReal p.val.arg p.wd.1
  let y := NativeBridge.asReal q.val.arg q.wd.1
  have hx := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hy := NativeBridge.asReal_spec q.val.arg q.wd.1
  have hxy : x ≤ y := (NativeBridge.le_iff_ofDenoteReal p.val.arg q.val.arg x y hx hy).mp h
  exact NativeBridge.leOfDenoteReal p q (Real.sqrt x) (Real.sqrt y)
    (NativeBridge.denoteSqrt p.val.arg p.wd.1 p.wd.2 x hx)
    (NativeBridge.denoteSqrt q.val.arg q.wd.1 q.wd.2 y hy)
    (Real.sqrt_le_sqrt hxy)

/-- The principal square root of a positive real number is nonzero. -/
theorem sqrtNonzeroOfPositive {M : Semantics.{u}} {α : Type v} [Representation M α]
    (p : Obj (M := M) (SqrtObj (M := M) α))
    (hpos : Lt (number 0) p.val.arg) : ¬ Same p (number 0) := by
  let r := NativeBridge.asReal p.val.arg p.wd.1
  have hr := NativeBridge.asReal_spec p.val.arg p.wd.1
  have hr0 : 0 < r := (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.arg 0 r rfl hr).mp hpos
  have hroot : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hr0))
  have hp : denote p = M.number ((Real.sqrt r : ℝ) : ℂ) :=
    NativeBridge.denoteSqrt p.val.arg p.wd.1 p.wd.2 r hr
  intro h
  exact hroot (M.number_injective (hp.symm.trans h))

theorem sqrtSquareValue {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) (ha0 : Le (number 0) a) :
    M.powValue (denote (sqrt a haR ha0)) (M.number ((2 : ℕ) : ℂ)) = denote a := by
  let r := NativeBridge.asReal a haR
  have hr : denote a = M.number (r : ℂ) := NativeBridge.asReal_spec a haR
  have h0 : 0 ≤ r := (NativeBridge.le_iff_ofDenoteReal (number 0) a 0 r rfl hr).mp ha0
  rw [NativeBridge.denoteSqrt a haR ha0 r hr, M.pow_numbers_nat, ← Complex.ofReal_pow,
    Real.sq_sqrt h0, ← hr]

theorem addCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add a k ha hk) (add b k hb hk)) : Same a b := by
  change M.addValue (denote a) (denote k) = M.addValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (add_right_cancel (M.number_injective h))

theorem addCancelRightLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add a k ha hk) (add k b hk hb)) : Same a b := by
  change M.addValue (denote a) (denote k) = M.addValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  have he := M.number_injective h
  rw [add_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex b hb)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (add_right_cancel he)

theorem addCancelLeftRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add k a hk ha) (add b k hb hk)) : Same a b := by
  change M.addValue (denote k) (denote a) = M.addValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  have he := M.number_injective h
  rw [add_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex a ha)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (add_right_cancel he)

theorem addCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (add k a hk ha) (add k b hk hb)) : Same a b := by
  change M.addValue (denote k) (denote a) = M.addValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.add_numbers, M.add_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (add_left_cancel (M.number_injective h))

/-- Replay the selected unequal-operands rule for a nonzero difference. -/
theorem subNonzeroOfNotSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C) (hab : ¬ Same a b) :
    ¬ Same (sub a b ha hb) (number 0) := by
  intro h
  apply hab
  change M.subValue (denote a) (denote b) = M.number 0 at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr
    (sub_eq_zero.mp (M.number_injective h))

/-- Replay a cited zero difference using the original operands' certificates. -/
theorem sameOfSubZero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C)
    (hsub : Same (sub a b ha hb) (number 0)) : Same a b := by
  by_contra h
  exact (subNonzeroOfNotSame a b ha hb h) hsub

/-- Replay a known nonzero difference without searching for another inequality. -/
theorem notSameOfSubNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (ha : In a C) (hb : In b C)
    (hsub : ¬ Same (sub a b ha hb) (number 0)) : ¬ Same a b := by
  intro hab
  apply hsub
  change M.subValue (denote a) (denote b) = M.number 0
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    M.sub_numbers, (NativeBridge.same_iff_asComplex a b ha hb).mp hab, sub_self]

theorem notSameNegOfNonzeroSumLeft {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (q : Obj (M := M) γ)
    (hq : denote q = M.negValue (denote p.val.right))
    (h : ¬ Same p (number 0)) : ¬ Same p.val.left q := by
  intro he
  apply h
  change M.addValue (denote p.val.left) (denote p.val.right) = M.number 0
  change denote p.val.left = denote q at he
  rw [hq, NativeBridge.asComplex_spec p.val.right p.wd.2, M.neg_numbers] at he
  rw [he, NativeBridge.asComplex_spec p.val.right p.wd.2, M.add_numbers, neg_add_cancel]

theorem notSameNegOfNonzeroSumRight {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (AddObj (M := M) α β)) (q : Obj (M := M) γ)
    (hq : denote q = M.negValue (denote p.val.left))
    (h : ¬ Same p (number 0)) : ¬ Same p.val.right q := by
  intro he
  apply h
  change M.addValue (denote p.val.left) (denote p.val.right) = M.number 0
  change denote p.val.right = denote q at he
  rw [hq, NativeBridge.asComplex_spec p.val.left p.wd.1, M.neg_numbers] at he
  rw [he, NativeBridge.asComplex_spec p.val.left p.wd.1, M.add_numbers, add_neg_cancel]

/-- Replay the source's shared-subtrahend and shared-minuend cancellation rules. -/
theorem subCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (sub a k ha hk) (sub b k hb hk)) : Same a b := by
  change M.subValue (denote a) (denote k) = M.subValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.sub_numbers, M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (sub_left_inj.mp (M.number_injective h))

theorem subCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (h : Same (sub k a hk ha) (sub k b hk hb)) : Same a b := by
  change M.subValue (denote k) (denote a) = M.subValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.sub_numbers, M.sub_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (sub_right_inj.mp (M.number_injective h))

theorem mulCancelRightRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul a k ha hk) (mul b k hb hk)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote a) (denote k) =
    M.mulValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' (M.number_injective h))

theorem mulCancelRightLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul a k ha hk) (mul k b hk hb)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote a) (denote k) =
    M.mulValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  have he := M.number_injective h
  rw [mul_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex b hb)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' he)

theorem mulCancelLeftRight {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul k a hk ha) (mul b k hb hk)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote k) (denote a) =
    M.mulValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  have he := M.number_injective h
  rw [mul_comm (NativeBridge.asComplex k hk) (NativeBridge.asComplex a ha)] at he
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_right_cancel₀ hk0' he)

theorem mulCancelLeftLeft {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (mul k a hk ha) (mul k b hk hb)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.mulValue (denote k) (denote a) =
    M.mulValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.mul_numbers, M.mul_numbers] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_left_cancel₀ hk0' (M.number_injective h))

theorem divCancelCommonDenominator {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0))
    (h : Same (div a k ha hk hk0) (div b k hb hk hk0)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  change M.divValue (denote a) (denote k) = M.divValue (denote b) (denote k) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.div_numbers _ _ hk0', M.div_numbers _ _ hk0'] at h
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr ((div_left_inj' hk0').mp (M.number_injective h))

theorem divCancelNonzeroNumerator {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (k : Obj (M := M) γ)
    (ha : In a C) (hb : In b C) (hk : In k C)
    (hk0 : ¬ Same k (number 0)) (ha0 : ¬ Same a (number 0))
    (hb0 : ¬ Same b (number 0))
    (h : Same (div k a hk ha ha0) (div k b hk hb hb0)) : Same a b := by
  have hk0' := NativeBridge.nativeNonzeroOfDenote k (NativeBridge.asComplex k hk)
    (NativeBridge.asComplex_spec k hk) hk0
  have ha0' := NativeBridge.nativeNonzeroOfDenote a (NativeBridge.asComplex a ha)
    (NativeBridge.asComplex_spec a ha) ha0
  have hb0' := NativeBridge.nativeNonzeroOfDenote b (NativeBridge.asComplex b hb)
    (NativeBridge.asComplex_spec b hb) hb0
  change M.divValue (denote k) (denote a) = M.divValue (denote k) (denote b) at h
  rw [NativeBridge.asComplex_spec a ha, NativeBridge.asComplex_spec b hb,
    NativeBridge.asComplex_spec k hk, M.div_numbers _ _ ha0', M.div_numbers _ _ hb0'] at h
  have he := (div_eq_div_iff ha0' hb0').mp (M.number_injective h)
  exact (NativeBridge.same_iff_asComplex a b ha hb).mpr (mul_left_cancel₀ hk0' he).symm


theorem leOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (hab : Same a b) (hcd : Same c d) (hac : Le a c) : Le b d := by
  obtain ⟨r, s, hr, hs, h⟩ := hac
  exact ⟨r, s, hab.symm.trans hr, hcd.symm.trans hs, h⟩

theorem ltOfSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (hab : Same a b) (hcd : Same c d) (hac : Lt a c) : Lt b d := by
  obtain ⟨r, s, hr, hs, h⟩ := hac
  exact ⟨r, s, hab.symm.trans hr, hcd.symm.trans hs, h⟩

theorem leRefl {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : Le a a := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp haR
  exact ⟨r, r, hr, hr, le_refl r⟩

theorem sameOfLeAntisymm {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (hab : Le a b) (hba : Le b a) : Same a b := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', r', hs', hr', hsr⟩ := hba
  have er : r = r' := Complex.ofReal_injective (M.number_injective (hr.symm.trans hr'))
  have es : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  have h : r = s := le_antisymm hrs (by simpa only [← er, ← es] using hsr)
  exact hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) h).trans hs.symm)

theorem leSelfAddRight {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (haR : In p.val.left R) (hb : Le (number 0) p.val.right) : Le p.val.left p := by
  obtain ⟨a, ha⟩ := (M.real_members _).mp haR
  obtain ⟨z, b, hz, hb, hzb⟩ := hb
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  refine ⟨a, a + b, ha, ?_, le_add_of_nonneg_right (by simpa only [hz0] using hzb)⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [ha, hb, M.add_numbers, Complex.ofReal_add]

theorem leSelfAddLeft {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (hbR : In p.val.right R) (ha : Le (number 0) p.val.left) : Le p.val.right p := by
  obtain ⟨b, hb⟩ := (M.real_members _).mp hbR
  obtain ⟨z, a, hz, ha, hza⟩ := ha
  have hz0 : z = 0 := Complex.ofReal_injective (M.number_injective hz).symm
  refine ⟨b, a + b, hb, ?_, le_add_of_nonneg_left (by simpa only [hz0] using hza)⟩
  change M.addValue (denote p.val.left) (denote p.val.right) = _
  rw [ha, hb, M.add_numbers, Complex.ofReal_add]

theorem ltAddOfLeOfPos {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (p : Obj (M := M) (AddObj (M := M) β γ))
    (ha : Le a p.val.left) (hb : Lt (number 0) p.val.right) : Lt a p := by
  obtain ⟨a', x', ha', hx', hax⟩ := ha
  obtain ⟨z', y', hz', hy', hzy⟩ := hb
  have hz0 : z' = 0 := Complex.ofReal_injective (M.number_injective hz').symm
  refine ⟨a', x' + y', ha', ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [hx', hy', M.add_numbers, Complex.ofReal_add]
  · have hpos : (0 : ℝ) < y' := hz0 ▸ hzy
    exact lt_of_le_of_lt hax (lt_add_of_pos_right x' hpos)

theorem addLtAdd {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.left) (h₂ : Lt p.val.right q.val.right) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, b + d, ?_, ?_, add_lt_add hab hcd⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hb, hd, M.add_numbers, Complex.ofReal_add]

theorem addStructuralLtLeft {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (AddObj (M := M) α β))
    (rhs : Obj (M := M) (AddObj (M := M) γ δ))
    (hSum : In lhs R)
    (hOrder : Lt lhs.val.right rhs.val.right)
    (hSame : Same lhs.val.left rhs.val.left) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hSum
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.1
  have hsum : z + (a : ℂ) = (r : ℂ) := by
    apply M.number_injective
    change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.add_numbers] using hr
  have hc : denote lhs.val.left = M.number ((r - a : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (eq_sub_iff_add_eq.mpr hsum)
  refine NativeBridge.ltOfDenoteReal lhs rhs ((r - a) + a) ((r - a) + b) ?_ ?_ (add_lt_add_right hab (r - a))
  · change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.add_numbers, Complex.ofReal_add]

theorem addStructuralLtRight {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (lhs : Obj (M := M) (AddObj (M := M) α β))
    (rhs : Obj (M := M) (AddObj (M := M) γ δ))
    (hSum : In lhs R)
    (hOrder : Lt lhs.val.left rhs.val.left)
    (hSame : Same lhs.val.right rhs.val.right) : Lt lhs rhs := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp hSum
  obtain ⟨a, b, ha, hb, hab⟩ := hOrder
  obtain ⟨z, hz⟩ := (M.complex_members _).mp lhs.wd.2
  have hsum : (a : ℂ) + z = (r : ℂ) := by
    apply M.number_injective
    change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _ at hr
    simpa only [hz, ha, M.add_numbers] using hr
  have hc : denote lhs.val.right = M.number ((r - a : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_sub]
    exact congrArg M.number (eq_sub_iff_add_eq.mpr ((add_comm z (a : ℂ)).trans hsum))
  refine NativeBridge.ltOfDenoteReal lhs rhs (a + (r - a)) (b + (r - a)) ?_ ?_ (add_lt_add_left hab (r - a))
  · change M.addValue (denote lhs.val.left) (denote lhs.val.right) = _
    rw [hc, ha, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote rhs.val.left) (denote rhs.val.right) = _
    rw [hSame.symm.trans hc, hb, M.add_numbers, Complex.ofReal_add]

theorem addLtAddSwap {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (AddObj (M := M) α β))
    (q : Obj (M := M) (AddObj (M := M) γ δ))
    (h₁ : Lt p.val.left q.val.right) (h₂ : Lt p.val.right q.val.left) : Lt p q := by
  obtain ⟨a, b, ha, hb, hab⟩ := h₁
  obtain ⟨c, d, hc, hd, hcd⟩ := h₂
  refine ⟨a + c, d + b, ?_, ?_, ?_⟩
  · change M.addValue (denote p.val.left) (denote p.val.right) = _
    rw [ha, hc, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote q.val.left) (denote q.val.right) = _
    rw [hd, hb, M.add_numbers, Complex.ofReal_add]
  · simpa only [add_comm b d] using add_lt_add hab hcd

theorem naturalNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haN : In a N) : Le (number 0) a := by
  obtain ⟨n, hn⟩ := (M.natural_members (denote a)).mp haN
  refine ⟨0, (n : ℝ), ?_, ?_, Nat.cast_nonneg n⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · simpa only [Complex.ofReal_natCast] using hn

theorem ltToLe {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (hab : Lt a b) : Le a b := by
  obtain ⟨r, s, hr, hs, h⟩ := hab
  exact ⟨r, s, hr, hs, le_of_lt h⟩

theorem leEqOrLt {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (h : Le a b) : Same a b ∨ Lt a b := by
  obtain ⟨r, s, hr, hs, hrs⟩ := h
  rcases eq_or_lt_of_le hrs with equal | strict
  · exact Or.inl (hr.trans ((congrArg (fun x : ℝ => M.number (x : ℂ)) equal).trans hs.symm))
  · exact Or.inr ⟨r, s, hr, hs, strict⟩

/-- The selected integer-tail certificate retains both original integer
memberships even though the checked order alternative also holds for reals. -/
theorem integerSuccessorTail {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (subject : Obj (M := M) α) (base : Obj (M := M) β)
    (_hSubjectZ : In subject Z) (_hBaseZ : In base Z) (hLower : Le base subject) :
    Same subject base ∨ Lt base subject := by
  rcases leEqOrLt base subject hLower with equal | strict
  · exact Or.inl equal.symm
  · exact Or.inr strict

theorem ltNotSame {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (hab : Lt a b) : ¬ Same a b := by
  obtain ⟨r, s, hr, hs, h⟩ := hab
  intro equal
  exact (ne_of_lt h)
    (Complex.ofReal_injective (M.number_injective (hr.symm.trans (equal.trans hs))))

/-- Replay positivity of an owned sum using its original constructor evidence. -/
theorem addPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (add a b haC hbC) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  refine NativeBridge.ltOfDenoteReal (number 0) (add a b haC hbC) 0 (r + s)
    rfl ?_ (add_pos hposR hposS)
  change M.addValue (denote a) (denote b) = M.number ((r + s : ℝ) : ℂ)
  rw [hr, hs, M.add_numbers, Complex.ofReal_add]

/-- Replay the selected positive/positive quotient rule. The semantic
denominator proof still comes from the original division constructor. -/
theorem divPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (hNonzero : ¬ Same b (number 0))
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (div a b haC hbC hNonzero) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  have hsNonzero : (s : ℂ) ≠ 0 := fun h => hNonzero (hs.trans (congrArg M.number h))
  refine NativeBridge.ltOfDenoteReal (number 0) (div a b haC hbC hNonzero) 0 (r / s)
    rfl ?_ (div_pos hposR hposS)
  change M.divValue (denote a) (denote b) = M.number ((r / s : ℝ) : ℂ)
  rw [hr, hs, M.div_numbers _ _ hsNonzero, Complex.ofReal_div]

theorem mulPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C)
    (ha : Lt (number 0) a) (hb : Lt (number 0) b) :
    Lt (number 0) (mul a b haC hbC) := by
  obtain ⟨r₀, r, hzeroR, hr, hposR⟩ := ha
  obtain ⟨s₀, s, hzeroS, hs, hposS⟩ := hb
  change M.number 0 = M.number (r₀ : ℂ) at hzeroR
  change M.number 0 = M.number (s₀ : ℂ) at hzeroS
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroR).symm
  have hs₀ : s₀ = 0 := Complex.ofReal_injective (M.number_injective hzeroS).symm
  subst r₀
  subst s₀
  refine NativeBridge.ltOfDenoteReal (number 0) (mul a b haC hbC) 0 (r * s)
    rfl ?_ (mul_pos hposR hposS)
  change M.mulValue (denote a) (denote b) = M.number ((r * s : ℝ) : ℂ)
  rw [hr, hs, M.mul_numbers, Complex.ofReal_mul]

theorem powStructuralPositiveOfPositive {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (hbase : Lt (number 0) p.val.base) : Lt (number 0) p := by
  obtain ⟨r₀, r, hzero, hr, hpos⟩ := hbase
  change M.number 0 = M.number (r₀ : ℂ) at hzero
  have hr₀ : r₀ = 0 := Complex.ofReal_injective (M.number_injective hzero).symm
  subst r₀
  rcases p.wd with ⟨_haR, n, _heN, he⟩ | ⟨_haC, n, _heN, he⟩ |
    ⟨_haC, z, _heZ, ha0, he⟩
  · refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (pow_pos hpos n)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]
  · refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (pow_pos hpos n)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (n : ℂ) at he
    rw [hr, he, M.pow_numbers_nat, Complex.ofReal_pow]
  · have hr0 : (r : ℂ) ≠ 0 := fun h => ha0 (hr.trans (congrArg M.number h))
    refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ z) rfl ?_ (zpow_pos hpos z)
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    change denote p.val.exponent = M.number (z : ℂ) at he
    rw [hr, he, M.pow_numbers_int _ _ hr0, Complex.ofReal_zpow]

theorem powStructuralPositiveOfEven {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haR : In p.val.base R)
    (n : ℕ) (heValue : Same p.val.exponent (number (n : ℂ)))
    (hEven : Even n) (_hPositive : 0 < n)
    (hBaseNonzero : ¬ Same p.val.base (number 0)) : Lt (number 0) p := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.base)).mp haR
  have hr0 : r ≠ 0 := by
    intro h
    apply hBaseNonzero
    change denote p.val.base = M.number 0
    rw [hr, h, Complex.ofReal_zero]
  refine NativeBridge.ltOfDenoteReal (number 0) p 0 (r ^ n) rfl ?_ (hEven.pow_pos hr0)
  change M.powValue (denote p.val.base) (denote p.val.exponent) = _
  change denote p.val.exponent = M.number (n : ℂ) at heValue
  rw [hr, heValue, M.pow_numbers_nat, Complex.ofReal_pow]

/-- Monotonicity consumes the captured nonnegative lower base and ordered bases. -/
theorem powStructuralLe {M : Semantics.{u}} {α β γ δ : Type*}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (left : Obj (M := M) (PowObj (M := M) α β))
    (right : Obj (M := M) (PowObj (M := M) γ δ)) (n : ℕ)
    (heL : Same left.val.exponent (number (n : ℂ)))
    (heR : Same right.val.exponent (number (n : ℂ)))
    (h0 : Le (number 0) left.val.base)
    (hle : Le left.val.base right.val.base) : Le left right := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hle
  have hr0 : 0 ≤ r :=
    (NativeBridge.le_iff_ofDenoteReal (number 0) left.val.base 0 r rfl hr).mp h0
  refine NativeBridge.leOfDenoteReal left right (r ^ n) (s ^ n) ?_ ?_
    (pow_le_pow_left₀ hr0 hrs n)
  · change M.powValue (denote left.val.base) (denote left.val.exponent) = _
    change denote left.val.exponent = M.number (n : ℂ) at heL
    rw [hr, heL, M.pow_numbers_nat, Complex.ofReal_pow]
  · change M.powValue (denote right.val.base) (denote right.val.exponent) = _
    change denote right.val.exponent = M.number (n : ℂ) at heR
    rw [hs, heR, M.pow_numbers_nat, Complex.ofReal_pow]

theorem absPowStructuralSame {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (left : Obj (M := M) (PowObj (M := M) (AbsObj (M := M) α) β))
    (right : Obj (M := M) (PowObj (M := M) α γ)) (n : ℕ)
    (hBase : Same left.val.base.val.arg right.val.base)
    (heL : Same left.val.exponent (number (n : ℂ)))
    (heR : Same right.val.exponent (number (n : ℂ))) (hEven : Even n) : Same left right := by
  obtain ⟨r, hr⟩ := (M.real_members (denote left.val.base.val.arg)).mp left.val.base.wd
  have hrRight : denote right.val.base = M.number (r : ℂ) := hBase.symm.trans hr
  change M.powValue (absValue (denote left.val.base.val.arg)) (denote left.val.exponent) =
    M.powValue (denote right.val.base) (denote right.val.exponent)
  change denote left.val.exponent = M.number (n : ℂ) at heL
  change denote right.val.exponent = M.number (n : ℂ) at heR
  rw [hr, hrRight, heL, heR, absValue_number, M.pow_numbers_nat, M.pow_numbers_nat,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow, hEven.pow_abs]

theorem leTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Le a b) (hbc : Le b c) : Le a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, le_trans hrs (middle ▸ hst)⟩

theorem ltTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Lt a b) (hbc : Lt b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_trans hrs (middle ▸ hst)⟩

theorem ltLeTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Lt a b) (hbc : Le b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_of_lt_of_le hrs (middle ▸ hst)⟩

theorem leLtTrans {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (hab : Le a b) (hbc : Lt b c) : Lt a c := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨s', t, hs', ht, hst⟩ := hbc
  have middle : s = s' := Complex.ofReal_injective (M.number_injective (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, lt_of_le_of_lt hrs (middle ▸ hst)⟩

theorem integerToNaturalOfNonnegative {M : Semantics.{u}} {α : Type v}
    [Representation M α]
    (a : Obj (M := M) α) (haZ : In a Z) (ha0 : Le (number 0) a) : In a N := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  obtain ⟨r, s, hr, hs, hrs⟩ := ha0
  change M.number 0 = M.number (r : ℂ) at hr
  have hr0 : r = 0 := Complex.ofReal_injective (M.number_injective hr).symm
  have hsz : s = (z : ℝ) := Complex.ofReal_injective (by
    have hcast : (s : ℂ) = (z : ℂ) := M.number_injective (hs.symm.trans hz)
    exact_mod_cast hcast)
  have nonnegative : (0 : ℝ) ≤ (z : ℝ) := by simpa only [hr0, hsz] using hrs
  have hz0 : 0 ≤ z := by exact_mod_cast nonnegative
  have castEq : (z.toNat : ℂ) = (z : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hz0
  exact (M.natural_members _).mpr ⟨z.toNat, hz.trans (congrArg M.number castEq.symm)⟩

theorem integerSuccessorLowerBound {M : Semantics.{u}} {α : Type v}
    [Representation M α] (a : Obj (M := M) α) (haZ : In a Z)
    (h0a : Lt (number 0) a) : Le (number 1) a := by
  obtain ⟨z, hz⟩ := (M.integer_members (denote a)).mp haZ
  have hzReal : denote a = M.number ((z : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_intCast] using hz
  have hpos : (0 : ℝ) < (z : ℝ) :=
    (NativeBridge.lt_iff_ofDenoteReal (number 0) a 0 (z : ℝ) rfl hzReal).mp h0a
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hpos
  have hzOne : (1 : ℤ) ≤ z := Int.add_one_le_iff.mpr hzpos
  exact NativeBridge.leOfDenoteReal (number 1) a 1 (z : ℝ) rfl hzReal
    (by exact_mod_cast hzOne)

theorem subNonnegative {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β))
    (hba : Le p.val.right p.val.left) : Le (number 0) p := by
  obtain ⟨s, r, hs, hr, hsr⟩ := hba
  refine NativeBridge.leOfDenoteReal (number 0) p 0 (r - s) rfl ?_ (sub_nonneg.mpr hsr)
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  rw [hr, hs, M.sub_numbers, Complex.ofReal_sub]

theorem subtractOneLess {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β)) (haR : In p.val.left R)
    (hOne : Same p.val.right (number 1)) : Lt p p.val.left := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.left)).mp haR
  refine NativeBridge.ltOfDenoteReal p p.val.left (r - 1) r ?_ hr
    (sub_lt_self r zero_lt_one)
  change M.subValue (denote p.val.left) (denote p.val.right) = _
  change denote p.val.right = M.number 1 at hOne
  rw [hr, hOne, M.sub_numbers, Complex.ofReal_sub, Complex.ofReal_one]

theorem predecessorInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (SubObj (M := M) α β)) (hn : In p.val.left N)
    (hPositive : Lt (number 0) p.val.left)
    (hOne : Same p.val.right (number 1)) : In p N := by
  let n := NativeBridge.asNat p.val.left hn
  have hs : denote p.val.left = M.number (n : ℂ) := NativeBridge.asNat_spec p.val.left hn
  have hr : denote p.val.left = M.number ((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hs
  have hpos : (0 : ℝ) < (n : ℝ) :=
    (NativeBridge.lt_iff_ofDenoteReal (number 0) p.val.left 0 (n : ℝ) rfl hr).mp hPositive
  have hnpos : 0 < n := by exact_mod_cast hpos
  exact (M.natural_members _).mpr ⟨n - 1, by
    change M.subValue (denote p.val.left) (denote p.val.right) = _
    change denote p.val.right = M.number 1 at hOne
    rw [hs, hOne, M.sub_numbers,
      Nat.cast_sub (Nat.succ_le_of_lt hnpos), Nat.cast_one]⟩

theorem weakIntegerLowerBoundInN {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (bound : Obj (M := M) α) (a : Obj (M := M) β)
    (haZ : In a Z) (hbound : Le (number 0) bound) (h : Le bound a) : In a N :=
  integerToNaturalOfNonnegative a haZ (leTrans (number 0) bound a hbound h)

theorem leAdd {M : Semantics.{u}} {α : Type v} {β : Type w}
    {γ : Type x} {δ : Type*}
    [Representation M α] [Representation M β]
    [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (c : Obj (M := M) γ) (d : Obj (M := M) δ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hdC : In d C)
    (hab : Le a b) (hcd : Le c d) :
    Le (add a c haC hcC) (add b d hbC hdC) := by
  obtain ⟨r, s, hr, hs, hrs⟩ := hab
  obtain ⟨t, v, ht, hv, htv⟩ := hcd
  refine ⟨r + t, s + v, ?_, ?_, add_le_add hrs htv⟩
  · change M.addValue (denote a) (denote c) = _
    rw [hr, ht, M.add_numbers, Complex.ofReal_add]
  · change M.addValue (denote b) (denote d) = _
    rw [hs, hv, M.add_numbers, Complex.ofReal_add]

theorem leAddRight {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hcR : In c R)
    (hab : Le a b) : Le (add a c haC hcC) (add b c hbC hcC) :=
  leAdd a b c c haC hbC hcC hcC hab (leRefl c hcR)

theorem leAddLeft {M : Semantics.{u}} {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (haC : In a C) (hbC : In b C) (hcC : In c C) (hcR : In c R)
    (hab : Le a b) : Le (add c a hcC haC) (add c b hcC hbC) :=
  leAdd c c a b hcC hcC haC hbC (leRefl c hcR) hab

theorem mulSelfNonnegative {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) :
    Le (number 0) (mul a a (realToComplex a haR) (realToComplex a haR)) := by
  obtain ⟨r, hr⟩ := (M.real_members (denote a)).mp haR
  refine ⟨0, r * r, ?_, ?_, mul_self_nonneg r⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · change M.mulValue (denote a) (denote a) = _
    rw [hr, M.mul_numbers, Complex.ofReal_mul]

/-- Replay the exact even natural exponent independently of which supported
power WD alternative certified the owned object. -/
theorem powStructuralNonnegativeOfEven {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) (haR : In p.val.base R)
    (n : ℕ) (heValue : Same p.val.exponent (number (n : ℂ))) (hEven : Even n) :
    Le (number 0) p := by
  obtain ⟨r, hr⟩ := (M.real_members (denote p.val.base)).mp haR
  refine ⟨0, r ^ n, ?_, ?_, hEven.pow_nonneg r⟩
  · simp only [denote, number, Representation.denote, Complex.ofReal_zero]
  · change denote p.val.exponent = M.number (n : ℂ) at heValue
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hr, heValue, M.pow_numbers_nat, Complex.ofReal_pow]

/-- A nonzero product has two nonzero factors. -/
theorem productNonzeroFactors {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (MulObj (M := M) α β))
    (h : ¬ Same p (number 0)) :
    (¬ Same p.val.left (number 0)) ∧ (¬ Same p.val.right (number 0)) := by
  obtain ⟨x, hx⟩ := (M.complex_members (denote p.val.left)).mp p.wd.1
  obtain ⟨y, hy⟩ := (M.complex_members (denote p.val.right)).mp p.wd.2
  constructor
  · intro ha
    have hx0 : x = 0 := M.number_injective (hx.symm.trans ha)
    apply h
    change M.mulValue (denote p.val.left) (denote p.val.right) = M.number 0
    rw [hx, hy, M.mul_numbers, hx0, zero_mul]
  · intro hb
    have hy0 : y = 0 := M.number_injective (hy.symm.trans hb)
    apply h
    change M.mulValue (denote p.val.left) (denote p.val.right) = M.number 0
    rw [hx, hy, M.mul_numbers, hy0, mul_zero]

theorem mulNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C)
    (ha0 : ¬ Same a (number 0)) (hb0 : ¬ Same b (number 0)) :
    ¬ Same (mul a b haC hbC) (number 0) := by
  let x := NativeBridge.asComplex a haC
  let y := NativeBridge.asComplex b hbC
  have hx := NativeBridge.asComplex_spec a haC
  have hy := NativeBridge.asComplex_spec b hbC
  exact NativeBridge.notSameOfNativeNonzero _ (x * y)
    (NativeBridge.denoteMul a b haC hbC x y hx hy)
    (mul_ne_zero (NativeBridge.nativeNonzeroOfDenote a x hx ha0)
      (NativeBridge.nativeNonzeroOfDenote b y hy hb0))

theorem divNonzero {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C)
    (ha0 : ¬ Same a (number 0)) (hb0 : ¬ Same b (number 0)) :
    ¬ Same (div a b haC hbC hb0) (number 0) := by
  let x := NativeBridge.asComplex a haC
  let y := NativeBridge.asComplex b hbC
  have hx := NativeBridge.asComplex_spec a haC
  have hy := NativeBridge.asComplex_spec b hbC
  exact NativeBridge.notSameOfNativeNonzero _ (x / y)
    (NativeBridge.denoteDiv a b haC hbC hb0 x y hx hy)
    (div_ne_zero (NativeBridge.nativeNonzeroOfDenote a x hx ha0)
      (NativeBridge.nativeNonzeroOfDenote b y hy hb0))

end Litex

