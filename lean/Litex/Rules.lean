import Litex.Core

namespace Litex.Rules

universe u

/-- Ordinary upward induction over the exact integer observation selected by
the statement-result compiler. The compiler remains responsible for proving
that the Litex `Z` binder and lower-bound Result render to these native integer
premises; this theorem only packages Mathlib's reviewed induction principle. -/
theorem integerInductionFrom
    {motive : ℤ → Prop}
    {start : ℤ}
    (base : motive start)
    (step : ∀ value : ℤ, start ≤ value → motive value → motive (value + 1)) :
    ∀ value : ℤ, start ≤ value → motive value :=
  Int.leInduction base step

theorem complexInC (z : ℂ) : Litex.In z Litex.C :=
  Litex.In.own Litex.C z

theorem complexAddInC (a b : ℂ) : Litex.In (a + b) Litex.C :=
  complexInC (a + b)

theorem complexSubInC (a b : ℂ) : Litex.In (a - b) Litex.C :=
  complexInC (a - b)

theorem complexMulInC (a b : ℂ) : Litex.In (a * b) Litex.C :=
  complexInC (a * b)

theorem complexDivInC (a b : ℂ) : Litex.In (a / b) Litex.C :=
  complexInC (a / b)

/-- Complex modulus is multiplicative, stated in the heterogeneous equality
used by compiled Litex facts. -/
theorem absMul (a b : ℂ) :
    Litex.Same (Litex.abs (a * b)) (Litex.abs a * Litex.abs b) := by
  apply Litex.Same.ofEq
  simp [Litex.abs]

theorem absNonnegative (z : ℂ) : Litex.Nonnegative (Litex.abs z) := by
  exact ⟨‖z‖, by simpa [Litex.abs] using Litex.AsReal.complex ‖z‖, norm_nonneg z⟩

/-- Convert the exact zero-ended order selected for an `R` binder into the
semantic sign interface used by compound arithmetic rules. This theorem is
deliberately restricted to an explicit native real cast. -/
theorem realCastNonnegative (r : ℝ) (h : Litex.Le (0 : ℂ) (r : ℂ)) :
    Litex.Nonnegative (r : ℂ) := by
  exact ⟨r, Litex.AsReal.complex r, by simpa [Litex.Le, Litex.OrderValue] using h⟩

theorem realCastPositive (r : ℝ) (h : Litex.Lt (0 : ℂ) (r : ℂ)) :
    Litex.Positive (r : ℂ) := by
  exact ⟨r, Litex.AsReal.complex r, by simpa [Litex.Lt, Litex.OrderValue] using h⟩

theorem realCastNonpositive (r : ℝ) (h : Litex.Le (r : ℂ) (0 : ℂ)) :
    Litex.Nonpositive (r : ℂ) := by
  exact ⟨r, Litex.AsReal.complex r, by simpa [Litex.Le, Litex.OrderValue] using h⟩

theorem realCastNegative (r : ℝ) (h : Litex.Lt (r : ℂ) (0 : ℂ)) :
    Litex.Negative (r : ℂ) := by
  exact ⟨r, Litex.AsReal.complex r, by simpa [Litex.Lt, Litex.OrderValue] using h⟩

theorem absEqSelfOfLe (r : ℝ) (h : Litex.Le (0 : ℂ) (r : ℂ)) :
    Litex.Same (Litex.abs (r : ℂ)) (r : ℂ) := by
  apply Litex.Same.ofEq
  have hr : 0 ≤ r := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.abs, abs_of_nonneg hr]

theorem absEqNegOfLe (r : ℝ) (h : Litex.Le (r : ℂ) (0 : ℂ)) :
    Litex.Same (Litex.abs (r : ℂ)) ((-1 : ℂ) * (r : ℂ)) := by
  apply Litex.Same.ofEq
  have hr : r ≤ 0 := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.abs, abs_of_nonpos hr]

theorem absPositiveOfNotSame
    {alpha : Type}
    (source : alpha)
    (r : ℝ)
    (sourceToReal : Litex.Same source (r : ℂ))
    (nonzero : ¬ Litex.Same source (0 : ℂ)) :
    Litex.Positive (Litex.abs (r : ℂ)) := by
  have hr : r ≠ 0 := by
    intro equality
    apply nonzero
    exact Litex.Same.trans sourceToReal (Litex.Same.ofEq (by simp [equality]))
  exact ⟨|r|, by simpa [Litex.abs] using Litex.AsReal.complex |r|, abs_pos.mpr hr⟩

theorem absAddLe (a b : ℂ) :
    Litex.Le (Litex.abs (a + b)) (Litex.abs a + Litex.abs b) := by
  simpa [Litex.Le, Litex.OrderValue, Litex.abs] using norm_add_le a b

theorem absSubLeSum (a b : ℂ) :
    Litex.Le (Litex.abs (a - b)) (Litex.abs a + Litex.abs b) := by
  simpa [Litex.Le, Litex.OrderValue, Litex.abs] using norm_sub_le a b

theorem absSubAbsLeAbsAdd (a b : ℂ) :
    Litex.Le (Litex.abs a - Litex.abs b) (Litex.abs (a + b)) := by
  simp only [Litex.Le, Litex.OrderValue, Litex.abs, Complex.sub_re,
    Complex.ofReal_re]
  have h := norm_sub_le (a + b) b
  rw [add_sub_cancel_right] at h
  linarith

theorem absSubAbsLeAbsSub (a b : ℂ) :
    Litex.Le (Litex.abs a - Litex.abs b) (Litex.abs (a - b)) := by
  simp only [Litex.Le, Litex.OrderValue, Litex.abs, Complex.sub_re,
    Complex.ofReal_re]
  have h := norm_add_le (a - b) b
  rw [sub_add_cancel] at h
  linarith

theorem negAbsLe (z : ℂ) : Litex.Le ((-1 : ℂ) * Litex.abs z) z := by
  simpa [Litex.Le, Litex.OrderValue, Litex.abs] using
    (le_trans (neg_le_neg (Complex.abs_re_le_norm z)) (neg_abs_le z.re))

theorem negLeAbs (z : ℂ) : Litex.Le ((-1 : ℂ) * z) (Litex.abs z) := by
  simpa [Litex.Le, Litex.OrderValue, Litex.abs] using
    (le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z))

theorem selfLeAbs (z : ℂ) : Litex.Le z (Litex.abs z) := by
  simp only [Litex.Le, Litex.OrderValue, Litex.abs, Complex.ofReal_re]
  exact le_trans (le_abs_self z.re) (Complex.abs_re_le_norm z)

theorem minEqLeftOfLe (a b : ℝ) (h : Litex.Le (a : ℂ) (b : ℂ)) :
    Litex.Same (Litex.min (a : ℂ) (b : ℂ)) (a : ℂ) := by
  apply Litex.Same.ofEq
  have hab : a ≤ b := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.min, Litex.OrderValue, hab]

theorem minEqRightOfLe (a b : ℝ) (h : Litex.Le (b : ℂ) (a : ℂ)) :
    Litex.Same (Litex.min (a : ℂ) (b : ℂ)) (b : ℂ) := by
  apply Litex.Same.ofEq
  have hba : b ≤ a := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.min, Litex.OrderValue, hba]

theorem maxEqLeftOfLe (a b : ℝ) (h : Litex.Le (b : ℂ) (a : ℂ)) :
    Litex.Same (Litex.max (a : ℂ) (b : ℂ)) (a : ℂ) := by
  apply Litex.Same.ofEq
  have hba : b ≤ a := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.max, Litex.OrderValue, hba]

theorem maxEqRightOfLe (a b : ℝ) (h : Litex.Le (a : ℂ) (b : ℂ)) :
    Litex.Same (Litex.max (a : ℂ) (b : ℂ)) (b : ℂ) := by
  apply Litex.Same.ofEq
  have hab : a ≤ b := by simpa [Litex.Le, Litex.OrderValue] using h
  simp [Litex.max, Litex.OrderValue, hab]

theorem minLeLeft (a b : ℝ) : Litex.Le (Litex.min (a : ℂ) (b : ℂ)) (a : ℂ) := by
  simp [Litex.min, Litex.Le, Litex.OrderValue]

theorem minLeRight (a b : ℝ) : Litex.Le (Litex.min (a : ℂ) (b : ℂ)) (b : ℂ) := by
  simp [Litex.min, Litex.Le, Litex.OrderValue]

theorem leMaxLeft (a b : ℝ) : Litex.Le (a : ℂ) (Litex.max (a : ℂ) (b : ℂ)) := by
  simp [Litex.max, Litex.Le, Litex.OrderValue]

theorem leMaxRight (a b : ℝ) : Litex.Le (b : ℂ) (Litex.max (a : ℂ) (b : ℂ)) := by
  simp [Litex.max, Litex.Le, Litex.OrderValue]

theorem minMonotone (a b c d : ℝ)
    (hac : Litex.Le (a : ℂ) (c : ℂ))
    (hbd : Litex.Le (b : ℂ) (d : ℂ)) :
    Litex.Le (Litex.min (a : ℂ) (b : ℂ)) (Litex.min (c : ℂ) (d : ℂ)) := by
  have hac' : a ≤ c := by simpa [Litex.Le, Litex.OrderValue] using hac
  have hbd' : b ≤ d := by simpa [Litex.Le, Litex.OrderValue] using hbd
  simpa [Litex.min, Litex.Le, Litex.OrderValue] using min_le_min hac' hbd'

theorem maxMonotone (a b c d : ℝ)
    (hac : Litex.Le (a : ℂ) (c : ℂ))
    (hbd : Litex.Le (b : ℂ) (d : ℂ)) :
    Litex.Le (Litex.max (a : ℂ) (b : ℂ)) (Litex.max (c : ℂ) (d : ℂ)) := by
  have hac' : a ≤ c := by simpa [Litex.Le, Litex.OrderValue] using hac
  have hbd' : b ≤ d := by simpa [Litex.Le, Litex.OrderValue] using hbd
  simpa [Litex.max, Litex.Le, Litex.OrderValue] using max_le_max hac' hbd'

theorem minCommutative (a b : ℝ) :
    Litex.Same (Litex.min (a : ℂ) (b : ℂ)) (Litex.min (b : ℂ) (a : ℂ)) := by
  apply Litex.Same.ofEq
  simp [Litex.min, Litex.OrderValue, min_comm]

theorem maxCommutative (a b : ℝ) :
    Litex.Same (Litex.max (a : ℂ) (b : ℂ)) (Litex.max (b : ℂ) (a : ℂ)) := by
  apply Litex.Same.ofEq
  simp [Litex.max, Litex.OrderValue, max_comm]

theorem minAssociative (a b c : ℝ) :
    Litex.Same
      (Litex.min (Litex.min (a : ℂ) (b : ℂ)) (c : ℂ))
      (Litex.min (a : ℂ) (Litex.min (b : ℂ) (c : ℂ))) := by
  apply Litex.Same.ofEq
  simp [Litex.min, Litex.OrderValue, min_assoc]

theorem maxAssociative (a b c : ℝ) :
    Litex.Same
      (Litex.max (Litex.max (a : ℂ) (b : ℂ)) (c : ℂ))
      (Litex.max (a : ℂ) (Litex.max (b : ℂ) (c : ℂ))) := by
  apply Litex.Same.ofEq
  simp [Litex.max, Litex.OrderValue, max_assoc]

theorem minIdempotent (a : ℝ) :
    Litex.Same (Litex.min (a : ℂ) (a : ℂ)) (a : ℂ) := by
  apply Litex.Same.ofEq
  simp [Litex.min, Litex.OrderValue]

theorem maxIdempotent (a : ℝ) :
    Litex.Same (Litex.max (a : ℂ) (a : ℂ)) (a : ℂ) := by
  apply Litex.Same.ofEq
  simp [Litex.max, Litex.OrderValue]

theorem minAbsorbMaxLeft (a b : ℝ) :
    Litex.Same (Litex.min (a : ℂ) (Litex.max (a : ℂ) (b : ℂ))) (a : ℂ) := by
  apply Litex.Same.ofEq
  by_cases hab : a ≤ b
  · simp [Litex.min, Litex.max, Litex.OrderValue, hab]
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    simp [Litex.min, Litex.max, Litex.OrderValue, hba]

theorem maxAbsorbMinLeft (a b : ℝ) :
    Litex.Same (Litex.max (a : ℂ) (Litex.min (a : ℂ) (b : ℂ))) (a : ℂ) := by
  apply Litex.Same.ofEq
  by_cases hab : a ≤ b
  · simp [Litex.min, Litex.max, Litex.OrderValue, hab]
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    simp [Litex.min, Litex.max, Litex.OrderValue, hba]

/-- The empty typed tuple spine belongs to the empty Cartesian tail. -/
theorem inCartNil : Litex.In (Litex.HNil.nil : Litex.HNil.{u}) Litex.cartNil :=
  Litex.In.own Litex.cartNil Litex.HNil.nil

/-- Coordinate membership composes without erasing either carrier. -/
theorem inCartCons
    {α tailValue : Type u}
    {headSet tailSet : Litex.Set.{u}}
    {head : α}
    {tail : tailValue}
    (headMembership : Litex.In head headSet)
    (tailMembership : Litex.In tail tailSet) :
    Litex.In (Litex.HCons.mk head tail) (Litex.cartCons headSet tailSet) :=
  ⟨ Litex.HCons.mk
      (Litex.In.rep head headMembership)
      (Litex.In.rep tail tailMembership),
    Litex.Same.hcons
      (Litex.In.same_rep head headMembership)
      (Litex.In.same_rep tail tailMembership) ⟩

theorem complexNatInN (n : ℕ) : Litex.In (n : ℂ) Litex.N :=
  ⟨n, Litex.Same.complexNat n⟩

theorem complexIntInZ (z : ℤ) : Litex.In (z : ℂ) Litex.Z :=
  ⟨z, Litex.Same.complexInt z⟩

theorem complexRatInQ (q : ℚ) : Litex.In (q : ℂ) Litex.Q :=
  ⟨q, Litex.Same.complexRat q⟩

theorem complexRealInR (r : ℝ) : Litex.In (r : ℂ) Litex.R :=
  ⟨r, Litex.Same.complexReal r⟩

theorem imaginaryUnitInC : Litex.In Complex.I Litex.C :=
  complexInC Complex.I

theorem eInR : Litex.In ((Real.exp 1 : ℝ) : ℂ) Litex.R :=
  complexRealInR (Real.exp 1)

theorem piInR : Litex.In ((Real.pi : ℝ) : ℂ) Litex.R :=
  complexRealInR Real.pi

/-- Standard hierarchy projection from natural to integer membership. -/
theorem inZOfInN
    {alpha : Type}
    {x : alpha}
    (hx : Litex.In x Litex.N) :
    Litex.In x Litex.Z := by
  rcases hx with ⟨n, hxn⟩
  exact ⟨(n : ℤ), Litex.Same.trans hxn
    (Litex.Same.trans (Litex.Same.natComplex n)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (n : ℂ) = ((n : ℤ) : ℂ)))
        (Litex.Same.complexInt (n : ℤ))))⟩

/-- Standard hierarchy projection from integer to rational membership. -/
theorem inQOfInZ
    {alpha : Type}
    {x : alpha}
    (hx : Litex.In x Litex.Z) :
    Litex.In x Litex.Q := by
  rcases hx with ⟨z, hxz⟩
  exact ⟨(z : ℚ), Litex.Same.trans hxz
    (Litex.Same.trans (Litex.Same.intComplex z)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (z : ℂ) = ((z : ℚ) : ℂ)))
        (Litex.Same.complexRat (z : ℚ))))⟩

/-- Standard hierarchy projection from rational to real membership. -/
theorem inROfInQ
    {alpha : Type}
    {x : alpha}
    (hx : Litex.In x Litex.Q) :
    Litex.In x Litex.R := by
  rcases hx with ⟨q, hxq⟩
  exact ⟨(q : ℝ), Litex.Same.trans hxq
    (Litex.Same.trans (Litex.Same.ratComplex q)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (q : ℂ) = ((q : ℝ) : ℂ)))
        (Litex.Same.complexReal (q : ℝ))))⟩

/-- Standard hierarchy projection from real to complex membership. -/
theorem inCOfInR
    {alpha : Type}
    {x : alpha}
    (hx : Litex.In x Litex.R) :
    Litex.In x Litex.C := by
  rcases hx with ⟨r, hxr⟩
  exact ⟨(r : ℂ), Litex.Same.trans hxr (Litex.Same.realComplex r)⟩

theorem naturalNonempty : Litex.Set.Nonempty Litex.N :=
  ⟨0⟩

theorem integerNonempty : Litex.Set.Nonempty Litex.Z :=
  ⟨0⟩

theorem rationalNonempty : Litex.Set.Nonempty Litex.Q :=
  ⟨0⟩

theorem realNonempty : Litex.Set.Nonempty Litex.R :=
  ⟨0⟩

theorem complexNonempty : Litex.Set.Nonempty Litex.C :=
  ⟨0⟩

/-- A complex value proved equal to a natural cast belongs to `N`. -/
theorem complexEqNatInN
    (z : ℂ)
    (n : ℕ)
    (h : z = (n : ℂ)) :
    Litex.In z Litex.N :=
  ⟨n, Litex.Same.trans (Litex.Same.ofEq h) (Litex.Same.complexNat n)⟩

/-- Natural membership carries the exact nonnegativity inference used by Litex. -/
theorem nonnegativeOfInN
    {alpha : Type}
    {x : alpha}
    (hx : Litex.In x Litex.N) :
    Litex.Nonnegative x := by
  rcases hx with ⟨n, hxn⟩
  exact ⟨(n : ℝ), Litex.Same.trans hxn (Litex.AsReal.nat n), Nat.cast_nonneg n⟩

/-- The exact natural representative selected by the same membership
certificate is nonnegative in the native complex order ABI. -/
theorem naturalRepNonnegative
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.N) :
    Litex.Le (0 : ℂ) (((Litex.In.rep x h : ℕ) : ℂ)) := by
  simp [Litex.Le, Litex.OrderValue]

/-- A complex value proved equal to an integer cast belongs to `Z`. -/
theorem complexEqIntInZ
    (z : ℂ)
    (n : ℤ)
    (h : z = (n : ℂ)) :
    Litex.In z Litex.Z :=
  ⟨n, Litex.Same.trans (Litex.Same.ofEq h) (Litex.Same.complexInt n)⟩

/-- A complex value proved equal to a rational cast belongs to `Q`. -/
theorem complexEqRatInQ
    (z : ℂ)
    (q : ℚ)
    (h : z = (q : ℂ)) :
    Litex.In z Litex.Q :=
  ⟨q, Litex.Same.trans (Litex.Same.ofEq h) (Litex.Same.complexRat q)⟩

/-- Negated Litex semantic equality is symmetric because `Same` itself is
symmetric. Example: `a != b` proves `b != a`. -/
theorem notSameSymm
    {alpha beta : Litex.u.{u}}
    {a : alpha}
    {b : beta}
    (h : ¬ Litex.Same a b) :
    ¬ Litex.Same b a := by
  intro hba
  exact h (Litex.Same.symm hba)

private theorem complexAddAsReal
    {a b : ℂ}
    {r s : ℝ}
    (ha : Litex.AsReal a r)
    (hb : Litex.AsReal b s) :
    Litex.AsReal (a + b) (r + s) :=
  Litex.Same.symm
    (Litex.Same.realAddComplex (Litex.Same.symm ha) (Litex.Same.symm hb))

private theorem complexSubAsReal
    {a b : ℂ}
    {r s : ℝ}
    (ha : Litex.AsReal a r)
    (hb : Litex.AsReal b s) :
    Litex.AsReal (a - b) (r - s) :=
  Litex.Same.symm
    (Litex.Same.realSubComplex (Litex.Same.symm ha) (Litex.Same.symm hb))

private theorem complexMulAsReal
    {a b : ℂ}
    {r s : ℝ}
    (ha : Litex.AsReal a r)
    (hb : Litex.AsReal b s) :
    Litex.AsReal (a * b) (r * s) :=
  Litex.Same.symm
    (Litex.Same.realMulComplex (Litex.Same.symm ha) (Litex.Same.symm hb))

private theorem complexDivAsReal
    {a b : ℂ}
    {r s : ℝ}
    (ha : Litex.AsReal a r)
    (hb : Litex.AsReal b s) :
    Litex.AsReal (a / b) (r / s) :=
  Litex.Same.symm
    (Litex.Same.realDivComplex (Litex.Same.symm ha) (Litex.Same.symm hb))

private theorem complexIntAsReal
    {a : ℂ}
    {z : ℤ}
    (haz : Litex.Same a z) :
    Litex.AsReal a (z : ℝ) :=
  Litex.Same.trans haz
    (Litex.Same.trans (Litex.Same.intComplex z)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (z : ℂ) = ((z : ℝ) : ℂ)))
        (Litex.Same.complexReal (z : ℝ))))

private theorem realSameInt (z : ℤ) : Litex.Same (z : ℝ) z :=
  Litex.Same.trans (Litex.Same.realComplex (z : ℝ))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : ((z : ℝ) : ℂ) = (z : ℂ)))
      (Litex.Same.complexInt z))

private theorem complexNatAsReal
    {a : ℂ}
    {n : ℕ}
    (han : Litex.Same a n) :
    Litex.AsReal a (n : ℝ) :=
  Litex.Same.trans han
    (Litex.Same.trans (Litex.Same.natComplex n)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (n : ℂ) = ((n : ℝ) : ℂ)))
        (Litex.Same.complexReal (n : ℝ))))

private theorem realSameNat (n : ℕ) : Litex.Same (n : ℝ) n :=
  Litex.Same.trans (Litex.Same.realComplex (n : ℝ))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : ((n : ℝ) : ℂ) = (n : ℂ)))
      (Litex.Same.complexNat n))

private theorem complexRatAsReal
    {a : ℂ}
    {q : ℚ}
    (haq : Litex.Same a q) :
    Litex.AsReal a (q : ℝ) :=
  Litex.Same.trans haq
    (Litex.Same.trans (Litex.Same.ratComplex q)
      (Litex.Same.trans
        (Litex.Same.ofEq (by norm_num : (q : ℂ) = ((q : ℝ) : ℂ)))
        (Litex.Same.complexReal (q : ℝ))))

private theorem realSameRat (q : ℚ) : Litex.Same (q : ℝ) q :=
  Litex.Same.trans (Litex.Same.realComplex (q : ℝ))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : ((q : ℝ) : ℂ) = (q : ℂ)))
      (Litex.Same.complexRat q))

/-- Addition preserves real membership for complex-carrier source values. -/
theorem complexAddInR
    {a b : ℂ}
    (ha : Litex.In a Litex.R)
    (hb : Litex.In b Litex.R) :
    Litex.In (a + b) Litex.R := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb⟩

/-- Subtraction preserves real membership for complex-carrier source values. -/
theorem complexSubInR
    {a b : ℂ}
    (ha : Litex.In a Litex.R)
    (hb : Litex.In b Litex.R) :
    Litex.In (a - b) Litex.R := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  exact ⟨ra - rb, complexSubAsReal hra hrb⟩

/-- Multiplication preserves real membership for complex-carrier source values. -/
theorem complexMulInR
    {a b : ℂ}
    (ha : Litex.In a Litex.R)
    (hb : Litex.In b Litex.R) :
    Litex.In (a * b) Litex.R := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  exact ⟨ra * rb, complexMulAsReal hra hrb⟩

/-- Division preserves real membership for complex-carrier source values.
The source verifier retains denominator well-definedness separately. -/
theorem complexDivInR
    {a b : ℂ}
    (ha : Litex.In a Litex.R)
    (hb : Litex.In b Litex.R) :
    Litex.In (a / b) Litex.R := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  exact ⟨ra / rb, complexDivAsReal hra hrb⟩

/-- Addition preserves integer membership for complex-carrier source values. -/
theorem complexAddInZ
    {a b : ℂ}
    (ha : Litex.In a Litex.Z)
    (hb : Litex.In b Litex.Z) :
    Litex.In (a + b) Litex.Z := by
  rcases ha with ⟨za, hza⟩
  rcases hb with ⟨zb, hzb⟩
  exact ⟨za + zb, Litex.Same.trans
    (complexAddAsReal (complexIntAsReal hza) (complexIntAsReal hzb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (za : ℝ) + (zb : ℝ) = ((za + zb : ℤ) : ℝ)))
      (realSameInt (za + zb)))⟩

/-- Subtraction preserves integer membership for complex-carrier source values. -/
theorem complexSubInZ
    {a b : ℂ}
    (ha : Litex.In a Litex.Z)
    (hb : Litex.In b Litex.Z) :
    Litex.In (a - b) Litex.Z := by
  rcases ha with ⟨za, hza⟩
  rcases hb with ⟨zb, hzb⟩
  exact ⟨za - zb, Litex.Same.trans
    (complexSubAsReal (complexIntAsReal hza) (complexIntAsReal hzb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (za : ℝ) - (zb : ℝ) = ((za - zb : ℤ) : ℝ)))
      (realSameInt (za - zb)))⟩

/-- Multiplication preserves integer membership for complex-carrier source values. -/
theorem complexMulInZ
    {a b : ℂ}
    (ha : Litex.In a Litex.Z)
    (hb : Litex.In b Litex.Z) :
    Litex.In (a * b) Litex.Z := by
  rcases ha with ⟨za, hza⟩
  rcases hb with ⟨zb, hzb⟩
  exact ⟨za * zb, Litex.Same.trans
    (complexMulAsReal (complexIntAsReal hza) (complexIntAsReal hzb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (za : ℝ) * (zb : ℝ) = ((za * zb : ℤ) : ℝ)))
      (realSameInt (za * zb)))⟩

/-- A rational observation of an integer base raised to a natural exponent
still has an exact integer representative. This matches the compiler's
canonical rendering of source powers with a checked `Z` base. -/
theorem complexIntPowNatInZ
    (base : ℤ)
    (exponent : ℕ) :
    Litex.In ((((base : ℚ) ^ (exponent : ℤ) : ℚ) : ℂ)) Litex.Z := by
  have power_cast :
      ((((base : ℚ) ^ (exponent : ℤ) : ℚ) : ℂ)) =
        (((base ^ exponent : ℤ) : ℂ)) := by
    norm_cast
  exact ⟨base ^ exponent,
    Litex.Same.trans (Litex.Same.ofEq power_cast)
      (Litex.Same.complexInt (base ^ exponent))⟩

private theorem integerRangeSumSingleNative
    (start : ℤ)
    (function : Litex.Fn Litex.Z Litex.Z) :
    Litex.sum start start function =
      function.callOwn start := by
  simp [Litex.sum, Litex.integerRangeSum]

/-- Pointwise non-strict order on an inclusive integer interval lifts to the
corresponding exact-carrier sums. This is the reviewed target of the typed
`IntegerRangeSumPointwiseOrder` Result; the Result compiler supplies the
binder-owning pointwise theorem rather than reconstructing it from the sum. -/
theorem integerRangeSumLeOwn
    (start finish : ℤ)
    (left right : Litex.Fn Litex.Z Litex.Z)
    (pointwise : ∀ index : ℤ,
      Litex.Le (start : ℂ) (index : ℂ) →
      Litex.Le (index : ℂ) (finish : ℂ) →
      Litex.Le (left.callOwn index : ℂ) (right.callOwn index : ℂ)) :
    Litex.Le ((Litex.sum start finish left : ℤ) : ℂ)
      ((Litex.sum start finish right : ℤ) : ℂ) := by
  have native : Litex.sum start finish left ≤ Litex.sum start finish right := by
    simp only [Litex.sum, Litex.integerRangeSum]
    apply Finset.sum_le_sum
    intro index indexInRange
    have lower : start ≤ index := (Finset.mem_Icc.mp indexInRange).1
    have upper : index ≤ finish := (Finset.mem_Icc.mp indexInRange).2
    have checked := pointwise index
      (by simpa [Litex.Le, Litex.OrderValue] using lower)
      (by simpa [Litex.Le, Litex.OrderValue] using upper)
    have checkedReal : (left.callOwn index : ℝ) ≤ (right.callOwn index : ℝ) := by
      simpa [Litex.Le, Litex.OrderValue] using checked
    exact_mod_cast checkedReal
  simpa [Litex.Le, Litex.OrderValue] using native

/-- Registered `aggregate.sum_single` adapter for an exact function carrier. -/
theorem integerRangeSumSingleOwn
    (start : ℤ)
    (function : Litex.Fn Litex.Z Litex.Z) :
    Litex.Same (Litex.sum start start function)
      (Litex.fnApplyCarrier function
        (Litex.In.own (Litex.fnSet Litex.Z Litex.Z) function)
        start) := by
  apply Litex.Same.ofEq
  simpa [Litex.fnApplyCarrier] using
    integerRangeSumSingleNative start function

/-- Registered `aggregate.sum_single` adapter for a heterogeneous function
parameter with its exact `fnSet Z Z` membership certificate. -/
theorem integerRangeSumSingle
    {alpha : Type 1}
    (start : ℤ)
    (function : alpha)
    (functionMembership : Litex.In function (Litex.fnSet Litex.Z Litex.Z)) :
    Litex.Same
      (Litex.sum start start (Litex.In.rep function functionMembership))
      (Litex.fnApplySelectedCarrier function functionMembership start) := by
  apply Litex.Same.ofEq
  simpa [Litex.fnApplySelectedCarrier] using
    integerRangeSumSingleNative start (Litex.In.rep function functionMembership)

private theorem integerRangeSumSplitLastNative
    (start finish : ℤ)
    (function : Litex.Fn Litex.Z Litex.Z)
    (startLeFinish : start ≤ finish) :
    Litex.sum start (finish + 1) function =
      Litex.sum start finish function +
        function.callOwn (finish + 1) := by
  have endpointNotInPrevious : finish + 1 ∉ Finset.Icc start finish := by
    simp
  have intervalInsert :
      insert (finish + 1) (Finset.Icc start finish) =
        Finset.Icc start (finish + 1) := by
    simpa using
      (Finset.insert_Icc_sub_one_right_eq_Icc
        (a := start) (b := finish + 1) (by omega : start ≤ finish + 1))
  simp only [Litex.sum, Litex.integerRangeSum]
  rw [← intervalInsert, Finset.sum_insert endpointNotInPrevious]
  simp [add_comm]

/-- Registered `aggregate.sum_split_last` adapter for an exact function carrier. -/
theorem integerRangeSumSplitLastOwn
    (start finish : ℤ)
    (function : Litex.Fn Litex.Z Litex.Z)
    (startLeFinish : Litex.Le (start : ℂ) (finish : ℂ)) :
    Litex.Same (Litex.sum start (finish + 1) function)
      (((Litex.sum start finish function : ℤ) : ℂ) +
        ((Litex.fnApplyCarrier function
            (Litex.In.own (Litex.fnSet Litex.Z Litex.Z) function)
            (finish + 1) : ℤ) : ℂ)) := by
  have hnative := integerRangeSumSplitLastNative start finish function
    (by simpa [Litex.Le, Litex.OrderValue] using startLeFinish)
  exact Litex.Same.trans (Litex.Same.ofEq hnative)
    (Litex.Same.intAddComplex
      (Litex.Same.intComplex (Litex.sum start finish function))
      (Litex.Same.intComplex
        (Litex.fnApplyCarrier function
          (Litex.In.own (Litex.fnSet Litex.Z Litex.Z) function)
          (finish + 1))))

/-- Registered `aggregate.sum_split_last` adapter for a heterogeneous
function parameter. -/
theorem integerRangeSumSplitLast
    {alpha : Type 1}
    (start finish : ℤ)
    (function : alpha)
    (functionMembership : Litex.In function (Litex.fnSet Litex.Z Litex.Z))
    (startLeFinish : Litex.Le (start : ℂ) (finish : ℂ)) :
    Litex.Same
      (Litex.sum start (finish + 1) (Litex.In.rep function functionMembership))
      (((Litex.sum start finish (Litex.In.rep function functionMembership) : ℤ) : ℂ) +
        ((Litex.fnApplySelectedCarrier function functionMembership (finish + 1) : ℤ) : ℂ)) := by
  have hnative :
      Litex.sum start (finish + 1) (Litex.In.rep function functionMembership) =
        Litex.sum start finish (Litex.In.rep function functionMembership) +
          Litex.fnApplySelectedCarrier function functionMembership (finish + 1) := by
    simpa [Litex.fnApplySelectedCarrier] using
      integerRangeSumSplitLastNative start finish
        (Litex.In.rep function functionMembership)
        (by simpa [Litex.Le, Litex.OrderValue] using startLeFinish)
  exact Litex.Same.trans (Litex.Same.ofEq hnative)
    (Litex.Same.intAddComplex
      (Litex.Same.intComplex
        (Litex.sum start finish (Litex.In.rep function functionMembership)))
      (Litex.Same.intComplex
        (Litex.fnApplySelectedCarrier function functionMembership (finish + 1))))

/-- Addition preserves natural membership for complex-carrier source values. -/
theorem complexAddInN
    {a b : ℂ}
    (ha : Litex.In a Litex.N)
    (hb : Litex.In b Litex.N) :
    Litex.In (a + b) Litex.N := by
  rcases ha with ⟨na, hna⟩
  rcases hb with ⟨nb, hnb⟩
  exact ⟨na + nb, Litex.Same.trans
    (complexAddAsReal (complexNatAsReal hna) (complexNatAsReal hnb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (na : ℝ) + (nb : ℝ) = ((na + nb : ℕ) : ℝ)))
      (realSameNat (na + nb)))⟩

/-- Multiplication preserves natural membership for complex-carrier source values. -/
theorem complexMulInN
    {a b : ℂ}
    (ha : Litex.In a Litex.N)
    (hb : Litex.In b Litex.N) :
    Litex.In (a * b) Litex.N := by
  rcases ha with ⟨na, hna⟩
  rcases hb with ⟨nb, hnb⟩
  exact ⟨na * nb, Litex.Same.trans
    (complexMulAsReal (complexNatAsReal hna) (complexNatAsReal hnb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (na : ℝ) * (nb : ℝ) = ((na * nb : ℕ) : ℝ)))
      (realSameNat (na * nb)))⟩

/-- Addition preserves rational membership for complex-carrier source values. -/
theorem complexAddInQ
    {a b : ℂ}
    (ha : Litex.In a Litex.Q)
    (hb : Litex.In b Litex.Q) :
    Litex.In (a + b) Litex.Q := by
  rcases ha with ⟨qa, hqa⟩
  rcases hb with ⟨qb, hqb⟩
  exact ⟨qa + qb, Litex.Same.trans
    (complexAddAsReal (complexRatAsReal hqa) (complexRatAsReal hqb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (qa : ℝ) + (qb : ℝ) = ((qa + qb : ℚ) : ℝ)))
      (realSameRat (qa + qb)))⟩

/-- Subtraction preserves rational membership for complex-carrier source values. -/
theorem complexSubInQ
    {a b : ℂ}
    (ha : Litex.In a Litex.Q)
    (hb : Litex.In b Litex.Q) :
    Litex.In (a - b) Litex.Q := by
  rcases ha with ⟨qa, hqa⟩
  rcases hb with ⟨qb, hqb⟩
  exact ⟨qa - qb, Litex.Same.trans
    (complexSubAsReal (complexRatAsReal hqa) (complexRatAsReal hqb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (qa : ℝ) - (qb : ℝ) = ((qa - qb : ℚ) : ℝ)))
      (realSameRat (qa - qb)))⟩

/-- Multiplication preserves rational membership for complex-carrier source values. -/
theorem complexMulInQ
    {a b : ℂ}
    (ha : Litex.In a Litex.Q)
    (hb : Litex.In b Litex.Q) :
    Litex.In (a * b) Litex.Q := by
  rcases ha with ⟨qa, hqa⟩
  rcases hb with ⟨qb, hqb⟩
  exact ⟨qa * qb, Litex.Same.trans
    (complexMulAsReal (complexRatAsReal hqa) (complexRatAsReal hqb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (qa : ℝ) * (qb : ℝ) = ((qa * qb : ℚ) : ℝ)))
      (realSameRat (qa * qb)))⟩

/-- Division preserves rational membership for complex-carrier source values.
The source verifier retains denominator well-definedness separately. -/
theorem complexDivInQ
    {a b : ℂ}
    (ha : Litex.In a Litex.Q)
    (hb : Litex.In b Litex.Q) :
    Litex.In (a / b) Litex.Q := by
  rcases ha with ⟨qa, hqa⟩
  rcases hb with ⟨qb, hqb⟩
  exact ⟨qa / qb, Litex.Same.trans
    (complexDivAsReal (complexRatAsReal hqa) (complexRatAsReal hqb))
    (Litex.Same.trans
      (Litex.Same.ofEq (by norm_cast : (qa : ℝ) / (qb : ℝ) = ((qa / qb : ℚ) : ℝ)))
      (realSameRat (qa / qb)))⟩

/-- The complex-carrier adapter for nonnegative addition. Zero-ended order
uses Mathlib's canonical real zero, so only the operand representatives are
opened. -/
theorem complexAddNonnegative
    {a b : ℂ}
    (ha : Litex.Nonnegative a)
    (hb : Litex.Nonnegative b) :
    Litex.Nonnegative (a + b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb, add_nonneg haOrder hbOrder⟩

/-- Strict positivity is closed under addition. -/
theorem complexAddPositive
    {a b : ℂ}
    (ha : Litex.Positive a)
    (hb : Litex.Positive b) :
    Litex.Positive (a + b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb, add_pos haOrder hbOrder⟩

/-- The concrete complex-carrier adapter for Litex's strict-left,
nonnegative-right addition builtin rule. -/
theorem complexAddPositiveLeftStrict
    {a b : ℂ}
    (ha : Litex.Positive a)
    (hb : Litex.Nonnegative b) :
    Litex.Positive (a + b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb,
    add_pos_of_pos_of_nonneg haOrder hbOrder⟩

/-- The concrete complex-carrier adapter for Litex's nonnegative-left,
strict-right addition builtin rule. -/
theorem complexAddPositiveRightStrict
    {a b : ℂ}
    (ha : Litex.Nonnegative a)
    (hb : Litex.Positive b) :
    Litex.Positive (a + b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb,
    add_pos_of_nonneg_of_pos haOrder hbOrder⟩

/-- Nonnegative real representatives are closed under multiplication. -/
theorem complexMulNonnegative
    {a b : ℂ}
    (ha : Litex.Nonnegative a)
    (hb : Litex.Nonnegative b) :
    Litex.Nonnegative (a * b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra * rb, complexMulAsReal hra hrb, mul_nonneg haOrder hbOrder⟩

/-- Multiplication by negative one reverses a nonnegative source value into
the exact nonpositive expression retained by Litex inference. -/
theorem complexNegativeOneMulNonpositive
    {a : ℂ}
    (ha : Litex.Nonnegative a) :
    Litex.Nonpositive ((-1 : ℂ) * a) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  have minusOneAsReal : Litex.AsReal (-1 : ℂ) (-1 : ℝ) :=
    Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : (-1 : ℂ) = ((-1 : ℝ) : ℂ)))
      (Litex.AsReal.complex (-1 : ℝ))
  exact ⟨-1 * ra, complexMulAsReal minusOneAsReal hra, by linarith⟩

/-- Multiplication by negative one reverses a positive source value into the
exact strict negative expression retained by Litex inference. -/
theorem complexNegativeOneMulNegative
    {a : ℂ}
    (ha : Litex.Positive a) :
    Litex.Negative ((-1 : ℂ) * a) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  have minusOneAsReal : Litex.AsReal (-1 : ℂ) (-1 : ℝ) :=
    Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : (-1 : ℂ) = ((-1 : ℝ) : ℂ)))
      (Litex.AsReal.complex (-1 : ℝ))
  exact ⟨-1 * ra, complexMulAsReal minusOneAsReal hra, by linarith⟩

/-- Multiplication by negative one reverses a nonpositive source value into
the exact nonnegative expression retained by Litex inference. -/
theorem complexNegativeOneMulNonnegative
    {a : ℂ}
    (ha : Litex.Nonpositive a) :
    Litex.Nonnegative ((-1 : ℂ) * a) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  have minusOneAsReal : Litex.AsReal (-1 : ℂ) (-1 : ℝ) :=
    Litex.Same.trans
      (Litex.Same.ofEq (by norm_num : (-1 : ℂ) = ((-1 : ℝ) : ℂ)))
      (Litex.AsReal.complex (-1 : ℝ))
  exact ⟨-1 * ra, complexMulAsReal minusOneAsReal hra, by linarith⟩

/-- Positive real representatives are closed under multiplication. -/
theorem complexMulPositive
    {a b : ℂ}
    (ha : Litex.Positive a)
    (hb : Litex.Positive b) :
    Litex.Positive (a * b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra * rb, complexMulAsReal hra hrb, mul_pos haOrder hbOrder⟩

/-- A nonnegative numerator divided by a positive denominator is
nonnegative. -/
theorem complexDivNonnegative
    {a b : ℂ}
    (ha : Litex.Nonnegative a)
    (hb : Litex.Positive b) :
    Litex.Nonnegative (a / b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra / rb, complexDivAsReal hra hrb,
    div_nonneg haOrder (le_of_lt hbOrder)⟩

/-- A positive numerator divided by a positive denominator is positive. -/
theorem complexDivPositive
    {a b : ℂ}
    (ha : Litex.Positive a)
    (hb : Litex.Positive b) :
    Litex.Positive (a / b) := by
  rcases ha with ⟨ra, hra, haOrder⟩
  rcases hb with ⟨rb, hrb, hbOrder⟩
  exact ⟨ra / rb, complexDivAsReal hra hrb, div_pos haOrder hbOrder⟩

/-- Subtracting a smaller real observation from a larger one produces the
exact nonnegative complex-carrier expression retained by registered rule
`order.sub_nonnegative_of_less_equal`. -/
theorem complexSubNonnegativeOfLessEqual
    {u v : ℝ}
    (hvu : Litex.Le (v : ℂ) (u : ℂ)) :
    Litex.Nonnegative ((u : ℂ) - (v : ℂ)) := by
  exact ⟨u - v, complexSubAsReal (Litex.AsReal.complex u) (Litex.AsReal.complex v), by
    simpa [Litex.Le, Litex.OrderValue] using hvu⟩

/-- Strict subtraction counterpart for registered rule
`order.sub_positive_of_less`. -/
theorem complexSubPositiveOfLess
    {u v : ℝ}
    (hvu : Litex.Lt (v : ℂ) (u : ℂ)) :
    Litex.Positive ((u : ℂ) - (v : ℂ)) := by
  exact ⟨u - v, complexSubAsReal (Litex.AsReal.complex u) (Litex.AsReal.complex v), by
    simpa [Litex.Lt, Litex.OrderValue] using hvu⟩

/-- Adding one common complex term preserves Litex non-strict order.
This is the Lean adapter for registered rule `order.add_le_add_left`. -/
theorem complexAddPreservesLessEqualWithCommonLeft
    {u a b : ℂ}
    (hab : Litex.Le a b) :
    Litex.Le (u + a) (u + b) := by
  simpa [Litex.Le, Litex.OrderValue] using add_le_add_left hab u.re

/-- Componentwise addition preserves Litex non-strict order.
This is the Lean adapter for registered rule `order.add_le_add`. -/
theorem complexAddPreservesLessEqualComponentwise
    {a b c d : ℂ}
    (hab : Litex.Le a b)
    (hcd : Litex.Le c d) :
    Litex.Le (a + c) (b + d) := by
  simpa [Litex.Le, Litex.OrderValue] using add_le_add hab hcd

/-- Adding one common complex term preserves Litex strict order.
This is the Lean adapter for registered rule `order.add_lt_add_left`. -/
theorem complexAddPreservesLessWithCommonLeft
    {u a b : ℂ}
    (hab : Litex.Lt a b) :
    Litex.Lt (u + a) (u + b) := by
  simpa [Litex.Lt, Litex.OrderValue] using add_lt_add_left hab u.re

/-- Componentwise addition preserves Litex strict order.
This is the Lean adapter for registered rule `order.add_lt_add`. -/
theorem complexAddPreservesLessComponentwise
    {a b c d : ℂ}
    (hab : Litex.Lt a b)
    (hcd : Litex.Lt c d) :
    Litex.Lt (a + c) (b + d) := by
  simpa [Litex.Lt, Litex.OrderValue] using add_lt_add hab hcd

/-- A strict left comparison and weak right comparison give a strict
componentwise sum comparison. This is the Lean adapter for registered rule
`order.add_lt_add_of_lt_of_le`. -/
theorem complexAddPreservesLessOfLessAndLessEqual
    {a b c d : ℂ}
    (hab : Litex.Lt a b)
    (hcd : Litex.Le c d) :
    Litex.Lt (a + c) (b + d) := by
  simpa [Litex.Lt, Litex.Le, Litex.OrderValue] using add_lt_add_of_lt_of_le hab hcd

/-- A weak left comparison and strict right comparison give a strict
componentwise sum comparison. This is the Lean adapter for registered rule
`order.add_lt_add_of_le_of_lt`. -/
theorem complexAddPreservesLessOfLessEqualAndLess
    {a b c d : ℂ}
    (hab : Litex.Le a b)
    (hcd : Litex.Lt c d) :
    Litex.Lt (a + c) (b + d) := by
  simpa [Litex.Lt, Litex.Le, Litex.OrderValue] using add_lt_add_of_le_of_lt hab hcd

/-- Exact-real adapter for registered rule
`order.le_add_of_nonnegative_right`. -/
theorem realCastLeAddOfNonnegativeRight
    (a b : ℝ)
    (hb : Litex.Le (0 : ℂ) (b : ℂ)) :
    Litex.Le (a : ℂ) ((a : ℂ) + (b : ℂ)) := by
  simpa [Litex.Le, Litex.OrderValue] using
    (show a ≤ a + b from le_add_of_nonneg_right (by
      simpa [Litex.Le, Litex.OrderValue] using hb))

/-- Exact-real adapter for registered rule
`order.sub_le_of_le_of_nonnegative`. -/
theorem realCastSubLeOfLeOfNonnegative
    (a b c : ℝ)
    (hab : Litex.Le (a : ℂ) (b : ℂ))
    (hc : Litex.Le (0 : ℂ) (c : ℂ)) :
    Litex.Le ((a : ℂ) - (c : ℂ)) (b : ℂ) := by
  have hab' : a ≤ b := by
    simpa [Litex.Le, Litex.OrderValue] using hab
  have hc' : 0 ≤ c := by
    simpa [Litex.Le, Litex.OrderValue] using hc
  simpa [Litex.Le, Litex.OrderValue] using
    (show a - c ≤ b from (sub_le_self a hc').trans hab')

/-- Introduce membership in a predicate-defined set from a semantically equal
base representative satisfying the predicate. -/
theorem inSetBuilder
    {base : Litex.Set.{u}}
    {predicate : base.Carrier → Prop}
    {α : Litex.u.{u}}
    {x : α}
    {y : base.Carrier}
    (hxy : Litex.Same x y)
    (hy : predicate y) :
    Litex.In x (Litex.setBuilder base predicate) := by
  let selected : Subtype predicate := ⟨y, hy⟩
  exact ⟨selected, .trans hxy (.symm (.subtype selected))⟩

/-- Membership in a predicate-defined set always yields a satisfying base
representative semantically equal to the original value. -/
theorem inSetBuilder_iff
    {base : Litex.Set.{u}}
    {predicate : base.Carrier → Prop}
    {α : Litex.u.{u}}
    {x : α} :
    Litex.In x (Litex.setBuilder base predicate) ↔
      ∃ y : base.Carrier, predicate y ∧ Litex.Same x y := by
  constructor
  · rintro ⟨selected, hxSelected⟩
    exact ⟨selected.val, selected.property,
      .trans hxSelected (.subtype selected)⟩
  · rintro ⟨y, hy, hxy⟩
    exact inSetBuilder hxy hy

theorem inBaseOfInSetBuilder
    {base : Litex.Set.{u}}
    {predicate : base.Carrier → Prop}
    {α : Litex.u.{u}}
    {x : α}
    (h : Litex.In x (Litex.setBuilder base predicate)) :
    Litex.In x base := by
  rcases (inSetBuilder_iff.mp h) with ⟨y, _, hxy⟩
  exact ⟨y, hxy⟩

/-- A checked positive natural numeral constructs the exact `N+` subtype
carrier rather than reusing the carrier of `N`. -/
theorem complexEqNatInNPos
    (z : ℂ)
    (n : ℕ)
    (hz : z = (n : ℂ))
    (h : 0 < n) :
    Litex.In z Litex.NPos :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexNat n))
    h

/-- Forget only the refining predicate carried by `N+`; the selected natural
representative and its semantic equality are preserved. -/
theorem inNOfInNPos
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.NPos) :
    Litex.In x Litex.N :=
  inBaseOfInSetBuilder h

/-- Exact `N+` membership exposes strict positivity through the retained
natural representative and its canonical real observation. -/
theorem positiveOfInNPos
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.NPos) :
    Litex.Positive x := by
  rcases (inSetBuilder_iff.mp h) with ⟨n, hn, hxn⟩
  refine Litex.Positive.intro (Litex.Same.trans hxn (Litex.AsReal.nat n)) ?_
  exact_mod_cast hn

/-- `N+` retains positivity on its exact selected subtype representative. -/
theorem positiveNaturalRepPositive
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.NPos) :
    Litex.Lt (0 : ℂ) (((Litex.In.rep x h).val : ℕ) : ℂ) := by
  have hn : 0 < (Litex.In.rep x h).val := (Litex.In.rep x h).property
  have hr : (0 : ℝ) < ((Litex.In.rep x h).val : ℝ) := by
    exact_mod_cast hn
  simpa [Litex.Lt, Litex.OrderValue] using hr

/-- A checked positive rational constructs the exact `Q+` subtype carrier. -/
theorem complexEqRatInQPos
    (z : ℂ)
    (q : ℚ)
    (hz : z = (q : ℂ))
    (h : 0 < q) :
    Litex.In z Litex.QPos :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexRat q))
    h

/-- Exact `Q+` membership exposes strict positivity through its retained
rational representative. -/
theorem positiveOfInQPos
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QPos) :
    Litex.Positive x := by
  rcases (inSetBuilder_iff.mp h) with ⟨q, hq, hxq⟩
  exact Litex.Positive.intro (Litex.Same.trans hxq (Litex.AsReal.rat q)) (by exact_mod_cast hq)

/-- `Q+` retains positivity on its exact selected subtype representative. -/
theorem positiveRationalRepPositive
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QPos) :
    Litex.Lt (0 : ℂ) (((Litex.In.rep x h).val : ℚ) : ℂ) := by
  have hq : 0 < (Litex.In.rep x h).val := (Litex.In.rep x h).property
  have hr : (0 : ℝ) < ((Litex.In.rep x h).val : ℝ) := by
    exact_mod_cast hq
  simpa [Litex.Lt, Litex.OrderValue] using hr

/-- A checked positive real numeral constructs the exact `R+` subtype
carrier from its native real representative. -/
theorem complexEqRealInRPos
    (z : ℂ)
    (r : ℝ)
    (hz : z = (r : ℂ))
    (h : 0 < r) :
    Litex.In z Litex.RPos :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexReal r))
    h

/-- A positive native integer base raised to a nonnegative integral exponent
has an exact positive-real representative through Mathlib's rational `zpow`.
This is the fixed target adapter for the verifier's typed power/equality
transport certificate. -/
theorem positiveIntegerRationalPowInRPos
    (base : ℤ)
    (exponent : ℤ)
    (basePositive : Litex.Lt (0 : ℂ) (base : ℂ))
    (exponentNonnegative : 0 ≤ exponent) :
    Litex.In ((((base : ℚ) ^ exponent : ℚ) : ℂ)) Litex.RPos := by
  apply complexEqRealInRPos
      ((((base : ℚ) ^ exponent : ℚ) : ℂ))
      ((((base : ℚ) ^ exponent : ℚ) : ℝ))
  · norm_cast
  · have basePositiveInteger : 0 < base := by
      simpa [Litex.Lt, Litex.OrderValue] using basePositive
    have basePositiveRational : (0 : ℚ) < (base : ℚ) := by
      exact_mod_cast basePositiveInteger
    exact_mod_cast zpow_pos basePositiveRational exponent

theorem eInRPos : Litex.In ((Real.exp 1 : ℝ) : ℂ) Litex.RPos :=
  inSetBuilder (Litex.Same.complexReal (Real.exp 1)) (Real.exp_pos 1)

theorem piInRPos : Litex.In ((Real.pi : ℝ) : ℂ) Litex.RPos :=
  inSetBuilder (Litex.Same.complexReal Real.pi) Real.pi_pos

/-- Forget the refining predicate carried by `R+` while retaining its selected
native real representative. -/
theorem inROfInRPos
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RPos) :
    Litex.In x Litex.R :=
  inBaseOfInSetBuilder h

/-- Exact `R+` membership exposes strict positivity using the same retained
native real witness; no representative-coherence assumption is needed. -/
theorem positiveOfInRPos
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RPos) :
    Litex.Positive x := by
  rcases (inSetBuilder_iff.mp h) with ⟨r, hr, hxr⟩
  exact Litex.Positive.intro hxr hr

/-- `R+` retains positivity on its exact selected subtype representative. -/
theorem positiveRealRepPositive
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RPos) :
    Litex.Lt (0 : ℂ) (((Litex.In.rep x h).val : ℝ) : ℂ) := by
  simpa [Litex.Lt, Litex.OrderValue] using (Litex.In.rep x h).property

/-- Checked negative integer/rational/real numerals construct the exact
refined carrier retained by their successful Result. -/
theorem complexEqIntInZNeg
    (z : ℂ)
    (n : ℤ)
    (hz : z = (n : ℂ))
    (h : n < 0) :
    Litex.In z Litex.ZNeg :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexInt n))
    h

theorem complexEqRatInQNeg
    (z : ℂ)
    (q : ℚ)
    (hz : z = (q : ℂ))
    (h : q < 0) :
    Litex.In z Litex.QNeg :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexRat q))
    h

theorem complexEqRealInRNeg
    (z : ℂ)
    (r : ℝ)
    (hz : z = (r : ℂ))
    (h : r < 0) :
    Litex.In z Litex.RNeg :=
  inSetBuilder
    (Litex.Same.trans (Litex.Same.ofEq hz) (Litex.Same.complexReal r))
    h

/-- Exact negative-carrier memberships expose one selected real
representative, so the conclusion remains valid for heterogeneous source
objects and not only for a freshly reconstructed complex numeral. -/
theorem negativeOfInZNeg
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.ZNeg) :
    Litex.Negative x := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact Litex.Negative.intro (Litex.Same.trans hxz (Litex.AsReal.int z)) (by exact_mod_cast hz)

/-- `Z-` retains negativity on its exact selected integer representative. -/
theorem negativeIntegerRepNegative
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.ZNeg) :
    Litex.Lt (((Litex.In.rep x h).val : ℤ) : ℂ) (0 : ℂ) := by
  have hz : (Litex.In.rep x h).val < 0 := (Litex.In.rep x h).property
  have hr : ((Litex.In.rep x h).val : ℝ) < (0 : ℝ) := by
    exact_mod_cast hz
  simpa [Litex.Lt, Litex.OrderValue] using hr

theorem negativeOfInQNeg
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QNeg) :
    Litex.Negative x := by
  rcases (inSetBuilder_iff.mp h) with ⟨q, hq, hxq⟩
  exact Litex.Negative.intro (Litex.Same.trans hxq (Litex.AsReal.rat q)) (by exact_mod_cast hq)

/-- `Q-` retains negativity on its exact selected rational representative. -/
theorem negativeRationalRepNegative
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QNeg) :
    Litex.Lt (((Litex.In.rep x h).val : ℚ) : ℂ) (0 : ℂ) := by
  have hq : (Litex.In.rep x h).val < 0 := (Litex.In.rep x h).property
  have hr : ((Litex.In.rep x h).val : ℝ) < (0 : ℝ) := by
    exact_mod_cast hq
  simpa [Litex.Lt, Litex.OrderValue] using hr

theorem negativeOfInRNeg
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RNeg) :
    Litex.Negative x := by
  rcases (inSetBuilder_iff.mp h) with ⟨r, hr, hxr⟩
  exact Litex.Negative.intro hxr hr

/-- `R-` retains negativity on its exact selected real representative. -/
theorem negativeRealRepNegative
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RNeg) :
    Litex.Lt (((Litex.In.rep x h).val : ℝ) : ℂ) (0 : ℂ) := by
  simpa [Litex.Lt, Litex.OrderValue] using (Litex.In.rep x h).property

/-- Construct exact nonzero-integer membership from the verifier's base
membership and heterogeneous non-equality premises. -/
theorem inZStarOfInZNotSameZero
    {alpha : Type}
    {x : alpha}
    (hbase : Litex.In x Litex.Z)
    (hnonzero : ¬ Litex.Same x (0 : ℂ)) :
    Litex.In x Litex.ZStar := by
  rcases inCOfInR (inROfInQ (inQOfInZ hbase)) with ⟨z, hxz⟩
  apply inSetBuilder hxz
  constructor
  · exact (Litex.In.congr hxz Litex.Z).mp hbase
  · intro hz
    exact hnonzero (Litex.Same.trans hxz hz)

/-- Construct exact nonzero-rational membership from the verifier's base
membership and heterogeneous non-equality premises. -/
theorem inQStarOfInQNotSameZero
    {alpha : Type}
    {x : alpha}
    (hbase : Litex.In x Litex.Q)
    (hnonzero : ¬ Litex.Same x (0 : ℂ)) :
    Litex.In x Litex.QStar := by
  rcases inCOfInR (inROfInQ hbase) with ⟨z, hxz⟩
  apply inSetBuilder hxz
  constructor
  · exact (Litex.In.congr hxz Litex.Q).mp hbase
  · intro hz
    exact hnonzero (Litex.Same.trans hxz hz)

/-- Construct exact nonzero-real membership from the verifier's base
membership and heterogeneous non-equality premises. -/
theorem inRStarOfInRNotSameZero
    {alpha : Type}
    {x : alpha}
    (hbase : Litex.In x Litex.R)
    (hnonzero : ¬ Litex.Same x (0 : ℂ)) :
    Litex.In x Litex.RStar := by
  rcases inCOfInR hbase with ⟨z, hxz⟩
  apply inSetBuilder hxz
  constructor
  · exact (Litex.In.congr hxz Litex.R).mp hbase
  · intro hz
    exact hnonzero (Litex.Same.trans hxz hz)

/-- Construct exact nonzero-complex membership from the verifier's base
membership and heterogeneous non-equality premises. -/
theorem inCStarOfInCNotSameZero
    {alpha : Type}
    {x : alpha}
    (hbase : Litex.In x Litex.C)
    (hnonzero : ¬ Litex.Same x (0 : ℂ)) :
    Litex.In x Litex.CStar := by
  rcases hbase with ⟨z, hxz⟩
  apply inSetBuilder hxz
  constructor
  · exact Litex.In.own Litex.C z
  · intro hz
    exact hnonzero (Litex.Same.trans hxz hz)

theorem inZOfInZStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.ZStar) :
    Litex.In x Litex.Z := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact (Litex.In.congr hxz Litex.Z).mpr hz.1

theorem inQOfInQStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QStar) :
    Litex.In x Litex.Q := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact (Litex.In.congr hxz Litex.Q).mpr hz.1

theorem inROfInRStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RStar) :
    Litex.In x Litex.R := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact (Litex.In.congr hxz Litex.R).mpr hz.1

theorem inCOfInCStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.CStar) :
    Litex.In x Litex.C := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact (Litex.In.congr hxz Litex.C).mpr hz.1

/-- Exact `Z*` membership exposes the retained semantic nonzero certificate. -/
theorem notSameZeroOfInZStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.ZStar) :
    ¬ Litex.Same x (0 : ℂ) := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  intro hx
  exact hz.2 (Litex.Same.trans (Litex.Same.symm hxz) hx)

/-- Exact `Q*` membership exposes the retained semantic nonzero certificate. -/
theorem notSameZeroOfInQStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QStar) :
    ¬ Litex.Same x (0 : ℂ) := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  intro hx
  exact hz.2 (Litex.Same.trans (Litex.Same.symm hxz) hx)

/-- Exact `R*` membership exposes the retained semantic nonzero certificate. -/
theorem notSameZeroOfInRStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RStar) :
    ¬ Litex.Same x (0 : ℂ) := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  intro hx
  exact hz.2 (Litex.Same.trans (Litex.Same.symm hxz) hx)

/-- Exact `C*` membership exposes the retained semantic nonzero certificate. -/
theorem notSameZeroOfInCStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.CStar) :
    ¬ Litex.Same x (0 : ℂ) := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  intro hx
  exact hz.2 (Litex.Same.trans (Litex.Same.symm hxz) hx)

/-- Widen retained nonzero-integer evidence to nonzero-rational evidence. -/
theorem inQStarOfInZStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.ZStar) :
    Litex.In x Litex.QStar := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact inSetBuilder hxz ⟨inQOfInZ hz.1, hz.2⟩

/-- Widen retained nonzero-rational evidence to nonzero-real evidence. -/
theorem inRStarOfInQStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.QStar) :
    Litex.In x Litex.RStar := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact inSetBuilder hxz ⟨inROfInQ hz.1, hz.2⟩

/-- Widen retained nonzero-real evidence to nonzero-complex evidence. -/
theorem inCStarOfInRStar
    {alpha : Type}
    {x : alpha}
    (h : Litex.In x Litex.RStar) :
    Litex.In x Litex.CStar := by
  rcases (inSetBuilder_iff.mp h) with ⟨z, hz, hxz⟩
  exact inSetBuilder hxz ⟨inCOfInR hz.1, hz.2⟩

/-!
## Sequential completeness of the exact real-sequence carrier

Litex sequences are indexed by positive naturals. The Lean contract uses the
equivalent zero-based Mathlib sequence obtained by sending `n` to source index
`n + 1`; source positive cutoffs are therefore lowered by subtracting one.
-/

abbrev RealSequence := Litex.Fn Litex.NPos Litex.R

def positiveRealValue (epsilon : Litex.RPos.Carrier) : ℝ := by
  change {r : ℝ // 0 < r} at epsilon
  exact epsilon.val

def positiveNaturalZeroIndex (index : Litex.NPos.Carrier) : ℕ := by
  change {n : ℕ // 0 < n} at index
  exact index.val - 1

def realSequenceAt (a : RealSequence) (n : ℕ) : ℝ :=
  a.callOwn (by
    change {n : ℕ // 0 < n}
    exact ⟨n + 1, Nat.zero_lt_succ n⟩)

def RealSequenceTailClose
    (a : RealSequence)
    (limit epsilon : ℝ)
    (start : ℕ) : Prop :=
  ∀ n : ℕ,
    start ≤ n → dist (realSequenceAt a n) limit < epsilon

def RealSequenceConvergesTo (a : RealSequence) (limit : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ start : ℕ,
      RealSequenceTailClose a limit epsilon start

def RealSequenceConvergent (a : RealSequence) : Prop :=
  ∃ limit : ℝ, RealSequenceConvergesTo a limit

def RealSequenceCauchyTail
    (a : RealSequence)
    (epsilon : ℝ)
    (start : ℕ) : Prop :=
  ∀ m n : ℕ,
    start ≤ m → start ≤ n →
      dist (realSequenceAt a m) (realSequenceAt a n) < epsilon

def RealSequenceCauchy (a : RealSequence) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ start : ℕ,
      RealSequenceCauchyTail a epsilon start

/-- Mathlib's `CompleteSpace ℝ` discharges the only completeness step. -/
theorem realCauchySequenceConverges
    (a : RealSequence)
    (cauchy : RealSequenceCauchy a) :
    RealSequenceConvergent a := by
  have nativeCauchy : CauchySeq (realSequenceAt a) :=
    Metric.cauchySeq_iff.mpr (by
      intro epsilon epsilonPositive
      obtain ⟨start, tail⟩ := cauchy epsilon epsilonPositive
      exact ⟨start, fun m hm n hn => tail m n hm hn⟩)
  obtain ⟨limit, tends⟩ := cauchySeq_tendsto_of_complete nativeCauchy
  exact ⟨limit, Metric.tendsto_atTop.mp tends⟩

end Litex.Rules
