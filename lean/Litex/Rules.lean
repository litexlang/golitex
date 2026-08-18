import Litex.Core

namespace Litex.Rules

universe u

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

private theorem complexZeroAddAsReal
    {r s : ℝ}
    (hr : Litex.AsReal (0 : ℂ) r)
    (hs : Litex.AsReal (0 : ℂ) s) :
    Litex.AsReal (0 : ℂ) (r + s) := by
  have hsum : Litex.Same (r + s) ((0 : ℂ) + (0 : ℂ)) :=
    Litex.Same.realAddComplex (Litex.Same.symm hr) (Litex.Same.symm hs)
  exact Litex.Same.trans
    (Litex.Same.ofEq (by norm_num))
    (Litex.Same.symm hsum)

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

/-- The concrete complex-carrier adapter for Litex's nonnegative-addition
builtin rule. It combines the independently selected zero representatives
instead of assuming global representative coherence. -/
theorem complexAddNonnegative
    {a b : ℂ}
    (ha : Litex.Le (0 : ℂ) a)
    (hb : Litex.Le (0 : ℂ) b) :
    Litex.Le (0 : ℂ) (a + b) := by
  rcases ha with ⟨ra0, ra, hra0, hra, haOrder⟩
  rcases hb with ⟨rb0, rb, hrb0, hrb, hbOrder⟩
  exact ⟨ra0 + rb0, ra + rb,
    complexZeroAddAsReal hra0 hrb0,
    complexAddAsReal hra hrb,
    add_le_add haOrder hbOrder⟩

/-- The concrete complex-carrier adapter for Litex's strict-left,
nonnegative-right addition builtin rule. -/
theorem complexAddPositiveLeftStrict
    {a b : ℂ}
    (ha : Litex.Lt (0 : ℂ) a)
    (hb : Litex.Le (0 : ℂ) b) :
    Litex.Lt (0 : ℂ) (a + b) := by
  rcases ha with ⟨ra0, ra, hra0, hra, haOrder⟩
  rcases hb with ⟨rb0, rb, hrb0, hrb, hbOrder⟩
  exact ⟨ra0 + rb0, ra + rb,
    complexZeroAddAsReal hra0 hrb0,
    complexAddAsReal hra hrb,
    add_lt_add_of_lt_of_le haOrder hbOrder⟩

/-- The concrete complex-carrier adapter for Litex's nonnegative-left,
strict-right addition builtin rule. -/
theorem complexAddPositiveRightStrict
    {a b : ℂ}
    (ha : Litex.Le (0 : ℂ) a)
    (hb : Litex.Lt (0 : ℂ) b) :
    Litex.Lt (0 : ℂ) (a + b) := by
  rcases ha with ⟨ra0, ra, hra0, hra, haOrder⟩
  rcases hb with ⟨rb0, rb, hrb0, hrb, hbOrder⟩
  exact ⟨ra0 + rb0, ra + rb,
    complexZeroAddAsReal hra0 hrb0,
    complexAddAsReal hra hrb,
    add_lt_add_of_le_of_lt haOrder hbOrder⟩

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

end Litex.Rules
