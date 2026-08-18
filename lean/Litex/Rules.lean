import Litex.Core

namespace Litex.Rules

universe u

theorem complexInC (z : ℂ) : Litex.In z Litex.C :=
  Litex.In.own Litex.C z

theorem complexNatInN (n : ℕ) : Litex.In (n : ℂ) Litex.N :=
  ⟨n, Litex.Same.complexNat n⟩

theorem complexIntInZ (z : ℤ) : Litex.In (z : ℂ) Litex.Z :=
  ⟨z, Litex.Same.complexInt z⟩

theorem complexRatInQ (q : ℚ) : Litex.In (q : ℂ) Litex.Q :=
  ⟨q, Litex.Same.complexRat q⟩

theorem complexRealInR (r : ℝ) : Litex.In (r : ℂ) Litex.R :=
  ⟨r, Litex.Same.complexReal r⟩

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

/-- Addition preserves real membership for complex-carrier source values. -/
theorem complexAddInR
    {a b : ℂ}
    (ha : Litex.In a Litex.R)
    (hb : Litex.In b Litex.R) :
    Litex.In (a + b) Litex.R := by
  rcases ha with ⟨ra, hra⟩
  rcases hb with ⟨rb, hrb⟩
  exact ⟨ra + rb, complexAddAsReal hra hrb⟩

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
