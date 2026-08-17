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
