import Litex.Core

namespace Litex

/-!
The ordered-numeric layer deliberately lives at Lean universe `0`: Mathlib's
native `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ` all live there.  This does not restrict the
universe-polymorphic `Litex.Set`, `Litex.In`, or `Litex.Same` interfaces.

An open `BridgeRule` registry can contain an incoherent user extension.  Facts
which only transport a chosen real representative need no global assumption.
Facts which compare two representatives of the same object explicitly require
`RealCoherence`.  Supplying that certificate after installing an unsound bridge
is therefore a visible trust decision, rather than a hidden axiom of this file.
-/

/-- `x` has the real representative `r` when Litex semantic equality relates
the (possibly differently typed) value `x` to the native Mathlib real `r`. -/
def AsReal {α : Type} (x : α) (r : ℝ) : Prop :=
  Same x r

/-- The registry-level invariant needed whenever a proof must identify two
real representatives.  The core declares the certificate shape but does not
postulate an inhabitant. -/
class RealCoherence : Prop where
  unique :
    ∀ {α : Type} (x : α) {r s : ℝ},
      AsReal x r → AsReal x s → r = s

namespace AsReal

theorem real (r : ℝ) : AsReal r r :=
  .refl r

theorem complex (r : ℝ) : AsReal (r : ℂ) r :=
  Same.complexReal r

theorem nat (n : ℕ) : AsReal n (n : ℝ) :=
  .trans (Same.natComplex n) (Same.complexReal (n : ℝ))

theorem int (z : ℤ) : AsReal z (z : ℝ) :=
  .trans (Same.intComplex z) (Same.complexReal (z : ℝ))

theorem rat (q : ℚ) : AsReal q (q : ℝ) :=
  .trans (Same.ratComplex q) (Same.complexReal (q : ℝ))

/-- Semantic equality transports a chosen real representative. -/
theorem congr
    {α β : Type}
    {x : α}
    {y : β}
    {r : ℝ}
    (hxy : Same x y) :
    AsReal x r ↔ AsReal y r := by
  constructor
  · intro hxr
    exact .trans (.symm hxy) hxr
  · intro hyr
    exact .trans hxy hyr

/-- Values with the same real representative are semantically equal. -/
theorem same
    {α β : Type}
    {x : α}
    {y : β}
    {r : ℝ}
    (hxr : AsReal x r)
    (hyr : AsReal y r) :
    Same x y :=
  .trans hxr (.symm hyr)

theorem unique
    [RealCoherence]
    {α : Type}
    (x : α)
    {r s : ℝ}
    (hxr : AsReal x r)
    (hxs : AsReal x s) :
    r = s :=
  RealCoherence.unique x hxr hxs

end AsReal

/-- Membership in `R` is exactly existence of a real representative. -/
theorem inR_iff_asReal
    {α : Type}
    {x : α} :
    In x R ↔ ∃ r : ℝ, AsReal x r :=
  Iff.rfl

/-- Heterogeneous strict comparison through native Mathlib reals. -/
def Lt
    {α β : Type}
    (x : α)
    (y : β) : Prop :=
  ∃ r s : ℝ, AsReal x r ∧ AsReal y s ∧ r < s

/-- Heterogeneous non-strict comparison through native Mathlib reals. -/
def Le
    {α β : Type}
    (x : α)
    (y : β) : Prop :=
  ∃ r s : ℝ, AsReal x r ∧ AsReal y s ∧ r ≤ s

namespace Lt

theorem intro
    {α β : Type}
    {x : α}
    {y : β}
    {r s : ℝ}
    (hxr : AsReal x r)
    (hys : AsReal y s)
    (hrs : r < s) :
    Lt x y :=
  ⟨r, s, hxr, hys, hrs⟩

theorem congr
    {α α' β β' : Type}
    {x : α}
    {x' : α'}
    {y : β}
    {y' : β'}
    (hxx' : Same x x')
    (hyy' : Same y y') :
    Lt x y ↔ Lt x' y' := by
  constructor
  · rintro ⟨r, s, hxr, hys, hrs⟩
    exact ⟨r, s,
      (AsReal.congr hxx').mp hxr,
      (AsReal.congr hyy').mp hys,
      hrs⟩
  · rintro ⟨r, s, hxr, hys, hrs⟩
    exact ⟨r, s,
      (AsReal.congr hxx').mpr hxr,
      (AsReal.congr hyy').mpr hys,
      hrs⟩

theorem toLe
    {α β : Type}
    {x : α}
    {y : β}
    (h : Lt x y) :
    Le x y := by
  rcases h with ⟨r, s, hxr, hys, hrs⟩
  exact ⟨r, s, hxr, hys, le_of_lt hrs⟩

theorem irrefl
    [RealCoherence]
    {α : Type}
    (x : α) :
    ¬ Lt x x := by
  rintro ⟨r, s, hxr, hxs, hrs⟩
  have hrsEq : r = s := AsReal.unique x hxr hxs
  subst s
  exact (lt_irrefl r) hrs

theorem trans
    [RealCoherence]
    {α β γ : Type}
    {x : α}
    {y : β}
    {z : γ}
    (hxy : Lt x y)
    (hyz : Lt y z) :
    Lt x z := by
  rcases hxy with ⟨r, s, hxr, hys, hrs⟩
  rcases hyz with ⟨s', t, hys', hzt, hst⟩
  have hss' : s = s' := AsReal.unique y hys hys'
  subst s'
  exact ⟨r, t, hxr, hzt, lt_trans hrs hst⟩

end Lt

namespace Le

theorem intro
    {α β : Type}
    {x : α}
    {y : β}
    {r s : ℝ}
    (hxr : AsReal x r)
    (hys : AsReal y s)
    (hrs : r ≤ s) :
    Le x y :=
  ⟨r, s, hxr, hys, hrs⟩

theorem congr
    {α α' β β' : Type}
    {x : α}
    {x' : α'}
    {y : β}
    {y' : β'}
    (hxx' : Same x x')
    (hyy' : Same y y') :
    Le x y ↔ Le x' y' := by
  constructor
  · rintro ⟨r, s, hxr, hys, hrs⟩
    exact ⟨r, s,
      (AsReal.congr hxx').mp hxr,
      (AsReal.congr hyy').mp hys,
      hrs⟩
  · rintro ⟨r, s, hxr, hys, hrs⟩
    exact ⟨r, s,
      (AsReal.congr hxx').mpr hxr,
      (AsReal.congr hyy').mpr hys,
      hrs⟩

theorem reflOfAsReal
    {α : Type}
    {x : α}
    {r : ℝ}
    (hxr : AsReal x r) :
    Le x x :=
  ⟨r, r, hxr, hxr, le_rfl⟩

theorem reflOfInR
    {α : Type}
    {x : α}
    (hx : In x R) :
    Le x x := by
  rcases inR_iff_asReal.mp hx with ⟨r, hxr⟩
  exact reflOfAsReal hxr

theorem trans
    [RealCoherence]
    {α β γ : Type}
    {x : α}
    {y : β}
    {z : γ}
    (hxy : Le x y)
    (hyz : Le y z) :
    Le x z := by
  rcases hxy with ⟨r, s, hxr, hys, hrs⟩
  rcases hyz with ⟨s', t, hys', hzt, hst⟩
  have hss' : s = s' := AsReal.unique y hys hys'
  subst s'
  exact ⟨r, t, hxr, hzt, le_trans hrs hst⟩

end Le

namespace OrderBridge

/-- A native Mathlib real inequality introduces a Litex inequality without
any global coherence assumption. -/
theorem ltOfReal
    {r s : ℝ}
    (h : r < s) :
    Lt r s :=
  Lt.intro (AsReal.real r) (AsReal.real s) h

theorem leOfReal
    {r s : ℝ}
    (h : r ≤ s) :
    Le r s :=
  Le.intro (AsReal.real r) (AsReal.real s) h

theorem ltOfComplexReals
    {r s : ℝ}
    (h : r < s) :
    Lt (r : ℂ) (s : ℂ) :=
  Lt.intro (AsReal.complex r) (AsReal.complex s) h

theorem leOfComplexReals
    {r s : ℝ}
    (h : r ≤ s) :
    Le (r : ℂ) (s : ℂ) :=
  Le.intro (AsReal.complex r) (AsReal.complex s) h

theorem real_lt_iff
    [RealCoherence]
    {r s : ℝ} :
    Lt r s ↔ r < s := by
  constructor
  · rintro ⟨r', s', hrr', hss', hrs⟩
    have hr : r = r' := AsReal.unique r (AsReal.real r) hrr'
    have hs : s = s' := AsReal.unique s (AsReal.real s) hss'
    simpa [hr, hs] using hrs
  · exact ltOfReal

theorem real_le_iff
    [RealCoherence]
    {r s : ℝ} :
    Le r s ↔ r ≤ s := by
  constructor
  · rintro ⟨r', s', hrr', hss', hrs⟩
    have hr : r = r' := AsReal.unique r (AsReal.real r) hrr'
    have hs : s = s' := AsReal.unique s (AsReal.real s) hss'
    simpa [hr, hs] using hrs
  · exact leOfReal

end OrderBridge

end Litex
