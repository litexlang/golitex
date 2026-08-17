import Litex.Rules

set_option linter.style.nameCheck false

namespace __SetSystem01

/-!
Tracer: heterogeneous equality transports Litex membership.

Before the v2 set core, native carrier equality could not retain one object's
memberships in both `R` and `C` without retyping or casting the object.

Now the intended Litex source

  forall a R, b C:
      a = b
      =>:
          b $in R
          a $in C

is represented by `__fact0` below. Both source variables and
the numeral convention use `ℂ`; membership remains separate evidence.

Boundary: this module defines no Litex function-space or application semantics.
It also installs no primitive bridge between arbitrary unrelated Lean types.

Evidence: `lake build` from the compiler2 `lean` repository; its
`Compiler2Examples` target owns this example directory.
-/

theorem __fact0 :
    ∀ (a : ℂ) (__h0_1 : Litex.In a Litex.R)
      (b : ℂ) (__h0_2 : Litex.In b Litex.C)
      (__h0_3 : Litex.Same a b),
      Litex.In b Litex.R ∧ Litex.In a Litex.C := by
  intro a __h0_1 b __h0_2 __h0_3
  exact ⟨
    (Litex.In.congr __h0_3 Litex.R).mp __h0_1,
    (Litex.In.congr __h0_3 Litex.C).mpr __h0_2
  ⟩

end __SetSystem01

namespace __UserSet01

/-- A user-defined Litex set whose exact carrier is a new Lean type. -/
inductive __Marker where
  | first
  | second

abbrev Markers : Litex.Set :=
  Litex.Set.ofType __Marker

def marker : __Marker := .first

theorem __fact0 : Litex.In marker Markers :=
  Litex.In.own Markers marker

/-- A user-defined subset uses a subtype carrier instead of storing
`Set.univ`. -/
abbrev NonzeroReal : Litex.Set :=
  Litex.setBuilder Litex.R (fun r => r ≠ 0)

theorem twoInNonzeroReal : Litex.In (2 : ℂ) NonzeroReal := by
  exact Litex.Rules.inSetBuilder
    (Litex.Same.complexReal (2 : ℝ))
    (by norm_num)

theorem twoInReal : Litex.In (2 : ℂ) Litex.R :=
  Litex.Rules.inBaseOfInSetBuilder twoInNonzeroReal

-- The nearest executable boundary: this command is required to fail because
-- the imported v2 header installs no `Bool`-to-`Nat` bridge rule.
#guard_msgs (drop error) in
#synth Litex.BridgeRule Bool Nat

#print axioms __SetSystem01.__fact0
#print axioms __UserSet01.__fact0
#print axioms twoInNonzeroReal
#print axioms twoInReal

end __UserSet01

namespace __HigherUniverseSet01

/-!
`Litex.Set.{0}` itself lives in `Type 1`, so a collection whose elements are
small Litex sets uses `Litex.Set.{1}`.  The ordered-numeric layer being confined
to ordinary Mathlib values does not restrict this construction.
-/

abbrev SmallSets : Litex.Set.{1} :=
  Litex.Set.ofType (Litex.Set.{0})

def theRealSet : Litex.Set.{0} :=
  Litex.R

theorem realSetInSmallSets : Litex.In theRealSet SmallSets :=
  Litex.In.own SmallSets theRealSet

#print axioms realSetInSmallSets

end __HigherUniverseSet01
