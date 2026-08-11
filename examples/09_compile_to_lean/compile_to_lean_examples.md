# Litex-to-Lean Examples

This is the default authoring ledger for small, self-contained Litex-to-Lean examples.
Append one H2 section with one Litex input fence followed by one complete generated Lean fence.
The Rust harness verifies every Litex input, regenerates Lean, and compares the adjacent snapshot byte for byte.
Strict compilation is the default. Put `<!-- to-lean: partial -->` before the Litex fence only when report mode intentionally records unsupported statements.
Use a standalone `.lit` file only when module imports, project paths, CLI behavior, or a durable acceptance artifact require real file semantics.

## native_carriers

```litex
# Primary tracer: native Mathlib carriers without invented source types.
#
# Expected Lean shapes:
#   2 = 2                         stays bare
#   2 $in R                       becomes 2 ∈ (Set.univ : Set ℝ)
#   proposition codomains         use Prop directly, with no LitexFact alias
#   cross-carrier bounded facts   live in the propositions_and_trust section,
#                                 their explicit trust boundary is visible

2 = 2
2 $in R

# More Litex-verified carrier facts live in the `carrier_boundaries` section.
# They stay out of this strict example until their proof routes have checked
# Lean backends.
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f1
theorem fact1 : 2 = 2 := by
  rfl

-- Litex fact f2
theorem fact2 : 2 ∈ (Set.univ : Set ℝ) := by
  change True
  trivial

end
```

## mixed_projected_forall

```litex
# A single source forall may store independently covered conclusions as
# separate reusable facts. Their target carriers remain occurrence-local:
# `a` is real, while `b` is a polymorphic native Lean set.
forall a R, b set:
    a = a
    b = b

# Boundary: these separate equalities do not justify the heterogeneous `a = b`.
# Persistent tracer: examples/05_compiler_interop/compile_to_lean_mixed_projected_forall.lit
# Evidence: cargo test --release compile_to_lean_mixed_projected_forall -- --nocapture
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f13
theorem fact13 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), a = a := by
  intro a litex_param_fact_1
  rfl

-- Litex fact f14
theorem fact14 : ∀ {α1 : Type u} [LitexObject α1], ∀ (b : Set α1), b = b := by
  intro _ _ b
  rfl

end
```

## bounded_facts

```litex
# Domain binders become native bounded quantifiers. Their membership facts
# remain propositions available inside the generated Lean proof.

forall x R:
    x = x

forall z Z:
    z = z

forall q Q:
    q = q

forall x R:
    x != 0
    =>:
        x != 0

forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x

forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
```

```lean
import Mathlib

namespace Litex.BuiltinRules

theorem nonzero_div
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : a ≠ 0)
    (hb : b ≠ 0) : a / b ≠ 0 := by
  exact div_ne_zero ha hb

end Litex.BuiltinRules

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f7
theorem fact7 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), x = x := by
  intro x litex_param_fact_1
  rfl

-- Litex fact f14
theorem fact14 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ (Set.univ : Set ℤ)), z = z := by
  intro z litex_param_fact_1
  rfl

-- Litex fact f21
theorem fact21 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ (Set.univ : Set ℚ)), q = q := by
  intro q litex_param_fact_1
  rfl

-- Litex fact f28
theorem fact28 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : x ≠ 0), x ≠ 0 := by
  intro x litex_param_fact_1 litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f44
theorem fact44 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (x : ℝ) (litex_param_fact_3 : x ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : x ≠ 0), ((a + b) / x) = ((a / x) + (b / x)) := by
  intro a litex_param_fact_1 b litex_param_fact_2 x litex_param_fact_3 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  have well_defined_fact_2 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses litex_param_fact_2
  have well_defined_fact_4 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses litex_domain_fact_1
  have well_defined_fact_6 : (a + b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses litex_param_fact_3
  have well_defined_fact_8 : (x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_9 : (a / x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_10 : (b / x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 11 reuses litex_param_fact_1
  -- Litex well-definedness certificate 12 reuses well_defined_fact_2
  -- Litex well-definedness certificate 13 reuses litex_param_fact_2
  -- Litex well-definedness certificate 14 reuses well_defined_fact_4
  -- Litex well-definedness certificate 15 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 16 reuses well_defined_fact_6
  -- Litex well-definedness certificate 17 reuses litex_param_fact_3
  -- Litex well-definedness certificate 18 reuses well_defined_fact_8
  -- Litex well-definedness certificate 19 reuses well_defined_fact_9
  -- Litex well-definedness certificate 20 reuses well_defined_fact_10
  -- Litex well-definedness certificate 21 reuses litex_param_fact_1
  -- Litex well-definedness certificate 22 reuses well_defined_fact_2
  -- Litex well-definedness certificate 23 reuses litex_param_fact_2
  -- Litex well-definedness certificate 24 reuses well_defined_fact_4
  -- Litex well-definedness certificate 25 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 26 reuses well_defined_fact_6
  -- Litex well-definedness certificate 27 reuses litex_param_fact_3
  -- Litex well-definedness certificate 28 reuses well_defined_fact_8
  -- Litex well-definedness certificate 29 reuses well_defined_fact_9
  -- Litex well-definedness certificate 30 reuses well_defined_fact_10
  -- native proof view, left fraction: (a + b) / x
  -- native proof view, right fraction: ((a * x) + (b * x)) / (x * x)
  field_simp [litex_domain_fact_1] <;> ring

-- Litex fact f60
theorem fact60 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≠ 0), ∀ (litex_domain_fact_2 : b ≠ 0), (a / b) ≠ 0 := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_domain_fact_2
  -- Litex well-definedness certificate 2 reuses litex_param_fact_1
  have well_defined_fact_3 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  have well_defined_fact_5 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 6 reuses litex_domain_fact_2
  -- Litex well-definedness certificate 7 reuses litex_param_fact_1
  -- Litex well-definedness certificate 8 reuses well_defined_fact_3
  -- Litex well-definedness certificate 9 reuses litex_param_fact_2
  -- Litex well-definedness certificate 10 reuses well_defined_fact_5
  -- Litex well-definedness certificate 11 reuses litex_domain_fact_2
  -- Litex well-definedness certificate 12 reuses litex_param_fact_1
  -- Litex well-definedness certificate 13 reuses well_defined_fact_3
  -- Litex well-definedness certificate 14 reuses litex_param_fact_2
  -- Litex well-definedness certificate 15 reuses well_defined_fact_5
  have proof_fact_1_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_1_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_1_3 : a ≠ 0 := by
    exact litex_domain_fact_1
  have proof_fact_1_4 : b ≠ 0 := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.nonzero_div a b proof_fact_1_1 proof_fact_1_2 proof_fact_1_3 proof_fact_1_4

end
```

## propositions_and_trust

```litex
# Abstract propositions are polymorphic over their object arguments. Only the
# explicit trusted interfaces below become Lean axioms.

abstract_prop demo_marked(x)

trust forall x R:
    $demo_marked(x)

$demo_marked(3)

prop demo_is_one(x R):
    x = 1

$demo_is_one(1)

abstract_prop demo_successor_pair(x, y)

trust forall x R:
    $demo_successor_pair(x, x + 1)

$demo_successor_pair(1, 2)

# These two propositions expose the native bounded-binder and cross-carrier
# output contracts. Membership supplies the carrier; `trust` supplies only the
# proof boundary.
trust forall x R:
    x $in R

trust forall z Z:
    z / 2 $in Q

# `trust 1 / 2 = 1 / 2` remains rejected by strict Litex-to-Lean because no judgment
# selects the division carrier.
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

opaque demo_marked {α : Type u} [LitexObject α] : α → Prop

-- Litex trust boundary: f3
axiom fact3 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), demo_marked x

-- Litex fact f4
theorem fact4 : demo_marked (3 : ℝ) := by
  -- Litex parameter requirement for `x`: 3 : ℝ
  let proof_arg_1_1 : ℝ := 3
  have proof_fact_1_2 : 3 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have proof_fact_1_3 : demo_marked (3 : ℝ) := fact3 proof_arg_1_1 proof_fact_1_2
  exact proof_fact_1_3

def demo_is_one (x : ℝ) : Prop := x = 1

-- Litex fact f7
theorem fact7 : demo_is_one 1 := by
  simp [demo_is_one]

opaque demo_successor_pair {α : Type u} [LitexObject α] {α1 : Type u} [LitexObject α1] : α → α1 → Prop

-- Litex trust boundary: f12
axiom fact12 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), demo_successor_pair x (x + 1)

-- Litex well-definedness certificate 1
theorem well_defined_fact_1 : 2 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_2 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f13
theorem fact13 : demo_successor_pair (1 : ℝ) (2 : ℝ) := by
  have proof_fact_2_1 : demo_successor_pair (2 - 1 : ℝ) ((2 - 1) + 1 : ℝ) := by
    -- Litex parameter requirement for `x`: (2 - 1) : ℝ
    let proof_arg_3_1 : ℝ := (2 - 1)
    have proof_fact_3_2 : (2 - 1) ∈ (Set.univ : Set ℝ) := by
      change True
      trivial
    have proof_fact_3_3 : demo_successor_pair (2 - 1 : ℝ) ((2 - 1) + 1 : ℝ) := fact12 proof_arg_3_1 proof_fact_3_2
    exact proof_fact_3_3
  have proof_fact_2_2 : demo_successor_pair (1 : ℝ) (2 : ℝ) := by
    convert proof_fact_2_1 using 1 <;> norm_num
  exact proof_fact_2_2

-- Litex trust boundary: f15
axiom fact15 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), x ∈ (Set.univ : Set ℝ)

-- Litex trust boundary: f18
axiom fact18 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ (Set.univ : Set ℤ)), (z / 2 : ℚ) ∈ (Set.univ : Set ℚ)

end
```

## object_definitions

```litex
# Checked real object definitions select their target carrier from the declared
# Litex domain. Their membership and defining equality are retained by the
# definition statement's proof IR.

have demo_real_two R = 2

# A real-valued division definition is intentionally not presented as strict
# coverage yet. The current emitter writes a plain `def`, while Mathlib's real
# division instance requires a `noncomputable def`:
#
# have demo_real_half R = 1 / 2

# The analogous N/Z/Q/C definitions verify in Litex and are kept in
# the `carrier_boundaries` section until their value-check routes have backends.
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

def demo_real_two : ℝ := 2

-- Litex fact f2
theorem fact2 : demo_real_two ∈ (Set.univ : Set ℝ) := by
  have proof_fact_1_1 : 2 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  simpa only [demo_real_two] using proof_fact_1_1

-- Litex fact f3
theorem fact3 : demo_real_two = 2 := by
  rfl

end
```

## equality_transport

```litex
# Equality transport preserves the verifier-selected source fact and every
# oriented equality edge needed to reach the requested target.

abstract_prop demo_transported(x)

forall a, b set:
    $demo_transported(a)
    a = b
    =>:
        $demo_transported(b)

abstract_prop demo_related(x, y)

forall a, b set:
    $demo_related(a, b)
    a = b
    =>:
        $demo_related(b, a)

forall a, b, c set:
    $demo_transported(c)
    a = b
    b = c
    =>:
        $demo_transported(a)

# Object resolution records normalization before equality transport.
abstract_prop demo_resolved(x)

forall a, b R:
    a = 13
    b = 1
    $demo_resolved(14)
    =>:
        $demo_resolved(a + b)
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

opaque demo_transported {α : Type u} [LitexObject α] : α → Prop

-- Litex fact f16
theorem fact16 : ∀ {α1 : Type u} [LitexObject α1], ∀ (a : Set α1), ∀ (b : Set α1), ∀ (litex_domain_fact_1 : demo_transported a), ∀ (litex_domain_fact_2 : a = b), demo_transported b := by
  intro _ _ a b litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_1_1 : demo_transported a := litex_domain_fact_1
  have proof_fact_1_2 : a = b := litex_domain_fact_2
  have proof_fact_1_3 : demo_transported b := by
    simpa only [proof_fact_1_2] using proof_fact_1_1
  exact proof_fact_1_3

opaque demo_related {α : Type u} [LitexObject α] {α1 : Type u} [LitexObject α1] : α → α1 → Prop

-- Litex fact f32
theorem fact32 : ∀ {α4 : Type u} [LitexObject α4], ∀ (a : Set α4), ∀ (b : Set α4), ∀ (litex_domain_fact_1 : demo_related a b), ∀ (litex_domain_fact_2 : a = b), demo_related b a := by
  intro _ _ a b litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_2_1 : demo_related a b := litex_domain_fact_1
  have proof_fact_2_2 : a = b := litex_domain_fact_2
  have proof_fact_2_3 : demo_related b a := by
    simpa only [proof_fact_2_2] using proof_fact_2_1
  exact proof_fact_2_3

-- Litex fact f54
theorem fact54 : ∀ {α6 : Type u} [LitexObject α6], ∀ (a : Set α6), ∀ (b : Set α6), ∀ (c : Set α6), ∀ (litex_domain_fact_1 : demo_transported c), ∀ (litex_domain_fact_2 : a = b), ∀ (litex_domain_fact_3 : b = c), demo_transported a := by
  intro _ _ a b c litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  have proof_fact_3_1 : demo_transported c := litex_domain_fact_1
  have proof_fact_3_2 : b = c := litex_domain_fact_3
  have proof_fact_3_3 : a = b := litex_domain_fact_2
  have proof_fact_3_4 : demo_transported a := by
    simpa only [proof_fact_3_2, proof_fact_3_3] using proof_fact_3_1
  exact proof_fact_3_4

opaque demo_resolved {α : Type u} [LitexObject α] : α → Prop

-- Litex fact f73
theorem fact73 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a = 13), ∀ (litex_domain_fact_2 : b = 1), ∀ (litex_domain_fact_3 : demo_resolved (14 : ℝ)), demo_resolved (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_4_1 : demo_resolved (13 + 1 : ℝ) := by
    have proof_fact_5_1 : demo_resolved (14 : ℝ) := litex_domain_fact_3
    have proof_fact_5_2 : demo_resolved (13 + 1 : ℝ) := by
      convert proof_fact_5_1 using 1 <;> norm_num
    exact proof_fact_5_2
  have proof_fact_4_2 : a = 13 := litex_domain_fact_1
  have proof_fact_4_3 : b = 1 := litex_domain_fact_2
  have proof_fact_4_4 : demo_resolved (a + b) := by
    simpa only [proof_fact_4_2, proof_fact_4_3] using proof_fact_4_1
  exact proof_fact_4_4

end
```

## builtin_arithmetic

```litex
# Twenty arithmetic and order facts whose successful verifier routes carry
# registered local-builtin certificates to paired Mathlib adapters.

forall a, b R:
    a < b
    =>:
        a <= b

forall a, b R:
    a > b
    =>:
        a >= b

forall u, v R:
    v <= u
    =>:
        0 <= u - v

forall u, v R:
    v < u
    =>:
        0 < u - v

forall a, b R:
    0 <= a
    0 <= b
    =>:
        0 <= a + b

forall a, b R:
    0 < a
    0 < b
    =>:
        0 < a + b

forall a, b R:
    0 < a
    0 <= b
    =>:
        0 < a + b

forall a, b R:
    0 <= a
    0 < b
    =>:
        0 < a + b

forall a, b R:
    0 <= a
    0 <= b
    =>:
        0 <= a * b

forall a, b R:
    0 < a
    0 < b
    =>:
        0 < a * b

forall a, b R:
    0 <= a
    0 < b
    =>:
        0 <= a / b

forall a, b R:
    0 < a
    0 < b
    =>:
        0 < a / b

forall u, a, b R:
    a <= b
    =>:
        u + a <= u + b

forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a + c <= b + d

forall u, a, b R:
    a < b
    =>:
        u + a < u + b

forall a, b, c, d R:
    a < b
    c < d
    =>:
        a + c < b + d

forall a, b, c, d R:
    a < b
    c <= d
    =>:
        a + c < b + d

forall a, b, c, d R:
    a <= b
    c < d
    =>:
        a + c < b + d

forall a, b, c R:
    a <= b
    0 <= c
    =>:
        a - c <= b

forall a, b R:
    0 <= b
    =>:
        a <= a + b
```

```lean
import Mathlib

namespace Litex.BuiltinRules

theorem order_add_le_add
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hab : a ≤ b)
    (hcd : c ≤ d) : a + c ≤ b + d := by
  exact add_le_add hab hcd

theorem order_add_le_add_left
    (u a b : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a ≤ b) : u + a ≤ u + b := by
  linarith only [h]

theorem order_add_lt_add
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hab : a < b)
    (hcd : c < d) : a + c < b + d := by
  exact add_lt_add hab hcd

theorem order_add_lt_add_left
    (u a b : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a < b) : u + a < u + b := by
  linarith only [h]

theorem order_add_lt_add_of_le_of_lt
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hab : a ≤ b)
    (hcd : c < d) : a + c < b + d := by
  exact add_lt_add_of_le_of_lt hab hcd

theorem order_add_lt_add_of_lt_of_le
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hab : a < b)
    (hcd : c ≤ d) : a + c < b + d := by
  exact add_lt_add_of_lt_of_le hab hcd

theorem order_add_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) : 0 ≤ a + b := by
  exact add_nonneg ha hb

theorem order_add_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 < b) : 0 < a + b := by
  exact add_pos ha hb

theorem order_add_positive_of_nonnegative_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 ≤ a)
    (hb : 0 < b) : 0 < a + b := by
  exact add_pos_of_nonneg_of_pos ha hb

theorem order_add_positive_of_positive_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 ≤ b) : 0 < a + b := by
  exact add_pos_of_pos_of_nonneg ha hb

theorem order_div_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 ≤ a)
    (hb : 0 < b) : 0 ≤ a / b := by
  exact div_nonneg ha (le_of_lt hb)

theorem order_div_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 < b) : 0 < a / b := by
  exact div_pos ha hb

theorem order_greater_equal_of_greater
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a > b) : a ≥ b := by
  exact le_of_lt h

theorem order_le_add_of_nonnegative_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (hb : 0 ≤ b) : a ≤ a + b := by
  linarith only [hb]

theorem order_less_equal_of_less
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a < b) : a ≤ b := by
  exact le_of_lt h

theorem order_mul_nonnegative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact mul_nonneg ha hb

theorem order_mul_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

theorem order_sub_le_of_le_of_nonnegative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (hab : a ≤ b)
    (hc : 0 ≤ c) : a - c ≤ b := by
  linarith only [hab, hc]

theorem order_sub_nonnegative_of_less_equal
    (u v : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_hvR : v ∈ (Set.univ : Set ℝ))
    (h : v ≤ u) : 0 ≤ u - v := by
  exact sub_nonneg.mpr h

theorem order_sub_positive_of_less
    (u v : ℝ)
    (_huR : u ∈ (Set.univ : Set ℝ))
    (_hvR : v ∈ (Set.univ : Set ℝ))
    (h : v < u) : 0 < u - v := by
  exact sub_pos.mpr h

end Litex.BuiltinRules

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f13
theorem fact13 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a < b), a ≤ b := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  have proof_fact_1_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_1_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_1_3 : a < b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_less_equal_of_less a b proof_fact_1_1 proof_fact_1_2 proof_fact_1_3

-- Litex fact f26
theorem fact26 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a > b), a ≥ b := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  have proof_fact_2_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_2_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_2_3 : a > b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_greater_equal_of_greater a b proof_fact_2_1 proof_fact_2_2 proof_fact_2_3

-- Litex fact f39
theorem fact39 : ∀ (u : ℝ) (litex_param_fact_1 : u ∈ (Set.univ : Set ℝ)), ∀ (v : ℝ) (litex_param_fact_2 : v ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : v ≤ u), (0 : ℝ) ≤ (u - v) := by
  intro u litex_param_fact_1 v litex_param_fact_2 litex_domain_fact_1
  have well_defined_fact_1 : (u : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (v : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_3_1 : u ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_3_2 : v ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_3_3 : v ≤ u := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_sub_nonnegative_of_less_equal u v proof_fact_3_1 proof_fact_3_2 proof_fact_3_3

-- Litex fact f52
theorem fact52 : ∀ (u : ℝ) (litex_param_fact_1 : u ∈ (Set.univ : Set ℝ)), ∀ (v : ℝ) (litex_param_fact_2 : v ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : v < u), (0 : ℝ) < (u - v) := by
  intro u litex_param_fact_1 v litex_param_fact_2 litex_domain_fact_1
  have well_defined_fact_1 : (u : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (v : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_4_1 : u ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_4_2 : v ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_4_3 : v < u := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_sub_positive_of_less u v proof_fact_4_1 proof_fact_4_2 proof_fact_4_3

-- Litex fact f68
theorem fact68 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 ≤ a), ∀ (litex_domain_fact_2 : 0 ≤ b), 0 ≤ (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_5_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_5_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_5_3 : 0 ≤ a := by
    exact litex_domain_fact_1
  have proof_fact_5_4 : 0 ≤ b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_nonnegative a b proof_fact_5_1 proof_fact_5_2 proof_fact_5_3 proof_fact_5_4

-- Litex fact f84
theorem fact84 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 < a), ∀ (litex_domain_fact_2 : 0 < b), 0 < (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_6_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_6_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_6_3 : 0 < a := by
    exact litex_domain_fact_1
  have proof_fact_6_4 : 0 < b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_positive a b proof_fact_6_1 proof_fact_6_2 proof_fact_6_3 proof_fact_6_4

-- Litex fact f100
theorem fact100 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 < a), ∀ (litex_domain_fact_2 : 0 ≤ b), 0 < (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_7_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_7_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_7_3 : 0 < a := by
    exact litex_domain_fact_1
  have proof_fact_7_4 : 0 ≤ b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_positive_of_positive_nonnegative a b proof_fact_7_1 proof_fact_7_2 proof_fact_7_3 proof_fact_7_4

-- Litex fact f116
theorem fact116 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 ≤ a), ∀ (litex_domain_fact_2 : 0 < b), 0 < (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_8_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_8_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_8_3 : 0 ≤ a := by
    exact litex_domain_fact_1
  have proof_fact_8_4 : 0 < b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_positive_of_nonnegative_positive a b proof_fact_8_1 proof_fact_8_2 proof_fact_8_3 proof_fact_8_4

-- Litex fact f132
theorem fact132 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 ≤ a), ∀ (litex_domain_fact_2 : 0 ≤ b), 0 ≤ (a * b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_9_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_9_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_9_3 : 0 ≤ a := by
    exact litex_domain_fact_1
  have proof_fact_9_4 : 0 ≤ b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_mul_nonnegative a b proof_fact_9_1 proof_fact_9_2 proof_fact_9_3 proof_fact_9_4

-- Litex fact f148
theorem fact148 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 < a), ∀ (litex_domain_fact_2 : 0 < b), 0 < (a * b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_10_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_10_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_10_3 : 0 < a := by
    exact litex_domain_fact_1
  have proof_fact_10_4 : 0 < b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_mul_positive a b proof_fact_10_1 proof_fact_10_2 proof_fact_10_3 proof_fact_10_4

-- Litex well-definedness certificate 2 (forall type witness)
theorem well_defined_fact_1 : 0 ∈ (Set.univ : Set ℝ) := by
  change True
  trivial

-- Litex fact f164
theorem fact164 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 ≤ a), ∀ (litex_domain_fact_2 : 0 < b), 0 ≤ (a / b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_2
  -- Litex well-definedness certificate 2 reuses well_defined_fact_1
  have proof_fact_11_1 : b > 0 := by
    have proof_fact_12_1 : (0 : ℝ) < b := litex_domain_fact_2
    exact proof_fact_12_1
  have proof_fact_11_2 : b ≠ 0 := by
    have proof_fact_13_1 : b ∈ (Set.univ : Set ℝ) := by
      exact litex_param_fact_2
    have proof_fact_13_2 : 0 ∈ (Set.univ : Set ℝ) := by
      change True
      trivial
    have proof_fact_13_3 : b > 0 := by
      have proof_fact_14_1 : (0 : ℝ) < b := litex_domain_fact_2
      exact proof_fact_14_1
    intro litex_equal
    rw [litex_equal] at proof_fact_13_3
    exact (lt_irrefl _ proof_fact_13_3)
  have well_defined_fact_5 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_6 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses litex_param_fact_2
  -- Litex well-definedness certificate 8 reuses well_defined_fact_1
  -- Litex well-definedness certificate 9 reuses proof_fact_11_1
  -- Litex well-definedness certificate 10 reuses proof_fact_11_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_5
  -- Litex well-definedness certificate 12 reuses well_defined_fact_6
  -- Litex well-definedness certificate 13 reuses litex_param_fact_2
  -- Litex well-definedness certificate 14 reuses well_defined_fact_1
  -- Litex well-definedness certificate 15 reuses proof_fact_11_1
  -- Litex well-definedness certificate 16 reuses proof_fact_11_2
  -- Litex well-definedness certificate 17 reuses well_defined_fact_5
  -- Litex well-definedness certificate 18 reuses well_defined_fact_6
  have proof_fact_11_3 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_11_4 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_11_5 : (0 : ℝ) ≤ a := by
    exact litex_domain_fact_1
  have proof_fact_11_6 : (0 : ℝ) < b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_div_nonnegative a b proof_fact_11_3 proof_fact_11_4 proof_fact_11_5 proof_fact_11_6

-- Litex well-definedness certificate 2 (forall type witness)
theorem well_defined_fact_2 : 0 ∈ (Set.univ : Set ℝ) := by
  change True
  trivial

-- Litex fact f180
theorem fact180 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : 0 < a), ∀ (litex_domain_fact_2 : 0 < b), 0 < (a / b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_2
  -- Litex well-definedness certificate 2 reuses well_defined_fact_2
  have proof_fact_15_1 : b > 0 := by
    have proof_fact_16_1 : (0 : ℝ) < b := litex_domain_fact_2
    exact proof_fact_16_1
  have proof_fact_15_2 : b ≠ 0 := by
    have proof_fact_17_1 : b ∈ (Set.univ : Set ℝ) := by
      exact litex_param_fact_2
    have proof_fact_17_2 : 0 ∈ (Set.univ : Set ℝ) := by
      change True
      trivial
    have proof_fact_17_3 : b > 0 := by
      have proof_fact_18_1 : (0 : ℝ) < b := litex_domain_fact_2
      exact proof_fact_18_1
    intro litex_equal
    rw [litex_equal] at proof_fact_17_3
    exact (lt_irrefl _ proof_fact_17_3)
  have well_defined_fact_5 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_6 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses litex_param_fact_2
  -- Litex well-definedness certificate 8 reuses well_defined_fact_2
  -- Litex well-definedness certificate 9 reuses proof_fact_15_1
  -- Litex well-definedness certificate 10 reuses proof_fact_15_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_5
  -- Litex well-definedness certificate 12 reuses well_defined_fact_6
  -- Litex well-definedness certificate 13 reuses litex_param_fact_2
  -- Litex well-definedness certificate 14 reuses well_defined_fact_2
  -- Litex well-definedness certificate 15 reuses proof_fact_15_1
  -- Litex well-definedness certificate 16 reuses proof_fact_15_2
  -- Litex well-definedness certificate 17 reuses well_defined_fact_5
  -- Litex well-definedness certificate 18 reuses well_defined_fact_6
  have proof_fact_15_3 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_15_4 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_15_5 : (0 : ℝ) < a := by
    exact litex_domain_fact_1
  have proof_fact_15_6 : (0 : ℝ) < b := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_div_positive a b proof_fact_15_3 proof_fact_15_4 proof_fact_15_5 proof_fact_15_6

-- Litex fact f196
theorem fact196 : ∀ (u : ℝ) (litex_param_fact_1 : u ∈ (Set.univ : Set ℝ)), ∀ (a : ℝ) (litex_param_fact_2 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_3 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), (u + a) ≤ (u + b) := by
  intro u litex_param_fact_1 a litex_param_fact_2 b litex_param_fact_3 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  have well_defined_fact_2 : (u : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_19_1 : u ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_19_2 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_19_3 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_19_4 : a ≤ b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_add_le_add_left u a b proof_fact_19_1 proof_fact_19_2 proof_fact_19_3 proof_fact_19_4

-- Litex fact f218
theorem fact218 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), ∀ (litex_domain_fact_2 : c ≤ d), (a + c) ≤ (b + d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses well_defined_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_20_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_20_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_20_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_20_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_20_5 : a ≤ b := by
    exact litex_domain_fact_1
  have proof_fact_20_6 : c ≤ d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_le_add a b c d proof_fact_20_1 proof_fact_20_2 proof_fact_20_3 proof_fact_20_4 proof_fact_20_5 proof_fact_20_6

-- Litex fact f234
theorem fact234 : ∀ (u : ℝ) (litex_param_fact_1 : u ∈ (Set.univ : Set ℝ)), ∀ (a : ℝ) (litex_param_fact_2 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_3 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a < b), (u + a) < (u + b) := by
  intro u litex_param_fact_1 a litex_param_fact_2 b litex_param_fact_3 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  have well_defined_fact_2 : (u : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_21_1 : u ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_21_2 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_21_3 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_21_4 : a < b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_add_lt_add_left u a b proof_fact_21_1 proof_fact_21_2 proof_fact_21_3 proof_fact_21_4

-- Litex fact f256
theorem fact256 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a < b), ∀ (litex_domain_fact_2 : c < d), (a + c) < (b + d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses well_defined_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_22_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_22_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_22_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_22_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_22_5 : a < b := by
    exact litex_domain_fact_1
  have proof_fact_22_6 : c < d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_lt_add a b c d proof_fact_22_1 proof_fact_22_2 proof_fact_22_3 proof_fact_22_4 proof_fact_22_5 proof_fact_22_6

-- Litex fact f278
theorem fact278 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a < b), ∀ (litex_domain_fact_2 : c ≤ d), (a + c) < (b + d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses well_defined_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_23_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_23_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_23_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_23_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_23_5 : a < b := by
    exact litex_domain_fact_1
  have proof_fact_23_6 : c ≤ d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_lt_add_of_lt_of_le a b c d proof_fact_23_1 proof_fact_23_2 proof_fact_23_3 proof_fact_23_4 proof_fact_23_5 proof_fact_23_6

-- Litex fact f300
theorem fact300 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), ∀ (litex_domain_fact_2 : c < d), (a + c) < (b + d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses well_defined_fact_3
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses well_defined_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_24_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_24_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_24_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_24_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_24_5 : a ≤ b := by
    exact litex_domain_fact_1
  have proof_fact_24_6 : c < d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_add_lt_add_of_le_of_lt a b c d proof_fact_24_1 proof_fact_24_2 proof_fact_24_3 proof_fact_24_4 proof_fact_24_5 proof_fact_24_6

-- Litex fact f319
theorem fact319 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), ∀ (litex_domain_fact_2 : (0 : ℝ) ≤ c), (a - c) ≤ b := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  -- Litex well-definedness certificate 4 reuses well_defined_fact_2
  -- Litex well-definedness certificate 5 reuses well_defined_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  have proof_fact_25_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_25_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_25_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_25_4 : a ≤ b := by
    exact litex_domain_fact_1
  have proof_fact_25_5 : (0 : ℝ) ≤ c := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_sub_le_of_le_of_nonnegative a b c proof_fact_25_1 proof_fact_25_2 proof_fact_25_3 proof_fact_25_4 proof_fact_25_5

-- Litex fact f332
theorem fact332 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : (0 : ℝ) ≤ b), a ≤ (a + b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  have well_defined_fact_2 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_1
  -- Litex well-definedness certificate 5 reuses well_defined_fact_2
  -- Litex well-definedness certificate 6 reuses well_defined_fact_3
  -- Litex well-definedness certificate 7 reuses litex_param_fact_1
  -- Litex well-definedness certificate 8 reuses well_defined_fact_2
  -- Litex well-definedness certificate 9 reuses well_defined_fact_3
  have proof_fact_26_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_26_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_26_3 : (0 : ℝ) ≤ b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_le_add_of_nonnegative_right a b proof_fact_26_1 proof_fact_26_2 proof_fact_26_3

end
```

## recursive_arithmetic

```litex
# The proof tree recursively decomposes the nested sum. Typed additive evidence
# is emitted bottom-up instead of reconstructing a tactic from a text label.

forall a, b, c, d R+:
    (a + b) + (c + d) > 0
```

```lean
import Mathlib

namespace Litex.BuiltinRules

theorem order_add_positive
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : 0 < a)
    (hb : 0 < b) : 0 < a + b := by
  exact add_pos ha hb

theorem order_less_equal_of_less
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a < b) : a ≤ b := by
  exact le_of_lt h

end Litex.BuiltinRules

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex well-definedness certificate 7 (forall type witness)
theorem well_defined_fact_1 : -1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f34
theorem fact34 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ {r : ℝ | 0 < r}), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ {r : ℝ | 0 < r}), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ {r : ℝ | 0 < r}), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ {r : ℝ | 0 < r}), ((a + b) + (c + d)) > 0 := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4
  have proof_fact_1_1 : (0 : ℝ) < a := by
    have proof_fact_2_1 : a ∈ {r : ℝ | 0 < r} := litex_param_fact_1
    simpa using proof_fact_2_1
  have proof_fact_1_2 : (0 : ℝ) < b := by
    have proof_fact_3_1 : b ∈ {r : ℝ | 0 < r} := litex_param_fact_2
    simpa using proof_fact_3_1
  have proof_fact_1_3 : (0 : ℝ) < c := by
    have proof_fact_4_1 : c ∈ {r : ℝ | 0 < r} := litex_param_fact_3
    simpa using proof_fact_4_1
  have proof_fact_1_4 : (0 : ℝ) < d := by
    have proof_fact_5_1 : d ∈ {r : ℝ | 0 < r} := litex_param_fact_4
    simpa using proof_fact_5_1
  have well_defined_fact_1 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_2 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_3 : (c : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_4 : (d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_5 : (a + b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have well_defined_fact_6 : (c + d : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses well_defined_fact_1
  have well_defined_fact_8 : ((a + b) + (c + d) : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 9 reuses well_defined_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses well_defined_fact_3
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  -- Litex well-definedness certificate 13 reuses well_defined_fact_5
  -- Litex well-definedness certificate 14 reuses well_defined_fact_6
  -- Litex well-definedness certificate 15 reuses well_defined_fact_1
  -- Litex well-definedness certificate 16 reuses well_defined_fact_8
  -- Litex well-definedness certificate 17 reuses well_defined_fact_1
  -- Litex well-definedness certificate 18 reuses well_defined_fact_2
  -- Litex well-definedness certificate 19 reuses well_defined_fact_3
  -- Litex well-definedness certificate 20 reuses well_defined_fact_4
  -- Litex well-definedness certificate 21 reuses well_defined_fact_5
  -- Litex well-definedness certificate 22 reuses well_defined_fact_6
  -- Litex well-definedness certificate 23 reuses well_defined_fact_1
  -- Litex well-definedness certificate 24 reuses well_defined_fact_8
  have proof_fact_1_5 : (0 : ℝ) < (a + b) := by
    have proof_fact_6_1 : a ∈ (Set.univ : Set ℝ) := by
      have proof_fact_7_1 : a ∈ {r : ℝ | 0 < r} := by
        exact litex_param_fact_1
      exact Set.mem_univ _
    have proof_fact_6_2 : b ∈ (Set.univ : Set ℝ) := by
      have proof_fact_8_1 : b ∈ {r : ℝ | 0 < r} := by
        exact litex_param_fact_2
      exact Set.mem_univ _
    have proof_fact_6_3 : (0 : ℝ) < a := by
      exact proof_fact_1_1
    have proof_fact_6_4 : (0 : ℝ) < b := by
      exact proof_fact_1_2
    exact _root_.Litex.BuiltinRules.order_add_positive a b proof_fact_6_1 proof_fact_6_2 proof_fact_6_3 proof_fact_6_4
  have proof_fact_1_6 : (0 : ℝ) ≤ (c + d) := by
    have proof_fact_9_1 : (0 : ℝ) ≤ c := by
      have proof_fact_10_1 : 0 ∈ (Set.univ : Set ℝ) := by
        change True
        trivial
      have proof_fact_10_2 : c ∈ (Set.univ : Set ℝ) := by
        have proof_fact_11_1 : c ∈ {r : ℝ | 0 < r} := by
          exact litex_param_fact_3
        exact Set.mem_univ _
      have proof_fact_10_3 : (0 : ℝ) < c := by
        exact proof_fact_1_3
      exact _root_.Litex.BuiltinRules.order_less_equal_of_less 0 c proof_fact_10_1 proof_fact_10_2 proof_fact_10_3
    have proof_fact_9_2 : (0 : ℝ) ≤ d := by
      have proof_fact_12_1 : 0 ∈ (Set.univ : Set ℝ) := by
        change True
        trivial
      have proof_fact_12_2 : d ∈ (Set.univ : Set ℝ) := by
        have proof_fact_13_1 : d ∈ {r : ℝ | 0 < r} := by
          exact litex_param_fact_4
        exact Set.mem_univ _
      have proof_fact_12_3 : (0 : ℝ) < d := by
        exact proof_fact_1_4
      exact _root_.Litex.BuiltinRules.order_less_equal_of_less 0 d proof_fact_12_1 proof_fact_12_2 proof_fact_12_3
    have proof_fact_9_3 : (0 : ℝ) ≤ (c + d) := by
      linarith only [proof_fact_9_1, proof_fact_9_2]
    exact proof_fact_9_3
  have proof_fact_1_7 : ((a + b) + (c + d)) > 0 := by
    linarith only [proof_fact_1_5, proof_fact_1_6]
  exact proof_fact_1_7

end
```

## native_sets

```litex
# General set parameters share one implicit element carrier and become native
# `Set α` values. These operations preserve their source argument order.

forall A, B set:
    union(A, B) = union(A, B)

forall A, B set:
    intersect(A, B) = intersect(A, B)

forall A, B set:
    set_minus(A, B) = set_minus(A, B)

R = R
Q = Q

# Binder-owning set builders remain a separate unsupported Obj-IR boundary.
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f10
theorem fact10 : ∀ {α : Type u} [LitexObject α], ∀ (A : Set α), ∀ (B : Set α), (A ∪ B) = (A ∪ B) := by
  intro _ _ A B
  rfl

-- Litex fact f20
theorem fact20 : ∀ {α2 : Type u} [LitexObject α2], ∀ (A : Set α2), ∀ (B : Set α2), (A ∩ B) = (A ∩ B) := by
  intro _ _ A B
  rfl

-- Litex fact f30
theorem fact30 : ∀ {α4 : Type u} [LitexObject α4], ∀ (A : Set α4), ∀ (B : Set α4), (A \ B) = (A \ B) := by
  intro _ _ A B
  rfl

-- Litex fact f31
theorem fact31 : (Set.univ : Set ℝ) = (Set.univ : Set ℝ) := by
  rfl

-- Litex fact f32
theorem fact32 : (Set.univ : Set ℚ) = (Set.univ : Set ℚ) := by
  rfl

end
```

## native_set_builtins

```litex
# Native `Set` equalities, membership introduction, elementary subset laws,
# and nonzero multiplication retain the verifier's selected zero-, one-, and
# two-premise builtin route.

forall A, B set:
    union(A, B) = union(B, A)

forall A set:
    union(A, A) = A

forall A set:
    union(A, {}) = A

forall A, B set:
    intersect(A, B) = intersect(B, A)

# Bind `x` in A rather than declaring it as another generic set. This keeps
# the target carrier as `A : Set α`, `x : α`, and its membership premise is
# still an ordinary Litex fact.
forall A, B set, x A:
    x $in union(A, B)

forall A, B set, x A:
    x $in B
    =>:
        x $in intersect(A, B)

forall A, B set, x A:
    not x $in B
    =>:
        x $in set_minus(A, B)

forall A, B set:
    intersect(A, B) $subset A

forall A, B set:
    intersect(A, B) $subset B

forall A, B set:
    A $subset union(A, B)

forall A, B set:
    B $subset union(A, B)

forall A, B set:
    set_minus(A, B) $subset A

forall a, b R:
    a != 0
    b != 0
    =>:
        a * b != 0

forall A, B, S set:
    A $subset S
    B $subset S
    =>:
        union(A, B) $subset S

forall A set:
    {} $subset A

forall a, b R:
    min(a, b) <= a

forall a, b R:
    min(a, b) <= b

forall a, b R:
    a <= max(a, b)

forall a, b R:
    b <= max(a, b)

forall a, b R:
    a <= b
    =>:
        min(a, b) = a

forall a, b R:
    a <= b
    =>:
        max(a, b) = b

forall a, b R:
    b <= a
    =>:
        min(a, b) = b

forall a, b R:
    b <= a
    =>:
        max(a, b) = a

forall a, b R:
    min(a, b) = min(b, a)

forall a, b R:
    max(a, b) = max(b, a)

forall a, b, c R:
    min(min(a, b), c) = min(a, min(b, c))

forall a, b, c R:
    max(max(a, b), c) = max(a, max(b, c))

forall a R:
    min(a, a) = a

forall a R:
    max(a, a) = a

forall a, b R:
    min(a, max(a, b)) = a

forall a, b R:
    max(a, min(a, b)) = a

forall a, b, c, d R:
    a <= c
    b <= d
    =>:
        min(a, b) <= min(c, d)

forall a, b, c, d R:
    a <= c
    b <= d
    =>:
        max(a, b) <= max(c, d)

forall A, B set:
    A $subset B
    =>:
        intersect(A, B) = A

forall A, B set:
    B $subset A
    =>:
        intersect(A, B) = B

forall A, B set:
    B $subset A
    =>:
        set_minus(A, set_minus(A, B)) = B

forall A, B set:
    B $subset A
    =>:
        B = set_minus(A, set_minus(A, B))

forall A, B set:
    $is_nonempty_set(A)
    =>:
        $is_nonempty_set(union(A, B))

forall A, B set:
    $is_nonempty_set(B)
    =>:
        $is_nonempty_set(union(A, B))

forall A, B set:
    $is_finite_set(A)
    $is_finite_set(B)
    =>:
        $is_finite_set(union(A, B))

forall A, B set:
    $is_finite_set(A)
    $is_finite_set(B)
    =>:
        $is_finite_set(intersect(A, B))

forall A, B set:
    $is_finite_set(A)
    =>:
        $is_finite_set(set_minus(A, B))

forall A set:
    $is_nonempty_set(power_set(A))

forall A set:
    $is_finite_set(A)
    =>:
        $is_finite_set(power_set(A))

forall A, B set:
    A $subset B
    =>:
        A $in power_set(B)

forall X, S set:
    not $is_finite_set(X)
    $is_finite_set(S)
    =>:
        not $is_finite_set(set_minus(X, S))

forall x R:
    0 <= x
    =>:
        abs(x) = x

forall x R:
    x != 0
    =>:
        0 < abs(x)

$is_nonempty_set(N)
$is_nonempty_set(Z)
$is_nonempty_set(Q)
$is_nonempty_set(R)
$is_nonempty_set(C)
```

```lean
import Mathlib

namespace Litex.BuiltinRules

theorem nonzero_mul
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (ha : a ≠ 0)
    (hb : b ≠ 0) : a * b ≠ 0 := by
  exact mul_ne_zero ha hb

theorem order_abs_eq_self_of_nonnegative
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (hx : 0 ≤ x) : |x| = x := by
  exact abs_of_nonneg hx

theorem order_abs_positive_of_nonzero
    (x : ℝ)
    (_hxR : x ∈ (Set.univ : Set ℝ))
    (hx : x ≠ 0) : 0 < |x| := by
  exact abs_pos.mpr hx

theorem order_le_max_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : a ≤ max a b := by
  exact le_max_left a b

theorem order_le_max_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : b ≤ max a b := by
  exact le_max_right a b

theorem order_max_absorb_min_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : max a (min a b) = a := by
  exact max_eq_left (min_le_left a b)

theorem order_max_associative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ)) :
    max (max a b) c = max a (max b c) := by
  exact max_assoc a b c

theorem order_max_commutative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : max a b = max b a := by
  exact max_comm a b

theorem order_max_eq_left_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : b ≤ a) : max a b = a := by
  exact max_eq_left h

theorem order_max_eq_right_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a ≤ b) : max a b = b := by
  exact max_eq_right h

theorem order_max_idempotent
    (a : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ)) : max a a = a := by
  exact max_self a

theorem order_max_monotone
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hac : a ≤ c)
    (hbd : b ≤ d) : max a b ≤ max c d := by
  exact max_le_max hac hbd

theorem order_min_absorb_max_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a (max a b) = a := by
  exact min_eq_left (le_max_left a b)

theorem order_min_associative
    (a b c : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ)) :
    min (min a b) c = min a (min b c) := by
  exact min_assoc a b c

theorem order_min_commutative
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a b = min b a := by
  exact min_comm a b

theorem order_min_eq_left_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : a ≤ b) : min a b = a := by
  exact min_eq_left h

theorem order_min_eq_right_of_le
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (h : b ≤ a) : min a b = b := by
  exact min_eq_right h

theorem order_min_idempotent
    (a : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ)) : min a a = a := by
  exact min_self a

theorem order_min_le_left
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a b ≤ a := by
  exact min_le_left a b

theorem order_min_le_right
    (a b : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ)) : min a b ≤ b := by
  exact min_le_right a b

theorem order_min_monotone
    (a b c d : ℝ)
    (_haR : a ∈ (Set.univ : Set ℝ))
    (_hbR : b ∈ (Set.univ : Set ℝ))
    (_hcR : c ∈ (Set.univ : Set ℝ))
    (_hdR : d ∈ (Set.univ : Set ℝ))
    (hac : a ≤ c)
    (hbd : b ≤ d) : min a b ≤ min c d := by
  exact min_le_min hac hbd

theorem set_empty_subset
    {α : Type*}
    (A : Set α)
    (_hA : True) : (∅ : Set α) ⊆ A := by
  exact Set.empty_subset A

theorem set_intersect_commutative
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B = B ∩ A := by
  exact Set.inter_comm A B

theorem set_intersect_eq_left_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : A ⊆ B) : A ∩ B = A := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨hx, h hx⟩

theorem set_intersect_eq_right_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : A ∩ B = B := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hx
    exact ⟨h hx, hx⟩

theorem set_intersect_finite
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite)
    (_hBFinite : B.Finite) : (A ∩ B).Finite := by
  apply hA.subset
  intro x hx
  exact hx.1

theorem set_intersect_membership
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxA : x ∈ A)
    (hxB : x ∈ B) : x ∈ A ∩ B := by
  exact ⟨hxA, hxB⟩

theorem set_intersect_subset_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

theorem set_intersect_subset_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∩ B ⊆ B := by
  intro x hx
  exact hx.2

theorem set_power_set_finite
    {α : Type*}
    (A : Set α)
    (_hA : True)
    (hA : A.Finite) : (Set.powerset A).Finite := by
  exact hA.powerset

theorem set_power_set_membership_of_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : A ⊆ B) : A ∈ Set.powerset B := by
  exact h

theorem set_power_set_nonempty
    {α : Type*}
    (A : Set α)
    (_hA : True) : (Set.powerset A).Nonempty := by
  refine ⟨∅, ?_⟩
  exact Set.empty_subset A

theorem set_set_minus_finite_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite) : (A \ B).Finite := by
  apply hA.subset
  intro x hx
  exact hx.1

theorem set_set_minus_infinite_of_infinite_finite
    {α : Type*}
    (X S : Set α)
    (_hX : True)
    (_hS : True)
    (hX : ¬ X.Finite)
    (hS : S.Finite) : ¬ (X \ S).Finite := by
  classical
  intro hDifference
  apply hX
  apply (hDifference.union hS).subset
  intro x hxX
  by_cases hxS : x ∈ S
  · exact Or.inr hxS
  · exact Or.inl ⟨hxX, hxS⟩

theorem set_set_minus_membership
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxA : x ∈ A)
    (hxB : x ∉ B) : x ∈ A \ B := by
  exact ⟨hxA, hxB⟩

theorem set_set_minus_recover_subset
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : A \ (A \ B) = B := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxB
    exact hx.2 ⟨hx.1, hxB⟩
  · intro hxB
    exact ⟨h hxB, fun hxAB => hxAB.2 hxB⟩

theorem set_set_minus_subset_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A \ B ⊆ A := by
  intro x hx
  exact hx.1

theorem set_subset_eq_set_minus_recovery
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (h : B ⊆ A) : B = A \ (A \ B) := by
  classical
  ext x
  constructor
  · intro hxB
    exact ⟨h hxB, fun hxAB => hxAB.2 hxB⟩
  · intro hx
    by_contra hxB
    exact hx.2 ⟨hx.1, hxB⟩

theorem set_subset_union_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx

theorem set_subset_union_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : B ⊆ A ∪ B := by
  intro x hx
  exact Or.inr hx

theorem set_union_commutative
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True) : A ∪ B = B ∪ A := by
  exact Set.union_comm A B

theorem set_union_empty_right
    {α : Type*}
    (A : Set α)
    (_hA : True) : A ∪ ∅ = A := by
  exact Set.union_empty A

theorem set_union_finite
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Finite)
    (hB : B.Finite) : (A ∪ B).Finite := by
  exact hA.union hB

theorem set_union_idempotent
    {α : Type*}
    (A : Set α)
    (_hA : True) : A ∪ A = A := by
  exact Set.union_self A

theorem set_union_membership_left
    {α : Type*}
    (A B : Set α)
    (x : α)
    (_hA : True)
    (_hB : True)
    (hxA : x ∈ A) : x ∈ A ∪ B := by
  exact Set.mem_union_left B hxA

theorem set_union_nonempty_left
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hA : A.Nonempty) : (A ∪ B).Nonempty := by
  rcases hA with ⟨x, hx⟩
  exact ⟨x, Set.mem_union_left B hx⟩

theorem set_union_nonempty_right
    {α : Type*}
    (A B : Set α)
    (_hA : True)
    (_hB : True)
    (hB : B.Nonempty) : (A ∪ B).Nonempty := by
  rcases hB with ⟨x, hx⟩
  exact ⟨x, Set.mem_union_right A hx⟩

theorem set_union_subset
    {α : Type*}
    (A B S : Set α)
    (_hA : True)
    (_hB : True)
    (_hS : True)
    (hA : A ⊆ S)
    (hB : B ⊆ S) : A ∪ B ⊆ S := by
  exact Set.union_subset hA hB

end Litex.BuiltinRules

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f10
theorem fact10 : ∀ {α : Type u} [LitexObject α], ∀ (A : Set α), ∀ (B : Set α), (A ∪ B) = (B ∪ A) := by
  intro _ _ A B
  have proof_fact_1_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_1_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_union_commutative A B proof_fact_1_1 proof_fact_1_2

-- Litex fact f17
theorem fact17 : ∀ {α2 : Type u} [LitexObject α2], ∀ (A : Set α2), (A ∪ A) = A := by
  intro _ _ A
  have proof_fact_2_1 : litexIsSet A := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_union_idempotent A proof_fact_2_1

-- Litex fact f24
theorem fact24 : ∀ {α3 : Type u} [LitexObject α3], ∀ (A : Set α3), (A ∪ ∅) = A := by
  intro _ _ A
  have proof_fact_3_1 : litexIsSet A := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_union_empty_right A proof_fact_3_1

-- Litex fact f34
theorem fact34 : ∀ {α4 : Type u} [LitexObject α4], ∀ (A : Set α4), ∀ (B : Set α4), (A ∩ B) = (B ∩ A) := by
  intro _ _ A B
  have proof_fact_4_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_4_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_intersect_commutative A B proof_fact_4_1 proof_fact_4_2

-- Litex fact f50
theorem fact50 : ∀ {α6 : Type u} [LitexObject α6], ∀ (A : Set α6), ∀ (B : Set α6), ∀ (x : α6) (litex_param_fact_3 : x ∈ A), x ∈ (A ∪ B) := by
  intro _ _ A B x litex_param_fact_3
  have proof_fact_5_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_5_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_5_3 : x ∈ A := by
    exact litex_param_fact_3
  exact _root_.Litex.BuiltinRules.set_union_membership_left A B x proof_fact_5_1 proof_fact_5_2 proof_fact_5_3

-- Litex fact f66
theorem fact66 : ∀ {α9 : Type u} [LitexObject α9], ∀ (A : Set α9), ∀ (B : Set α9), ∀ (x : α9) (litex_param_fact_3 : x ∈ A), ∀ (litex_domain_fact_1 : x ∈ B), x ∈ (A ∩ B) := by
  intro _ _ A B x litex_param_fact_3 litex_domain_fact_1
  have proof_fact_6_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_6_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_6_3 : x ∈ A := by
    exact litex_param_fact_3
  have proof_fact_6_4 : x ∈ B := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_intersect_membership A B x proof_fact_6_1 proof_fact_6_2 proof_fact_6_3 proof_fact_6_4

-- Litex fact f82
theorem fact82 : ∀ {α12 : Type u} [LitexObject α12], ∀ (A : Set α12), ∀ (B : Set α12), ∀ (x : α12) (litex_param_fact_3 : x ∈ A), ∀ (litex_domain_fact_1 : x ∉ B), x ∈ (A \ B) := by
  intro _ _ A B x litex_param_fact_3 litex_domain_fact_1
  have proof_fact_7_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_7_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_7_3 : x ∈ A := by
    exact litex_param_fact_3
  have proof_fact_7_4 : x ∉ B := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_set_minus_membership A B x proof_fact_7_1 proof_fact_7_2 proof_fact_7_3 proof_fact_7_4

-- Litex fact f104
theorem fact104 : ∀ {α15 : Type u} [LitexObject α15], ∀ (A : Set α15), ∀ (B : Set α15), (A ∩ B) ⊆ A := by
  intro _ _ A B
  have proof_fact_8_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_8_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_intersect_subset_left A B proof_fact_8_1 proof_fact_8_2

-- Litex fact f126
theorem fact126 : ∀ {α20 : Type u} [LitexObject α20], ∀ (A : Set α20), ∀ (B : Set α20), (A ∩ B) ⊆ B := by
  intro _ _ A B
  have proof_fact_9_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_9_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_intersect_subset_right A B proof_fact_9_1 proof_fact_9_2

-- Litex fact f148
theorem fact148 : ∀ {α25 : Type u} [LitexObject α25], ∀ (A : Set α25), ∀ (B : Set α25), A ⊆ (A ∪ B) := by
  intro _ _ A B
  have proof_fact_10_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_10_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_subset_union_left A B proof_fact_10_1 proof_fact_10_2

-- Litex fact f170
theorem fact170 : ∀ {α30 : Type u} [LitexObject α30], ∀ (A : Set α30), ∀ (B : Set α30), B ⊆ (A ∪ B) := by
  intro _ _ A B
  have proof_fact_11_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_11_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_subset_union_right A B proof_fact_11_1 proof_fact_11_2

-- Litex fact f192
theorem fact192 : ∀ {α35 : Type u} [LitexObject α35], ∀ (A : Set α35), ∀ (B : Set α35), (A \ B) ⊆ A := by
  intro _ _ A B
  have proof_fact_12_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_12_2 : litexIsSet B := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_set_minus_subset_left A B proof_fact_12_1 proof_fact_12_2

-- Litex fact f208
theorem fact208 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≠ 0), ∀ (litex_domain_fact_2 : b ≠ 0), (a * b) ≠ 0 := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  have well_defined_fact_2 : (a : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses litex_param_fact_2
  have well_defined_fact_4 : (b : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses well_defined_fact_2
  -- Litex well-definedness certificate 7 reuses litex_param_fact_2
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses well_defined_fact_2
  -- Litex well-definedness certificate 11 reuses litex_param_fact_2
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  have proof_fact_13_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_13_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_13_3 : a ≠ 0 := by
    exact litex_domain_fact_1
  have proof_fact_13_4 : b ≠ 0 := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.nonzero_mul a b proof_fact_13_1 proof_fact_13_2 proof_fact_13_3 proof_fact_13_4

-- Litex fact f257
theorem fact257 : ∀ {α42 : Type u} [LitexObject α42], ∀ (A : Set α42), ∀ (B : Set α42), ∀ (S : Set α42), ∀ (litex_domain_fact_1 : A ⊆ S), ∀ (litex_domain_fact_2 : B ⊆ S), (A ∪ B) ⊆ S := by
  intro _ _ A B S litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_14_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_14_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_14_3 : litexIsSet S := by
    exact (by trivial)
  have proof_fact_14_4 : A ⊆ S := by
    exact litex_domain_fact_1
  have proof_fact_14_5 : B ⊆ S := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.set_union_subset A B S proof_fact_14_1 proof_fact_14_2 proof_fact_14_3 proof_fact_14_4 proof_fact_14_5

-- Litex fact f273
theorem fact273 : ∀ {α54 : Type u} [LitexObject α54], ∀ (A : Set α54), ∅ ⊆ A := by
  intro _ _ A
  have proof_fact_15_1 : litexIsSet A := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_empty_subset A proof_fact_15_1

-- Litex fact f283
theorem fact283 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (min a b) ≤ a := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_16_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_16_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_min_le_left a b proof_fact_16_1 proof_fact_16_2

-- Litex fact f293
theorem fact293 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (min a b) ≤ b := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_17_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_17_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_min_le_right a b proof_fact_17_1 proof_fact_17_2

-- Litex fact f303
theorem fact303 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), a ≤ (max a b) := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_18_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_18_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_le_max_left a b proof_fact_18_1 proof_fact_18_2

-- Litex fact f313
theorem fact313 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), b ≤ (max a b) := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_19_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_19_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_le_max_right a b proof_fact_19_1 proof_fact_19_2

-- Litex fact f326
theorem fact326 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), (min a b) = a := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_20_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_20_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_20_3 : a ≤ b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_min_eq_left_of_le a b proof_fact_20_1 proof_fact_20_2 proof_fact_20_3

-- Litex fact f339
theorem fact339 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ b), (max a b) = b := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_21_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_21_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_21_3 : a ≤ b := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_max_eq_right_of_le a b proof_fact_21_1 proof_fact_21_2 proof_fact_21_3

-- Litex fact f352
theorem fact352 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : b ≤ a), (min a b) = b := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_22_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_22_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_22_3 : b ≤ a := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_min_eq_right_of_le a b proof_fact_22_1 proof_fact_22_2 proof_fact_22_3

-- Litex fact f365
theorem fact365 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : b ≤ a), (max a b) = a := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_23_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_23_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_23_3 : b ≤ a := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_max_eq_left_of_le a b proof_fact_23_1 proof_fact_23_2 proof_fact_23_3

-- Litex fact f375
theorem fact375 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (min a b) = (min b a) := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_24_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_24_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_min_commutative a b proof_fact_24_1 proof_fact_24_2

-- Litex fact f385
theorem fact385 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (max a b) = (max b a) := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  -- Litex well-definedness certificate 4 reuses litex_param_fact_2
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  have proof_fact_25_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_25_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_max_commutative a b proof_fact_25_1 proof_fact_25_2

-- Litex fact f398
theorem fact398 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), (min (min a b) c) = (min a (min b c)) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  have well_defined_fact_3 : (min a b) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_3
  have well_defined_fact_5 : (min b c) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 6 reuses litex_param_fact_1
  -- Litex well-definedness certificate 7 reuses litex_param_fact_2
  -- Litex well-definedness certificate 8 reuses well_defined_fact_3
  -- Litex well-definedness certificate 9 reuses litex_param_fact_3
  -- Litex well-definedness certificate 10 reuses well_defined_fact_5
  -- Litex well-definedness certificate 11 reuses litex_param_fact_1
  -- Litex well-definedness certificate 12 reuses litex_param_fact_2
  -- Litex well-definedness certificate 13 reuses well_defined_fact_3
  -- Litex well-definedness certificate 14 reuses litex_param_fact_3
  -- Litex well-definedness certificate 15 reuses well_defined_fact_5
  have proof_fact_26_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_26_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_26_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  exact _root_.Litex.BuiltinRules.order_min_associative a b c proof_fact_26_1 proof_fact_26_2 proof_fact_26_3

-- Litex fact f411
theorem fact411 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), (max (max a b) c) = (max a (max b c)) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  have well_defined_fact_3 : (max a b) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_3
  have well_defined_fact_5 : (max b c) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 6 reuses litex_param_fact_1
  -- Litex well-definedness certificate 7 reuses litex_param_fact_2
  -- Litex well-definedness certificate 8 reuses well_defined_fact_3
  -- Litex well-definedness certificate 9 reuses litex_param_fact_3
  -- Litex well-definedness certificate 10 reuses well_defined_fact_5
  -- Litex well-definedness certificate 11 reuses litex_param_fact_1
  -- Litex well-definedness certificate 12 reuses litex_param_fact_2
  -- Litex well-definedness certificate 13 reuses well_defined_fact_3
  -- Litex well-definedness certificate 14 reuses litex_param_fact_3
  -- Litex well-definedness certificate 15 reuses well_defined_fact_5
  have proof_fact_27_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_27_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_27_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  exact _root_.Litex.BuiltinRules.order_max_associative a b c proof_fact_27_1 proof_fact_27_2 proof_fact_27_3

-- Litex fact f418
theorem fact418 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), (min a a) = a := by
  intro a litex_param_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_1
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have proof_fact_28_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  exact _root_.Litex.BuiltinRules.order_min_idempotent a proof_fact_28_1

-- Litex fact f425
theorem fact425 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), (max a a) = a := by
  intro a litex_param_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_1
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have proof_fact_29_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  exact _root_.Litex.BuiltinRules.order_max_idempotent a proof_fact_29_1

-- Litex fact f435
theorem fact435 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (min a (max a b)) = a := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  have well_defined_fact_3 : (max a b) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_1
  -- Litex well-definedness certificate 5 reuses litex_param_fact_2
  -- Litex well-definedness certificate 6 reuses well_defined_fact_3
  -- Litex well-definedness certificate 7 reuses litex_param_fact_1
  -- Litex well-definedness certificate 8 reuses litex_param_fact_2
  -- Litex well-definedness certificate 9 reuses well_defined_fact_3
  have proof_fact_30_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_30_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_min_absorb_max_left a b proof_fact_30_1 proof_fact_30_2

-- Litex fact f445
theorem fact445 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), (max a (min a b)) = a := by
  intro a litex_param_fact_1 b litex_param_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  have well_defined_fact_3 : (min a b) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 4 reuses litex_param_fact_1
  -- Litex well-definedness certificate 5 reuses litex_param_fact_2
  -- Litex well-definedness certificate 6 reuses well_defined_fact_3
  -- Litex well-definedness certificate 7 reuses litex_param_fact_1
  -- Litex well-definedness certificate 8 reuses litex_param_fact_2
  -- Litex well-definedness certificate 9 reuses well_defined_fact_3
  have proof_fact_31_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_31_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  exact _root_.Litex.BuiltinRules.order_max_absorb_min_left a b proof_fact_31_1 proof_fact_31_2

-- Litex fact f467
theorem fact467 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ c), ∀ (litex_domain_fact_2 : b ≤ d), (min a b) ≤ (min c d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_3
  -- Litex well-definedness certificate 4 reuses litex_param_fact_4
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  -- Litex well-definedness certificate 7 reuses litex_param_fact_3
  -- Litex well-definedness certificate 8 reuses litex_param_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses litex_param_fact_2
  -- Litex well-definedness certificate 11 reuses litex_param_fact_3
  -- Litex well-definedness certificate 12 reuses litex_param_fact_4
  have proof_fact_32_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_32_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_32_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_32_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_32_5 : a ≤ c := by
    exact litex_domain_fact_1
  have proof_fact_32_6 : b ≤ d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_min_monotone a b c d proof_fact_32_1 proof_fact_32_2 proof_fact_32_3 proof_fact_32_4 proof_fact_32_5 proof_fact_32_6

-- Litex fact f489
theorem fact489 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (c : ℝ) (litex_param_fact_3 : c ∈ (Set.univ : Set ℝ)), ∀ (d : ℝ) (litex_param_fact_4 : d ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : a ≤ c), ∀ (litex_domain_fact_2 : b ≤ d), (max a b) ≤ (max c d) := by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 d litex_param_fact_4 litex_domain_fact_1 litex_domain_fact_2
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_2
  -- Litex well-definedness certificate 3 reuses litex_param_fact_3
  -- Litex well-definedness certificate 4 reuses litex_param_fact_4
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_param_fact_2
  -- Litex well-definedness certificate 7 reuses litex_param_fact_3
  -- Litex well-definedness certificate 8 reuses litex_param_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses litex_param_fact_2
  -- Litex well-definedness certificate 11 reuses litex_param_fact_3
  -- Litex well-definedness certificate 12 reuses litex_param_fact_4
  have proof_fact_33_1 : a ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_33_2 : b ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_2
  have proof_fact_33_3 : c ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_3
  have proof_fact_33_4 : d ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_4
  have proof_fact_33_5 : a ≤ c := by
    exact litex_domain_fact_1
  have proof_fact_33_6 : b ≤ d := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.order_max_monotone a b c d proof_fact_33_1 proof_fact_33_2 proof_fact_33_3 proof_fact_33_4 proof_fact_33_5 proof_fact_33_6

-- Litex fact f511
theorem fact511 : ∀ {α98 : Type u} [LitexObject α98], ∀ (A : Set α98), ∀ (B : Set α98), ∀ (litex_domain_fact_1 : A ⊆ B), (A ∩ B) = A := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_34_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_34_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_34_3 : A ⊆ B := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_intersect_eq_left_of_subset A B proof_fact_34_1 proof_fact_34_2 proof_fact_34_3

-- Litex fact f533
theorem fact533 : ∀ {α103 : Type u} [LitexObject α103], ∀ (A : Set α103), ∀ (B : Set α103), ∀ (litex_domain_fact_1 : B ⊆ A), (A ∩ B) = B := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_35_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_35_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_35_3 : B ⊆ A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_intersect_eq_right_of_subset A B proof_fact_35_1 proof_fact_35_2 proof_fact_35_3

-- Litex fact f555
theorem fact555 : ∀ {α108 : Type u} [LitexObject α108], ∀ (A : Set α108), ∀ (B : Set α108), ∀ (litex_domain_fact_1 : B ⊆ A), (A \ (A \ B)) = B := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_36_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_36_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_36_3 : B ⊆ A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_set_minus_recover_subset A B proof_fact_36_1 proof_fact_36_2 proof_fact_36_3

-- Litex fact f577
theorem fact577 : ∀ {α113 : Type u} [LitexObject α113], ∀ (A : Set α113), ∀ (B : Set α113), ∀ (litex_domain_fact_1 : B ⊆ A), B = (A \ (A \ B)) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_37_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_37_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_37_3 : B ⊆ A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_subset_eq_set_minus_recovery A B proof_fact_37_1 proof_fact_37_2 proof_fact_37_3

-- Litex fact f590
theorem fact590 : ∀ {α118 : Type u} [LitexObject α118], ∀ (A : Set α118), ∀ (B : Set α118), ∀ (litex_domain_fact_1 : litexIsNonemptySet A), litexIsNonemptySet (A ∪ B) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_38_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_38_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_38_3 : litexIsNonemptySet A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_union_nonempty_left A B proof_fact_38_1 proof_fact_38_2 proof_fact_38_3

-- Litex fact f603
theorem fact603 : ∀ {α120 : Type u} [LitexObject α120], ∀ (A : Set α120), ∀ (B : Set α120), ∀ (litex_domain_fact_1 : litexIsNonemptySet B), litexIsNonemptySet (A ∪ B) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_39_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_39_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_39_3 : litexIsNonemptySet B := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_union_nonempty_right A B proof_fact_39_1 proof_fact_39_2 proof_fact_39_3

-- Litex fact f619
theorem fact619 : ∀ {α122 : Type u} [LitexObject α122], ∀ (A : Set α122), ∀ (B : Set α122), ∀ (litex_domain_fact_1 : litexIsFiniteSet A), ∀ (litex_domain_fact_2 : litexIsFiniteSet B), litexIsFiniteSet (A ∪ B) := by
  intro _ _ A B litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_40_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_40_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_40_3 : litexIsFiniteSet A := by
    exact litex_domain_fact_1
  have proof_fact_40_4 : litexIsFiniteSet B := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.set_union_finite A B proof_fact_40_1 proof_fact_40_2 proof_fact_40_3 proof_fact_40_4

-- Litex fact f635
theorem fact635 : ∀ {α124 : Type u} [LitexObject α124], ∀ (A : Set α124), ∀ (B : Set α124), ∀ (litex_domain_fact_1 : litexIsFiniteSet A), ∀ (litex_domain_fact_2 : litexIsFiniteSet B), litexIsFiniteSet (A ∩ B) := by
  intro _ _ A B litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_41_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_41_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_41_3 : litexIsFiniteSet A := by
    exact litex_domain_fact_1
  have proof_fact_41_4 : litexIsFiniteSet B := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.set_intersect_finite A B proof_fact_41_1 proof_fact_41_2 proof_fact_41_3 proof_fact_41_4

-- Litex fact f648
theorem fact648 : ∀ {α126 : Type u} [LitexObject α126], ∀ (A : Set α126), ∀ (B : Set α126), ∀ (litex_domain_fact_1 : litexIsFiniteSet A), litexIsFiniteSet (A \ B) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_42_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_42_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_42_3 : litexIsFiniteSet A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_set_minus_finite_left A B proof_fact_42_1 proof_fact_42_2 proof_fact_42_3

-- Litex fact f655
theorem fact655 : ∀ {α128 : Type u} [LitexObject α128], ∀ (A : Set α128), litexIsNonemptySet (Set.powerset A) := by
  intro _ _ A
  have proof_fact_43_1 : litexIsSet A := by
    exact (by trivial)
  exact _root_.Litex.BuiltinRules.set_power_set_nonempty A proof_fact_43_1

-- Litex fact f665
theorem fact665 : ∀ {α129 : Type u} [LitexObject α129], ∀ (A : Set α129), ∀ (litex_domain_fact_1 : litexIsFiniteSet A), litexIsFiniteSet (Set.powerset A) := by
  intro _ _ A litex_domain_fact_1
  have proof_fact_44_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_44_2 : litexIsFiniteSet A := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_power_set_finite A proof_fact_44_1 proof_fact_44_2

-- Litex fact f693
theorem fact693 : ∀ {α130 : Type u} [LitexObject α130], ∀ (A : Set α130), ∀ (B : Set α130), ∀ (litex_domain_fact_1 : A ⊆ B), A ∈ (Set.powerset B) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_45_1 : litexIsSet A := by
    exact (by trivial)
  have proof_fact_45_2 : litexIsSet B := by
    exact (by trivial)
  have proof_fact_45_3 : A ⊆ B := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.set_power_set_membership_of_subset A B proof_fact_45_1 proof_fact_45_2 proof_fact_45_3

-- Litex fact f709
theorem fact709 : ∀ {α138 : Type u} [LitexObject α138], ∀ (X : Set α138), ∀ (S : Set α138), ∀ (litex_domain_fact_1 : ¬ litexIsFiniteSet X), ∀ (litex_domain_fact_2 : litexIsFiniteSet S), ¬ litexIsFiniteSet (X \ S) := by
  intro _ _ X S litex_domain_fact_1 litex_domain_fact_2
  have proof_fact_46_1 : litexIsSet X := by
    exact (by trivial)
  have proof_fact_46_2 : litexIsSet S := by
    exact (by trivial)
  have proof_fact_46_3 : ¬ litexIsFiniteSet X := by
    exact litex_domain_fact_1
  have proof_fact_46_4 : litexIsFiniteSet S := by
    exact litex_domain_fact_2
  exact _root_.Litex.BuiltinRules.set_set_minus_infinite_of_infinite_finite X S proof_fact_46_1 proof_fact_46_2 proof_fact_46_3 proof_fact_46_4

-- Litex fact f719
theorem fact719 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : (0 : ℝ) ≤ x), (abs x) = x := by
  intro x litex_param_fact_1 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_1
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have proof_fact_47_1 : x ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_47_2 : (0 : ℝ) ≤ x := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_abs_eq_self_of_nonnegative x proof_fact_47_1 proof_fact_47_2

-- Litex fact f729
theorem fact729 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : x ≠ 0), (0 : ℝ) < (abs x) := by
  intro x litex_param_fact_1 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_param_fact_1
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have proof_fact_48_1 : x ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  have proof_fact_48_2 : x ≠ 0 := by
    exact litex_domain_fact_1
  exact _root_.Litex.BuiltinRules.order_abs_positive_of_nonzero x proof_fact_48_1 proof_fact_48_2

-- Litex fact f730
theorem fact730 : litexIsNonemptySet (Set.univ : Set ℕ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f731
theorem fact731 : litexIsNonemptySet (Set.univ : Set ℤ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f732
theorem fact732 : litexIsNonemptySet (Set.univ : Set ℚ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f733
theorem fact733 : litexIsNonemptySet (Set.univ : Set ℝ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f734
theorem fact734 : litexIsNonemptySet (Set.univ : Set ℂ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

end
```

## standard_numeric_subsets

```litex
# Tracer: compact standard numeric subsets use native Mathlib sets.
#
# Before (not part of the strict compiler contract):
# forall r R+:
#     r $in R+
# Former limitation: compact-subset renderer branches existed, but no durable
# strict example or real Mathlib gate established this source-to-target ABI.
#
# Now (verified):
forall r R+:
    r $in R+
# Current behavior: R+ binds an `ℝ` value and retains membership in
# `{r : ℝ | 0 < r}` as an ordinary proposition.
#
# Z+ is Litex's canonical alias of N+, so both target positive naturals.
forall n N+:
    n $in N+

Z+ = N+

forall q Q+:
    q $in Q+

forall z Z-:
    z $in Z-

forall q Q-:
    q $in Q-

forall r R-:
    r $in R-

forall z Z*:
    z $in Z*

forall q Q*:
    q $in Q*

forall r R*:
    r $in R*

forall c C*:
    c $in C*

# Standard numeric membership uses one checked projection rule backed by the
# centralized Litex subset hierarchy. It retains the exact source membership;
# target-carrier casts exist only in the generated Lean fact occurrence.
forall n N+:
    n $in N

forall z Z-:
    z $in Z

forall z Z*:
    z $in Z

forall q Q+:
    q $in Q

forall q Q-:
    q $in Q

forall q Q*:
    q $in Q

forall r R+:
    r $in R

forall r R-:
    r $in R

forall r R*:
    r $in R

forall c C*:
    c $in C

# Before, cross-carrier membership reached a label-only builtin result and the
# strict compiler rejected it as OtherUnsupported. The same projection
# certificate now covers the native tower and refined cross-carrier cases.
forall n N:
    n $in Z

forall z Z:
    z $in Q

forall q Q:
    q $in R

forall r R:
    r $in C

forall q Q+:
    q $in R+

forall z Z*:
    z $in C*

forall n N+:
    n $in C*

forall z Z-:
    z $in C*

# Closed numeric memberships use checked reflection rather than trust.
1 $in N+
1 $in Q+
2 $in R+
0 - 1 $in Z-
0 - 1 $in Q-
0 - 1 $in R-
1 $in Z*
1 $in Q*
1 $in R*
1 $in C*
not 0 $in N+
not 0 $in Q+
not 0 $in R+
not 0 $in Z-
not 0 $in Q-
not 0 $in R-
not 0 $in Z*
not 0 $in Q*
not 0 $in R*
not 0 $in C*

# Boundaries: C+ is intentionally not a Litex standard set because complex
# numbers have no canonical order. Direct heterogeneous set propositions such
# as `N $subset Z` remain unsupported until their Lean meaning is chosen; this
# batch only compiles an object's membership projection.
# Evidence: cargo test --release compact_standard_numeric_subsets -- --nocapture
# and cargo test --release closed_compact_numeric_memberships -- --nocapture
# Ledger gate: cargo test --release compile_to_lean_examples_markdown_emits_checked_source -- --nocapture
# Implementation: src/obj/standard_set.rs,
# src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs,
# src/litex_to_lean_ir/builtin_rule.rs, and src/compile_to_lean/pipeline.rs.
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f7
theorem fact7 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | 0 < r}), r ∈ {r : ℝ | 0 < r} := by
  intro r litex_param_fact_1
  have proof_fact_1_1 : 0 < r := by
    have proof_fact_2_1 : r ∈ {r : ℝ | 0 < r} := litex_param_fact_1
    simpa using proof_fact_2_1
  exact litex_param_fact_1

-- Litex fact f14
theorem fact14 : ∀ (n : ℕ) (litex_param_fact_1 : n ∈ {n : ℕ | 0 < n}), n ∈ {n : ℕ | 0 < n} := by
  intro n litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f15
theorem fact15 : {n : ℕ | 0 < n} = {n : ℕ | 0 < n} := by
  rfl

-- Litex fact f22
theorem fact22 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | 0 < q}), q ∈ {q : ℚ | 0 < q} := by
  intro q litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f35
theorem fact35 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z < 0}), z ∈ {z : ℤ | z < 0} := by
  intro z litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f48
theorem fact48 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | q < 0}), q ∈ {q : ℚ | q < 0} := by
  intro q litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f61
theorem fact61 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | r < 0}), r ∈ {r : ℝ | r < 0} := by
  intro r litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f68
theorem fact68 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z ≠ 0}), z ∈ {z : ℤ | z ≠ 0} := by
  intro z litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f75
theorem fact75 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | q ≠ 0}), q ∈ {q : ℚ | q ≠ 0} := by
  intro q litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f82
theorem fact82 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | r ≠ 0}), r ∈ {r : ℝ | r ≠ 0} := by
  intro r litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f89
theorem fact89 : ∀ (c : ℂ) (litex_param_fact_1 : c ∈ {c : ℂ | c ≠ 0}), c ∈ {c : ℂ | c ≠ 0} := by
  intro c litex_param_fact_1
  exact litex_param_fact_1

-- Litex fact f105
theorem fact105 : ∀ (n : ℕ) (litex_param_fact_1 : n ∈ {n : ℕ | 0 < n}), n ∈ (Set.univ : Set ℕ) := by
  intro n litex_param_fact_1
  have proof_fact_3_1 : n ∈ {n : ℕ | 0 < n} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f121
theorem fact121 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z < 0}), z ∈ (Set.univ : Set ℤ) := by
  intro z litex_param_fact_1
  have proof_fact_4_1 : z ∈ {z : ℤ | z < 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f131
theorem fact131 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z ≠ 0}), z ∈ (Set.univ : Set ℤ) := by
  intro z litex_param_fact_1
  have proof_fact_5_1 : z ∈ {z : ℤ | z ≠ 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f141
theorem fact141 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | 0 < q}), q ∈ (Set.univ : Set ℚ) := by
  intro q litex_param_fact_1
  have proof_fact_6_1 : q ∈ {q : ℚ | 0 < q} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f157
theorem fact157 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | q < 0}), q ∈ (Set.univ : Set ℚ) := by
  intro q litex_param_fact_1
  have proof_fact_7_1 : q ∈ {q : ℚ | q < 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f167
theorem fact167 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | q ≠ 0}), q ∈ (Set.univ : Set ℚ) := by
  intro q litex_param_fact_1
  have proof_fact_8_1 : q ∈ {q : ℚ | q ≠ 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f177
theorem fact177 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | 0 < r}), r ∈ (Set.univ : Set ℝ) := by
  intro r litex_param_fact_1
  have proof_fact_9_1 : 0 < r := by
    have proof_fact_10_1 : r ∈ {r : ℝ | 0 < r} := litex_param_fact_1
    simpa using proof_fact_10_1
  have proof_fact_9_2 : r ∈ {r : ℝ | 0 < r} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f193
theorem fact193 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | r < 0}), r ∈ (Set.univ : Set ℝ) := by
  intro r litex_param_fact_1
  have proof_fact_11_1 : r ∈ {r : ℝ | r < 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f203
theorem fact203 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ {r : ℝ | r ≠ 0}), r ∈ (Set.univ : Set ℝ) := by
  intro r litex_param_fact_1
  have proof_fact_12_1 : r ∈ {r : ℝ | r ≠ 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f213
theorem fact213 : ∀ (c : ℂ) (litex_param_fact_1 : c ∈ {c : ℂ | c ≠ 0}), c ∈ (Set.univ : Set ℂ) := by
  intro c litex_param_fact_1
  have proof_fact_13_1 : c ∈ {c : ℂ | c ≠ 0} := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f226
theorem fact226 : ∀ (n : ℕ) (litex_param_fact_1 : n ∈ (Set.univ : Set ℕ)), (n : ℤ) ∈ (Set.univ : Set ℤ) := by
  intro n litex_param_fact_1
  have proof_fact_14_1 : n ∈ (Set.univ : Set ℕ) := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f233
theorem fact233 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ (Set.univ : Set ℤ)), (z : ℚ) ∈ (Set.univ : Set ℚ) := by
  intro z litex_param_fact_1
  have proof_fact_15_1 : z ∈ (Set.univ : Set ℤ) := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f240
theorem fact240 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ (Set.univ : Set ℚ)), (q : ℝ) ∈ (Set.univ : Set ℝ) := by
  intro q litex_param_fact_1
  have proof_fact_16_1 : q ∈ (Set.univ : Set ℚ) := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f247
theorem fact247 : ∀ (r : ℝ) (litex_param_fact_1 : r ∈ (Set.univ : Set ℝ)), (r : ℂ) ∈ (Set.univ : Set ℂ) := by
  intro r litex_param_fact_1
  have proof_fact_17_1 : r ∈ (Set.univ : Set ℝ) := by
    exact litex_param_fact_1
  exact Set.mem_univ _

-- Litex fact f257
theorem fact257 : ∀ (q : ℚ) (litex_param_fact_1 : q ∈ {q : ℚ | 0 < q}), (q : ℝ) ∈ {r : ℝ | 0 < r} := by
  intro q litex_param_fact_1
  have proof_fact_18_1 : q ∈ {q : ℚ | 0 < q} := by
    exact litex_param_fact_1
  have proof_fact_18_2 : 0 < (q : ℚ) := by
    simpa using proof_fact_18_1
  change 0 < (q : ℝ)
  exact_mod_cast proof_fact_18_2

-- Litex fact f267
theorem fact267 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z ≠ 0}), (z : ℂ) ∈ {c : ℂ | c ≠ 0} := by
  intro z litex_param_fact_1
  have proof_fact_19_1 : z ∈ {z : ℤ | z ≠ 0} := by
    exact litex_param_fact_1
  have proof_fact_19_2 : (z : ℤ) ≠ 0 := by
    simpa using proof_fact_19_1
  change (z : ℂ) ≠ 0
  exact_mod_cast proof_fact_19_2

-- Litex fact f280
theorem fact280 : ∀ (n : ℕ) (litex_param_fact_1 : n ∈ {n : ℕ | 0 < n}), (n : ℂ) ∈ {c : ℂ | c ≠ 0} := by
  intro n litex_param_fact_1
  have proof_fact_20_1 : n ∈ {n : ℕ | 0 < n} := by
    exact litex_param_fact_1
  have proof_fact_20_2 : 0 < (n : ℕ) := by
    simpa using proof_fact_20_1
  have proof_fact_20_3 := ne_of_gt proof_fact_20_2
  change (n : ℂ) ≠ 0
  exact_mod_cast proof_fact_20_3

-- Litex fact f299
theorem fact299 : ∀ (z : ℤ) (litex_param_fact_1 : z ∈ {z : ℤ | z < 0}), (z : ℂ) ∈ {c : ℂ | c ≠ 0} := by
  intro z litex_param_fact_1
  have proof_fact_21_1 : z ∈ {z : ℤ | z < 0} := by
    exact litex_param_fact_1
  have proof_fact_21_2 : (z : ℤ) < 0 := by
    simpa using proof_fact_21_1
  have proof_fact_21_3 := ne_of_lt proof_fact_21_2
  change (z : ℂ) ≠ 0
  exact_mod_cast proof_fact_21_3

-- Litex fact f300
theorem fact300 : 1 ∈ {n : ℕ | 0 < n} := by
  norm_num

-- Litex fact f301
theorem fact301 : (0 : ℕ) < 1 := by
  norm_num

-- Litex fact f302
theorem fact302 : 1 ∈ {q : ℚ | 0 < q} := by
  norm_num

-- Litex fact f303
theorem fact303 : 2 ∈ {r : ℝ | 0 < r} := by
  norm_num

-- Litex fact f304
theorem fact304 : (0 : ℝ) < 2 := by
  have proof_fact_22_1 : 2 ∈ {r : ℝ | 0 < r} := fact303
  simpa using proof_fact_22_1

-- Litex well-definedness certificate 1
theorem well_defined_fact_1 : 0 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_2 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f305
theorem fact305 : (0 - 1) ∈ {z : ℤ | z < 0} := by
  norm_num

-- Litex fact f306
theorem fact306 : (0 - 1 : ℤ) < 0 := by
  norm_num

-- Litex well-definedness certificate 1
theorem well_defined_fact_3 : 0 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_4 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f308
theorem fact308 : (0 - 1) ∈ {q : ℚ | q < 0} := by
  norm_num

-- Litex well-definedness certificate 1
theorem well_defined_fact_5 : 0 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_6 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f309
theorem fact309 : (0 - 1) ∈ {r : ℝ | r < 0} := by
  norm_num

-- Litex fact f310
theorem fact310 : 1 ∈ {z : ℤ | z ≠ 0} := by
  norm_num

-- Litex fact f311
theorem fact311 : (1 : ℤ) ≠ 0 := by
  norm_num

-- Litex fact f312
theorem fact312 : 1 ∈ {q : ℚ | q ≠ 0} := by
  norm_num

-- Litex fact f313
theorem fact313 : 1 ∈ {r : ℝ | r ≠ 0} := by
  norm_num

-- Litex fact f314
theorem fact314 : 1 ∈ {c : ℂ | c ≠ 0} := by
  norm_num

-- Litex fact f315
theorem fact315 : 0 ∉ {n : ℕ | 0 < n} := by
  norm_num

-- Litex fact f316
theorem fact316 : 0 ∉ {q : ℚ | 0 < q} := by
  norm_num

-- Litex fact f317
theorem fact317 : 0 ∉ {r : ℝ | 0 < r} := by
  norm_num

-- Litex fact f318
theorem fact318 : 0 ∉ {z : ℤ | z < 0} := by
  norm_num

-- Litex fact f319
theorem fact319 : 0 ∉ {q : ℚ | q < 0} := by
  norm_num

-- Litex fact f320
theorem fact320 : 0 ∉ {r : ℝ | r < 0} := by
  norm_num

-- Litex fact f321
theorem fact321 : 0 ∉ {z : ℤ | z ≠ 0} := by
  norm_num

-- Litex fact f322
theorem fact322 : 0 ∉ {q : ℚ | q ≠ 0} := by
  norm_num

-- Litex fact f323
theorem fact323 : 0 ∉ {r : ℝ | r ≠ 0} := by
  norm_num

-- Litex fact f324
theorem fact324 : 0 ∉ {c : ℂ | c ≠ 0} := by
  norm_num

end
```

## builtin_predicates

```litex
# Tracer: native builtin propositions with selected checked proof routes.
#
# Before (Litex verified, strict Litex-to-Lean rejected):
# $prime(53)
# forall A, B set:
#     A $subset B
#     =>:
#         B $superset A
# Former behavior: `$prime` had no native Lean predicate, `$superset` and
# proper relations had no proposition lowering, and duality lost its premise.
#
# Now (strict Litex-to-Lean): closed prime facts use `Nat.Prime` plus checked
# reflection; subset/superset duality retains its one checked child; proper
# relations and negated comparisons use native propositions.

$prime(53)
not $prime(54)

forall A, B set:
    A $subset B
    =>:
        B $superset A

forall A, B set:
    A $superset B
    =>:
        B $subset A

forall A, B set:
    not A $subset B
    =>:
        not B $superset A

forall A, B set:
    not A $superset B
    =>:
        not B $subset A

forall A, B set:
    A $proper_subset B
    =>:
        A $proper_subset B

forall A, B set:
    not A $proper_subset B
    =>:
        not A $proper_subset B

forall A, B set:
    A $proper_superset B
    =>:
        A $proper_superset B

forall A, B set:
    not A $proper_superset B
    =>:
        not A $proper_superset B

forall a, b R:
    not a < b
    =>:
        not a < b

forall a, b R:
    not a <= b
    =>:
        not a <= b

forall a, b R:
    not a > b
    =>:
        not a > b

forall a, b R:
    not a >= b
    =>:
        not a >= b

# Boundary: `by def A $proper_subset B` and the function/cartesian builtin
# families still need their own proof/object ABI; this tracer does not claim
# those routes.
# Evidence: cargo test --release compile_to_lean_examples_markdown_emits_checked_source -- --nocapture
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex well-definedness certificate 1
theorem well_defined_fact_1 : 2 ∈ (Set.univ : Set ℤ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_2 : 53 ∈ (Set.univ : Set ℤ) := by
  change True
  trivial

-- Litex well-definedness certificate 4
theorem well_defined_fact_3 : ∀ (_binder_0 : ℤ), (_binder_0 : ℝ) ∈ (Set.univ : Set ℝ) := by
  intro _binder_0
  change True
  trivial

-- Litex well-definedness certificate 5
theorem well_defined_fact_4 : 0 ∈ (Set.univ : Set ℝ) := by
  change True
  trivial

-- Litex well-definedness certificate 6 (generalized local premise)
theorem well_defined_fact_5 : ∀ (_binder_0 : ℤ), 0 < _binder_0 → _binder_0 > 0 := by
  intro _binder_0 litex_wd_source
  exact litex_wd_source

-- Litex well-definedness certificate 7 (generalized strict-order premise)
theorem well_defined_fact_6 : ∀ (_binder_0 : ℤ), _binder_0 > 0 → _binder_0 ≠ 0 := by
  intro _binder_0 litex_strict_order litex_equal
  rw [litex_equal] at litex_strict_order
  exact (lt_irrefl _ litex_strict_order)

-- Litex fact f1
theorem fact1 : Nat.Prime 53 := by
  norm_num

-- Litex fact f10
theorem fact10 : ¬ Nat.Prime 54 := by
  norm_num

-- Litex fact f38
theorem fact38 : ∀ {α1 : Type u} [LitexObject α1], ∀ (A : Set α1), ∀ (B : Set α1), ∀ (litex_domain_fact_1 : A ⊆ B), A ⊆ B := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_1_1 : A ⊆ B := by
    exact litex_domain_fact_1
  exact proof_fact_1_1

-- Litex fact f66
theorem fact66 : ∀ {α9 : Type u} [LitexObject α9], ∀ (A : Set α9), ∀ (B : Set α9), ∀ (litex_domain_fact_1 : B ⊆ A), B ⊆ A := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_2_1 : B ⊆ A := by
    exact litex_domain_fact_1
  exact proof_fact_2_1

-- Litex fact f79
theorem fact79 : ∀ {α17 : Type u} [LitexObject α17], ∀ (A : Set α17), ∀ (B : Set α17), ∀ (litex_domain_fact_1 : ¬ (A ⊆ B)), ¬ (A ⊆ B) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_3_1 : ¬ (A ⊆ B) := by
    exact litex_domain_fact_1
  exact proof_fact_3_1

-- Litex fact f92
theorem fact92 : ∀ {α19 : Type u} [LitexObject α19], ∀ (A : Set α19), ∀ (B : Set α19), ∀ (litex_domain_fact_1 : ¬ (B ⊆ A)), ¬ (B ⊆ A) := by
  intro _ _ A B litex_domain_fact_1
  have proof_fact_4_1 : ¬ (B ⊆ A) := by
    exact litex_domain_fact_1
  exact proof_fact_4_1

-- Litex fact f117
theorem fact117 : ∀ {α21 : Type u} [LitexObject α21], ∀ (A : Set α21), ∀ (B : Set α21), ∀ (litex_domain_fact_1 : (A ⊆ B) ∧ A ≠ B), (A ⊆ B) ∧ A ≠ B := by
  intro _ _ A B litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f127
theorem fact127 : ∀ {α26 : Type u} [LitexObject α26], ∀ (A : Set α26), ∀ (B : Set α26), ∀ (litex_domain_fact_1 : ¬ (A ⊆ B) ∨ A = B), ¬ (A ⊆ B) ∨ A = B := by
  intro _ _ A B litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f152
theorem fact152 : ∀ {α28 : Type u} [LitexObject α28], ∀ (A : Set α28), ∀ (B : Set α28), ∀ (litex_domain_fact_1 : (B ⊆ A) ∧ A ≠ B), (B ⊆ A) ∧ A ≠ B := by
  intro _ _ A B litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f162
theorem fact162 : ∀ {α33 : Type u} [LitexObject α33], ∀ (A : Set α33), ∀ (B : Set α33), ∀ (litex_domain_fact_1 : ¬ (B ⊆ A) ∨ A = B), ¬ (B ⊆ A) ∨ A = B := by
  intro _ _ A B litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f172
theorem fact172 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : ¬ (a < b)), ¬ (a < b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f182
theorem fact182 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : ¬ (a ≤ b)), ¬ (a ≤ b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f192
theorem fact192 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : ¬ (a > b)), ¬ (a > b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

-- Litex fact f202
theorem fact202 : ∀ (a : ℝ) (litex_param_fact_1 : a ∈ (Set.univ : Set ℝ)), ∀ (b : ℝ) (litex_param_fact_2 : b ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : ¬ (a ≥ b)), ¬ (a ≥ b) := by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

end
```

## choice

```litex
# A checked nonemptiness proof selects a value from the real carrier. The same
# certificate supplies the selected value and its membership theorem.

have demo_chosen_real R
demo_chosen_real $in R

# Choice also remains local inside a generated contradiction proof.
by contra:
    ? demo_chosen_real = demo_chosen_real
    have demo_local_choice R
    demo_local_choice $in R
    impossible demo_chosen_real != demo_chosen_real
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex checked choice source for `demo_chosen_real`
theorem litex_choice_source_1 : litexIsNonemptySet (Set.univ : Set ℝ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

noncomputable def demo_chosen_real : ℝ := Exists.choose litex_choice_source_1

-- Litex fact f3
theorem fact3 : demo_chosen_real ∈ (Set.univ : Set ℝ) := by
  exact Exists.choose_spec litex_choice_source_1

-- Litex fact f8
theorem fact8 : demo_chosen_real = demo_chosen_real := by
  classical
  apply Classical.byContradiction
  intro proof_fact_1_1
  have proof_fact_1_2 : litexIsNonemptySet (Set.univ : Set ℝ) := by
    refine ⟨0, ?_⟩
    exact Set.mem_univ 0
  let demo_local_choice : ℝ := Exists.choose proof_fact_1_2
  have proof_fact_1_3 : demo_local_choice ∈ (Set.univ : Set ℝ) := by
    exact Exists.choose_spec proof_fact_1_2
  have proof_fact_1_4 : demo_local_choice ∈ (Set.univ : Set ℝ) := proof_fact_1_3
  have proof_fact_1_5 : demo_chosen_real ≠ demo_chosen_real := proof_fact_1_1
  have proof_fact_1_6 : demo_chosen_real = demo_chosen_real := by
    rfl
  exact False.elim (proof_fact_1_5 proof_fact_1_6)

end
```

## existentials

```litex
# Existential introduction retains checked witness types and direct body facts.
witness exist demo_source R st {demo_source = 1, demo_source = demo_source} from 1:
    1 = 1
    1 = 1

# Explicit extraction projects the chosen witness and both body facts.
obtain demo_selected from exist demo_source R st {demo_source = 1, demo_source = demo_source}

# Body-style `have` uses the same checked existential-elimination route.
have demo_shorthand R:
    demo_shorthand = 1
    demo_shorthand = demo_shorthand

# Multiple witnesses become nested Lean `Exists` packages in source order.
witness exist demo_left, demo_right R st {demo_left = 1, demo_right = 2} from 1, 2:
    1 = 1
    2 = 2

obtain demo_chosen_left, demo_chosen_right from exist demo_left, demo_right R st {demo_left = 1, demo_right = 2}
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex fact f10
theorem fact10 : ∃ demo_source : ℝ, demo_source ∈ (Set.univ : Set ℝ) ∧ (demo_source = 1) ∧ demo_source = demo_source := by
  have proof_fact_1_1 : (1 : ℝ) = 1 := by
    rfl
  have proof_fact_1_2 : (1 : ℝ) = 1 := proof_fact_1_1
  have proof_fact_1_3 : 1 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have proof_fact_1_4 : (1 : ℝ) = 1 := by
    norm_num
  have proof_fact_1_5 : (1 : ℝ) = 1 := by
    norm_num
  exact ⟨(1 : ℝ), proof_fact_1_3, proof_fact_1_4, proof_fact_1_5⟩

-- Litex checked existential source for `demo_selected`
theorem litex_exist_source_2 : ∃ demo_source : ℝ, demo_source ∈ (Set.univ : Set ℝ) ∧ (demo_source = 1) ∧ demo_source = demo_source := by
  exact fact10

noncomputable def demo_selected : ℝ := Exists.choose (litex_exist_source_2)

-- Litex fact f17
theorem fact17 : demo_selected ∈ (Set.univ : Set ℝ) := by
  exact (Exists.choose_spec (litex_exist_source_2)).1

-- Litex fact f18
theorem fact18 : demo_selected = 1 := by
  exact ((Exists.choose_spec (litex_exist_source_2)).2).1

-- Litex fact f19
theorem fact19 : demo_selected = demo_selected := by
  exact ((Exists.choose_spec (litex_exist_source_2)).2).2

-- Litex checked existential source for `demo_shorthand`
theorem litex_exist_source_4 : ∃ demo_shorthand : ℝ, demo_shorthand ∈ (Set.univ : Set ℝ) ∧ (demo_shorthand = 1) ∧ demo_shorthand = demo_shorthand := by
  exact fact10

noncomputable def demo_shorthand : ℝ := Exists.choose (litex_exist_source_4)

-- Litex fact f26
theorem fact26 : demo_shorthand ∈ (Set.univ : Set ℝ) := by
  exact (Exists.choose_spec (litex_exist_source_4)).1

-- Litex fact f27
theorem fact27 : demo_shorthand = 1 := by
  exact ((Exists.choose_spec (litex_exist_source_4)).2).1

-- Litex fact f28
theorem fact28 : demo_shorthand = demo_shorthand := by
  exact ((Exists.choose_spec (litex_exist_source_4)).2).2

-- Litex fact f43
theorem fact43 : ∃ demo_left : ℝ, demo_left ∈ (Set.univ : Set ℝ) ∧ ∃ demo_right : ℝ, demo_right ∈ (Set.univ : Set ℝ) ∧ (demo_left = 1) ∧ demo_right = 2 := by
  have proof_fact_2_1 : (1 : ℝ) = 1 := by
    rfl
  have proof_fact_2_2 : (2 : ℝ) = 2 := by
    rfl
  have proof_fact_2_3 : 1 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have proof_fact_2_4 : 2 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have proof_fact_2_5 : (1 : ℝ) = 1 := by
    norm_num
  have proof_fact_2_6 : (2 : ℝ) = 2 := by
    norm_num
  exact ⟨(1 : ℝ), proof_fact_2_3, (2 : ℝ), proof_fact_2_4, proof_fact_2_5, proof_fact_2_6⟩

-- Litex checked existential source for `demo_chosen_left`
theorem litex_exist_source_9 : ∃ demo_left : ℝ, demo_left ∈ (Set.univ : Set ℝ) ∧ ∃ demo_right : ℝ, demo_right ∈ (Set.univ : Set ℝ) ∧ (demo_left = 1) ∧ demo_right = 2 := by
  exact fact43

noncomputable def demo_chosen_left : ℝ := Exists.choose (litex_exist_source_9)

noncomputable def demo_chosen_right : ℝ := Exists.choose ((Exists.choose_spec (litex_exist_source_9)).2)

-- Litex fact f52
theorem fact52 : demo_chosen_left ∈ (Set.univ : Set ℝ) := by
  exact (Exists.choose_spec (litex_exist_source_9)).1

-- Litex fact f53
theorem fact53 : demo_chosen_right ∈ (Set.univ : Set ℝ) := by
  exact (Exists.choose_spec ((Exists.choose_spec (litex_exist_source_9)).2)).1

-- Litex fact f54
theorem fact54 : demo_chosen_left = 1 := by
  exact ((Exists.choose_spec ((Exists.choose_spec (litex_exist_source_9)).2)).2).1

-- Litex fact f55
theorem fact55 : demo_chosen_right = 2 := by
  exact ((Exists.choose_spec ((Exists.choose_spec (litex_exist_source_9)).2)).2).2

end
```

## atomic_fact_witness

```litex
# An atomic fact witness keeps the proposition call as the primary fact.
# Runtime resolves the current concrete definition only when this statement
# executes; the compiler consumes the frozen definition-introduction evidence.
prop divides(p Z, u Z):
    exist k Z st {p = u * k}

witness $divides(6, 2) from 3:
    6 = 2 * 3

$divides(6, 2)
obtain named_divisor from $divides(6, 2)
6 = 2 * named_divisor

# Boundary: v1 accepts exactly one positive plain `exist` definition clause;
# `exist!`, `not exist`, abstract props, and multi-clause definitions fail.
# Persistent tracer: examples/01_proof_patterns/witness_atomic_fact.lit
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

def divides (p : ℤ) (u : ℤ) : Prop := ∃ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ p = (u * k)

-- Litex fact f11
theorem fact11 : divides 6 2 := by
  have proof_fact_1_1 : ∃ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 6 = (2 * k) := by
    have proof_fact_2_1_wd_1 : 2 ∈ (Set.univ : Set ℂ) := by
      change True
      trivial
    have proof_fact_2_1_wd_2 : 3 ∈ (Set.univ : Set ℂ) := by
      change True
      trivial
    have proof_fact_2_2 : (6 : ℤ) = (2 * 3) := by
      -- native proof view, left fraction: (6 : ℝ) / (1 : ℝ)
      -- native proof view, right fraction: ((2 : ℝ) * (3 : ℝ)) / (1 : ℝ)
      norm_num
    have proof_fact_2_3 : 3 ∈ (Set.univ : Set ℤ) := by
      change True
      trivial
    have proof_fact_2_4 : (6 : ℤ) = (2 * 3) := by
      norm_num
    exact ⟨(3 : ℤ), proof_fact_2_3, proof_fact_2_4⟩
  simpa only [divides] using proof_fact_1_1

-- Litex fact f14
theorem fact14 : ∃ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 6 = (2 * k) := by
  have proof_fact_3_1 : divides 6 2 := fact11
  simpa only [divides] using proof_fact_3_1

-- Litex checked existential source for `named_divisor`
theorem litex_exist_source_4 : ∃ k : ℤ, k ∈ (Set.univ : Set ℤ) ∧ 6 = (2 * k) := by
  have proof_fact_4_1 : divides 6 2 := fact11
  simpa only [divides] using proof_fact_4_1

noncomputable def named_divisor : ℤ := Exists.choose (litex_exist_source_4)

-- Litex fact f17
theorem fact17 : named_divisor ∈ (Set.univ : Set ℤ) := by
  exact (Exists.choose_spec (litex_exist_source_4)).1

-- Litex fact f18
theorem fact18 : 6 = (2 * named_divisor) := by
  exact (Exists.choose_spec (litex_exist_source_4)).2

-- Litex well-definedness certificate 1
theorem well_defined_fact_1 : 2 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 2
theorem well_defined_fact_2 : (named_divisor : ℂ) ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

end
```

## obtain_from_existential_prop_definition

```litex
# A concrete prop with one existential clause can be eliminated directly.
prop has_copy(a R):
    exist x R st {x = a}

$has_copy(2)
obtain copy from $has_copy(2)
copy = 2
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

def has_copy (a : ℝ) : Prop := ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = a

-- Litex fact f5
theorem fact5 : has_copy 2 := by
  simp [has_copy]

-- Litex checked existential source for `copy`
theorem litex_exist_source_3 : ∃ x : ℝ, x ∈ (Set.univ : Set ℝ) ∧ x = 2 := by
  have proof_fact_1_1 : has_copy 2 := fact5
  simpa only [has_copy] using proof_fact_1_1

noncomputable def copy : ℝ := Exists.choose (litex_exist_source_3)

-- Litex fact f10
theorem fact10 : copy ∈ (Set.univ : Set ℝ) := by
  exact (Exists.choose_spec (litex_exist_source_3)).1

-- Litex fact f11
theorem fact11 : copy = 2 := by
  exact (Exists.choose_spec (litex_exist_source_3)).2

end
```

## proof_scopes

```litex
# File-scope and proof-local object definitions remain separate Lean scopes.
have demo_scope_value R = 2

by cases:
    ? demo_scope_value = demo_scope_value
    case demo_scope_value = 2:
        have demo_case_value R = 3
        demo_case_value = 3
    case demo_scope_value != 2:
        impossible demo_scope_value != 2

by contra:
    ? 2 = 2
    2 = 2
    impossible 2 != 2
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

def demo_scope_value : ℝ := 2

-- Litex fact f2
theorem fact2 : demo_scope_value ∈ (Set.univ : Set ℝ) := by
  have proof_fact_1_1 : 2 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  simpa only [demo_scope_value] using proof_fact_1_1

-- Litex fact f3
theorem fact3 : demo_scope_value = 2 := by
  rfl

-- Litex fact f9
theorem fact9 : demo_scope_value = demo_scope_value := by
  have proof_fact_2_1 : (demo_scope_value = 2 ∨ demo_scope_value ≠ 2) := by
    classical
    exact Classical.em (demo_scope_value = 2)
  rcases proof_fact_2_1 with proof_fact_3_1 | proof_fact_5_1
  · let demo_case_value : ℝ := 3
    have proof_fact_3_2 : demo_case_value ∈ (Set.univ : Set ℝ) := by
      have proof_fact_4_1 : 3 ∈ (Set.univ : Set ℝ) := by
        change True
        trivial
      simpa only [demo_case_value] using proof_fact_4_1
    have proof_fact_3_3 : demo_case_value = 3 := by
      rfl
    have proof_fact_3_4 : demo_case_value = 3 := proof_fact_3_3
    rfl
  · have proof_fact_5_2 : demo_scope_value ≠ 2 := proof_fact_5_1
    have proof_fact_5_3 : demo_scope_value = 2 := fact3
    exact False.elim (proof_fact_5_2 proof_fact_5_3)

-- Litex fact f12
theorem fact12 : 2 = 2 := by
  classical
  apply Classical.byContradiction
  intro proof_fact_6_1
  have proof_fact_6_2 : 2 = 2 := by
    rfl
  have proof_fact_6_3 : 2 ≠ 2 := proof_fact_6_1
  have proof_fact_6_4 : 2 = 2 := proof_fact_6_2
  exact False.elim (proof_fact_6_3 proof_fact_6_4)

end
```

## function_sets_and_well_definedness

```litex
# A named restricted function becomes one native dependent Lean function.
# Its later evaluation cites the exact checked defining equality, while all
# source-only and application well-definedness proofs remain explicit.

have fn reciprocal(x R: x != 0) R = 1 / x

forall x R:
    x != 0
    =>:
        reciprocal(x) = 1 / x
```

```lean
import Mathlib

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex checked function definition `reciprocal`
def reciprocal : (x : ℝ) → x ≠ 0 → ℝ := fun (x : ℝ) (litex_domain_fact_1 : x ≠ 0) => by
  have litex_param_fact_1 : x ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 1 reuses litex_domain_fact_1
  have litex_function_wd_0_2 : 1 ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have litex_function_wd_0_4 : (x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have litex_function_wd_0_5 : 1 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have litex_function_wd_0_6 : (1 / x) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 8 reuses litex_function_wd_0_2
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses litex_function_wd_0_4
  have litex_function_return_check_0 : (1 / x) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  exact (1 / x)

-- Litex fact f9
theorem fact9 : reciprocal ∈ (Set.univ : Set ((x : ℝ) → x ≠ 0 → ℝ)) := by
  change True
  trivial

-- Litex checked defining equality: #0#reciprocal = fn (#1#x R: #1#x != 0) R {1 / #1#x}
-- Litex fact f10
theorem fact10 : reciprocal = (fun (x : ℝ) (litex_domain_fact_1 : x ≠ 0) => by
  have litex_param_fact_1 : x ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 1 reuses litex_domain_fact_1
  have litex_function_wd_0_2 : 1 ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 3 reuses litex_param_fact_1
  have litex_function_wd_0_4 : (x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  have litex_function_wd_0_5 : 1 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have litex_function_wd_0_6 : (1 / x) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  -- Litex well-definedness certificate 7 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 8 reuses litex_function_wd_0_2
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses litex_function_wd_0_4
  have litex_function_return_check_0 : (1 / x) ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  exact (1 / x)) := by
  rfl

-- Litex well-definedness certificate 3 (forall type witness)
theorem well_defined_fact_1 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f23
theorem fact23 : ∀ (x : ℝ) (litex_param_fact_1 : x ∈ (Set.univ : Set ℝ)), ∀ (litex_domain_fact_1 : x ≠ 0), (reciprocal x litex_domain_fact_1) = (1 / x) := by
  intro x litex_param_fact_1 litex_domain_fact_1
  -- Litex well-definedness certificate 1 reuses litex_param_fact_1
  -- Litex well-definedness certificate 2 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 3 reuses well_defined_fact_1
  have well_defined_fact_4 : (x : ℂ) ∈ (Set.univ : Set ℂ) := by
    change True
    trivial
  -- Litex well-definedness certificate 5 reuses litex_param_fact_1
  -- Litex well-definedness certificate 6 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 7 reuses well_defined_fact_1
  -- Litex well-definedness certificate 8 reuses well_defined_fact_4
  -- Litex well-definedness certificate 9 reuses litex_param_fact_1
  -- Litex well-definedness certificate 10 reuses litex_domain_fact_1
  -- Litex well-definedness certificate 11 reuses well_defined_fact_1
  -- Litex well-definedness certificate 12 reuses well_defined_fact_4
  simpa only [reciprocal]

end
```

## carrier_boundaries

<!-- to-lean: partial -->

```litex
# These statements all verify in Litex. Report-mode Litex-to-Lean identifies the
# exact proof routes that are not yet checked by the strict Lean backend.

forall n N:
    n + 1 $in N

forall n N:
    n + 1 $in Z

forall z Z:
    z - 1 $in Z

forall z Z:
    z / 2 $in Q

forall z Z, q Q:
    z + q $in Q

forall z Z, q Q:
    z / 2 + q $in Q

forall n N+:
    n - 1 $in N

have boundary_natural_two N = 2
have boundary_integer_two Z = 2
have boundary_rational_half Q = 1 / 2
have boundary_complex_one C = 1

# Native target meanings are already fixed: N/Z/Q/C map to ℕ/ℤ/ℚ/ℂ.
# The missing pieces here are proof backends, not alternative carrier choices.
```

```lean
import Mathlib

-- Litex-to-Lean status: incomplete
-- Omitted statements: 11

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex-to-Lean omitted statement 1 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:4.
-- Statement: forall #0#n N: #0#n + 1 $in N
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "N: a + b from a in N and b in N" }

-- Litex-to-Lean omitted statement 2 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:7.
-- Statement: forall #1#n N: #1#n + 1 $in Z
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Z" }

-- Litex-to-Lean omitted statement 3 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:10.
-- Statement: forall #2#z Z: #2#z - 1 $in Z
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "Z closure: arithmetic operands in Z; pow base in Z and exponent in N, or base in N+ and exponent in N" }

-- Litex-to-Lean omitted statement 4 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:13.
-- Statement: forall #3#z Z: #3#z / 2 $in Q
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- Litex-to-Lean omitted statement 5 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:16.
-- Statement: forall #4#z Z, #5#q Q: #4#z + #5#q $in Q
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- Litex-to-Lean omitted statement 6 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:19.
-- Statement: forall #6#z Z, #7#q Q: #6#z / 2 + #7#q $in Q
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- Litex-to-Lean omitted statement 7 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:22.
-- Statement: forall #8#n N+: #8#n - 1 $in N
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "N: n - 1 from n in N+" }

-- Litex-to-Lean omitted statement 8 during IR construction at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:25.
-- Statement: have #10#boundary_natural_two N = 2
-- Reason: have-object equality inferred consequences are not represented by this Litex-to-Lean tranche

-- Litex-to-Lean omitted statement 9 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:26.
-- Statement: have #12#boundary_integer_two Z = 2
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "number in Z" }

-- Litex-to-Lean omitted statement 10 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:27.
-- Statement: have #14#boundary_rational_half Q = 1 / 2
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "number in Q" }

-- Litex-to-Lean omitted statement 11 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#carrier_boundaries:28.
-- Statement: have #16#boundary_complex_one C = 1
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "number in C" }

end
```

## partial_boundary

<!-- to-lean: partial -->

```litex
# All three statements verify in Litex. Report-mode Litex-to-Lean emits statements
# one and three, marks statement two unsupported, and returns Incomplete.

1 / 2 / 3 / 4 = 1 / 24
sin(0) = 0
1 / 3 + 2 / 3 = 1

# Strict Litex-to-Lean intentionally fails on the unsupported trigonometric proof;
# report mode never replaces it with `sorry`, an opaque constant, or an axiom.
```

```lean
import Mathlib

-- Litex-to-Lean status: incomplete
-- Omitted statements: 1

noncomputable section

universe u

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite

-- Litex well-definedness certificate 1
theorem well_defined_fact_1 : (2 : ℂ) ≠ 0 := by
  norm_num

-- Litex well-definedness certificate 2
theorem well_defined_fact_2 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 3
theorem well_defined_fact_3 : 2 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 4
theorem well_defined_fact_4 : (3 : ℂ) ≠ 0 := by
  norm_num

-- Litex well-definedness certificate 5
theorem well_defined_fact_5 : (1 / 2) ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 6
theorem well_defined_fact_6 : 3 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 7
theorem well_defined_fact_7 : (4 : ℂ) ≠ 0 := by
  norm_num

-- Litex well-definedness certificate 8
theorem well_defined_fact_8 : ((1 / 2) / 3) ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 9
theorem well_defined_fact_9 : 4 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 10
theorem well_defined_fact_10 : (24 : ℂ) ≠ 0 := by
  norm_num

-- Litex well-definedness certificate 11
theorem well_defined_fact_11 : 24 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f1
theorem fact1 : (((1 / 2) / 3) / 4 : ℚ) = (1 / 24) := by
  -- native proof view, left fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))
  -- native proof view, right fraction: (1 : ℝ) / (24 : ℝ)
  norm_num

-- Litex-to-Lean omitted statement 2 during Lean emission at examples/09_compile_to_lean/compile_to_lean_examples.md#partial_boundary:5.
-- Statement: sin(0) = 0
-- Reason: Litex-to-Lean has no checked backend for proof rule OtherUnsupported { name: "trigonometry layer 0: canonical expansion from core values at zero" }

-- Litex well-definedness certificate 1
theorem well_defined_fact_12 : (3 : ℂ) ≠ 0 := by
  norm_num

-- Litex well-definedness certificate 2
theorem well_defined_fact_13 : 1 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 3
theorem well_defined_fact_14 : 3 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 4
theorem well_defined_fact_15 : 2 ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 5
theorem well_defined_fact_16 : (1 / 3) ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex well-definedness certificate 6
theorem well_defined_fact_17 : (2 / 3) ∈ (Set.univ : Set ℂ) := by
  change True
  trivial

-- Litex fact f3
theorem fact3 : ((1 / 3) + (2 / 3) : ℚ) = 1 := by
  -- native proof view, left fraction: ((3 : ℝ) + ((2 : ℝ) * (3 : ℝ))) / ((3 : ℝ) * (3 : ℝ))
  -- native proof view, right fraction: (1 : ℝ) / (1 : ℝ)
  norm_num

end
```
