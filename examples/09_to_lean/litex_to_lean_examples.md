# Litex-to-Lean Examples

This is the default authoring ledger for small, self-contained To-Lean examples.
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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f1
theorem fact1 : 2 = 2 := by
  rfl

-- Litex fact f2
theorem fact2 : 2 ∈ (Set.univ : Set ℝ) := by
  change True
  trivial

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

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f7
theorem fact7 : ∀ x ∈ (Set.univ : Set ℝ), x = x := by
  intro x proof_fact_1_1
  rfl

-- Litex fact f14
theorem fact14 : ∀ z ∈ (Set.univ : Set ℤ), z = z := by
  intro z proof_fact_2_1
  rfl

-- Litex fact f21
theorem fact21 : ∀ q ∈ (Set.univ : Set ℚ), q = q := by
  intro q proof_fact_3_1
  rfl

-- Litex fact f28
theorem fact28 : ∀ x ∈ (Set.univ : Set ℝ), x ≠ 0 → x ≠ 0 := by
  intro x proof_fact_4_1 proof_fact_4_2
  exact proof_fact_4_2

-- Litex fact f44
theorem fact44 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ x ∈ (Set.univ : Set ℝ), x ≠ 0 → ((a + b) / x) = ((a / x) + (b / x)) := by
  intro a proof_fact_5_1 b proof_fact_5_2 x proof_fact_5_3 proof_fact_5_4
  -- native proof view, left fraction: (a + b) / x
  -- native proof view, right fraction: ((a * x) + (b * x)) / (x * x)
  field_simp [proof_fact_5_4] <;> ring

-- Litex fact f60
theorem fact60 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a ≠ 0 → b ≠ 0 → (a / b) ≠ 0 := by
  intro a proof_fact_6_1 b proof_fact_6_2 proof_fact_6_3 proof_fact_6_4
  have proof_fact_6_5 : a ≠ 0 := by
    exact proof_fact_6_3
  have proof_fact_6_6 : b ≠ 0 := by
    exact proof_fact_6_4
  have proof_fact_6_7 : (a / b) ≠ 0 := by
    exact div_ne_zero proof_fact_6_5 proof_fact_6_6
  exact proof_fact_6_7

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

# `trust 1 / 2 = 1 / 2` remains rejected by strict To-Lean because no judgment
# selects the division carrier.
```

```lean
import Mathlib

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

opaque demo_marked {α : Type LitexUniverse} [LitexObject α] : α → LitexFact

-- Litex trust boundary: f3
axiom fact3 : ∀ x ∈ (Set.univ : Set ℝ), demo_marked x

-- Litex fact f4
theorem fact4 : demo_marked (3 : ℝ) := by
  -- Litex parameter requirement for `x`: 3 : ℝ
  let proof_arg_1_1 : ℝ := 3
  have proof_fact_1_2 : 3 ∈ (Set.univ : Set ℝ) := by
    change True
    trivial
  have proof_fact_1_3 : demo_marked (3 : ℝ) := fact3 proof_arg_1_1 proof_fact_1_2
  exact proof_fact_1_3

def demo_is_one (x : ℝ) : LitexFact := x = 1

-- Litex fact f7
theorem fact7 : demo_is_one 1 := by
  simp [demo_is_one]

opaque demo_successor_pair {α : Type LitexUniverse} [LitexObject α] {α1 : Type LitexUniverse} [LitexObject α1] : α → α1 → LitexFact

-- Litex trust boundary: f12
axiom fact12 : ∀ x ∈ (Set.univ : Set ℝ), demo_successor_pair x (x + 1)

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
axiom fact15 : ∀ x ∈ (Set.univ : Set ℝ), x ∈ (Set.univ : Set ℝ)

-- Litex trust boundary: f18
axiom fact18 : ∀ z ∈ (Set.univ : Set ℤ), (z / 2 : ℚ) ∈ (Set.univ : Set ℚ)

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

opaque demo_transported {α : Type LitexUniverse} [LitexObject α] : α → LitexFact

-- Litex fact f16
theorem fact16 : ∀ {α1 : Type LitexUniverse} [LitexObject α1], ∀ (a : Set α1), ∀ (b : Set α1), demo_transported a → a = b → demo_transported b := by
  intro _ _ a b proof_fact_1_1 proof_fact_1_2
  have proof_fact_1_3 : demo_transported a := proof_fact_1_1
  have proof_fact_1_4 : a = b := proof_fact_1_2
  have proof_fact_1_5 : demo_transported b := by
    simpa only [proof_fact_1_4] using proof_fact_1_3
  exact proof_fact_1_5

opaque demo_related {α : Type LitexUniverse} [LitexObject α] {α1 : Type LitexUniverse} [LitexObject α1] : α → α1 → LitexFact

-- Litex fact f32
theorem fact32 : ∀ {α4 : Type LitexUniverse} [LitexObject α4], ∀ (a : Set α4), ∀ (b : Set α4), demo_related a b → a = b → demo_related b a := by
  intro _ _ a b proof_fact_2_1 proof_fact_2_2
  have proof_fact_2_3 : demo_related a b := proof_fact_2_1
  have proof_fact_2_4 : a = b := proof_fact_2_2
  have proof_fact_2_5 : demo_related b a := by
    simpa only [proof_fact_2_4] using proof_fact_2_3
  exact proof_fact_2_5

-- Litex fact f54
theorem fact54 : ∀ {α6 : Type LitexUniverse} [LitexObject α6], ∀ (a : Set α6), ∀ (b : Set α6), ∀ (c : Set α6), demo_transported c → a = b → b = c → demo_transported a := by
  intro _ _ a b c proof_fact_3_1 proof_fact_3_2 proof_fact_3_3
  have proof_fact_3_4 : demo_transported c := proof_fact_3_1
  have proof_fact_3_5 : b = c := proof_fact_3_3
  have proof_fact_3_6 : a = b := proof_fact_3_2
  have proof_fact_3_7 : demo_transported a := by
    simpa only [proof_fact_3_5, proof_fact_3_6] using proof_fact_3_4
  exact proof_fact_3_7

opaque demo_resolved {α : Type LitexUniverse} [LitexObject α] : α → LitexFact

-- Litex fact f73
theorem fact73 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a = 13 → b = 1 → demo_resolved (14 : ℝ) → demo_resolved (a + b) := by
  intro a proof_fact_4_1 b proof_fact_4_2 proof_fact_4_3 proof_fact_4_4 proof_fact_4_5
  have proof_fact_4_6 : demo_resolved (13 + 1 : ℝ) := by
    have proof_fact_5_1 : demo_resolved (14 : ℝ) := proof_fact_4_5
    have proof_fact_5_2 : demo_resolved (13 + 1 : ℝ) := by
      convert proof_fact_5_1 using 1 <;> norm_num
    exact proof_fact_5_2
  have proof_fact_4_7 : a = 13 := proof_fact_4_3
  have proof_fact_4_8 : b = 1 := proof_fact_4_4
  have proof_fact_4_9 : demo_resolved (a + b) := by
    simpa only [proof_fact_4_7, proof_fact_4_8] using proof_fact_4_6
  exact proof_fact_4_9

end
```

## builtin_arithmetic

```litex
# Twenty arithmetic and order facts whose successful verifier routes carry
# typed builtin evidence to Lean.

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

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f13
theorem fact13 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a < b → a ≤ b := by
  intro a proof_fact_1_1 b proof_fact_1_2 proof_fact_1_3
  have proof_fact_1_4 : a < b := by
    exact proof_fact_1_3
  have proof_fact_1_5 : a ≤ b := by
    linarith only [proof_fact_1_4]
  exact proof_fact_1_5

-- Litex fact f26
theorem fact26 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a > b → a ≥ b := by
  intro a proof_fact_2_1 b proof_fact_2_2 proof_fact_2_3
  have proof_fact_2_4 : a > b := by
    exact proof_fact_2_3
  have proof_fact_2_5 : a ≥ b := by
    linarith only [proof_fact_2_4]
  exact proof_fact_2_5

-- Litex fact f39
theorem fact39 : ∀ u ∈ (Set.univ : Set ℝ), ∀ v ∈ (Set.univ : Set ℝ), v ≤ u → (0 : ℝ) ≤ (u - v) := by
  intro u proof_fact_3_1 v proof_fact_3_2 proof_fact_3_3
  have proof_fact_3_4 : v ≤ u := by
    exact proof_fact_3_3
  have proof_fact_3_5 : (0 : ℝ) ≤ (u - v) := by
    linarith only [proof_fact_3_4]
  exact proof_fact_3_5

-- Litex fact f52
theorem fact52 : ∀ u ∈ (Set.univ : Set ℝ), ∀ v ∈ (Set.univ : Set ℝ), v < u → (0 : ℝ) < (u - v) := by
  intro u proof_fact_4_1 v proof_fact_4_2 proof_fact_4_3
  have proof_fact_4_4 : v < u := by
    exact proof_fact_4_3
  have proof_fact_4_5 : (0 : ℝ) < (u - v) := by
    linarith only [proof_fact_4_4]
  exact proof_fact_4_5

-- Litex fact f68
theorem fact68 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ (a + b) := by
  intro a proof_fact_5_1 b proof_fact_5_2 proof_fact_5_3 proof_fact_5_4
  have proof_fact_5_5 : 0 ≤ a := by
    exact proof_fact_5_3
  have proof_fact_5_6 : 0 ≤ b := by
    exact proof_fact_5_4
  have proof_fact_5_7 : 0 ≤ (a + b) := by
    linarith only [proof_fact_5_5, proof_fact_5_6]
  exact proof_fact_5_7

-- Litex fact f84
theorem fact84 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 < a → 0 < b → 0 < (a + b) := by
  intro a proof_fact_6_1 b proof_fact_6_2 proof_fact_6_3 proof_fact_6_4
  have proof_fact_6_5 : 0 < a := by
    exact proof_fact_6_3
  have proof_fact_6_6 : 0 < b := by
    exact proof_fact_6_4
  have proof_fact_6_7 : 0 < (a + b) := by
    linarith only [proof_fact_6_5, proof_fact_6_6]
  exact proof_fact_6_7

-- Litex fact f100
theorem fact100 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 < a → 0 ≤ b → 0 < (a + b) := by
  intro a proof_fact_7_1 b proof_fact_7_2 proof_fact_7_3 proof_fact_7_4
  have proof_fact_7_5 : 0 < a := by
    exact proof_fact_7_3
  have proof_fact_7_6 : 0 ≤ b := by
    exact proof_fact_7_4
  have proof_fact_7_7 : 0 < (a + b) := by
    linarith only [proof_fact_7_5, proof_fact_7_6]
  exact proof_fact_7_7

-- Litex fact f116
theorem fact116 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 ≤ a → 0 < b → 0 < (a + b) := by
  intro a proof_fact_8_1 b proof_fact_8_2 proof_fact_8_3 proof_fact_8_4
  have proof_fact_8_5 : 0 ≤ a := by
    exact proof_fact_8_3
  have proof_fact_8_6 : 0 < b := by
    exact proof_fact_8_4
  have proof_fact_8_7 : 0 < (a + b) := by
    linarith only [proof_fact_8_5, proof_fact_8_6]
  exact proof_fact_8_7

-- Litex fact f132
theorem fact132 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ (a * b) := by
  intro a proof_fact_9_1 b proof_fact_9_2 proof_fact_9_3 proof_fact_9_4
  have proof_fact_9_5 : 0 ≤ a := by
    exact proof_fact_9_3
  have proof_fact_9_6 : 0 ≤ b := by
    exact proof_fact_9_4
  have proof_fact_9_7 : 0 ≤ (a * b) := by
    exact mul_nonneg proof_fact_9_5 proof_fact_9_6
  exact proof_fact_9_7

-- Litex fact f148
theorem fact148 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 < a → 0 < b → 0 < (a * b) := by
  intro a proof_fact_10_1 b proof_fact_10_2 proof_fact_10_3 proof_fact_10_4
  have proof_fact_10_5 : 0 < a := by
    exact proof_fact_10_3
  have proof_fact_10_6 : 0 < b := by
    exact proof_fact_10_4
  have proof_fact_10_7 : 0 < (a * b) := by
    exact mul_pos proof_fact_10_5 proof_fact_10_6
  exact proof_fact_10_7

-- Litex fact f164
theorem fact164 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 ≤ a → 0 < b → 0 ≤ (a / b) := by
  intro a proof_fact_11_1 b proof_fact_11_2 proof_fact_11_3 proof_fact_11_4
  have proof_fact_11_5 : 0 ≤ a := by
    exact proof_fact_11_3
  have proof_fact_11_6 : 0 < b := by
    exact proof_fact_11_4
  have proof_fact_11_7 : 0 ≤ (a / b) := by
    exact div_nonneg proof_fact_11_5 (le_of_lt proof_fact_11_6)
  exact proof_fact_11_7

-- Litex fact f180
theorem fact180 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), 0 < a → 0 < b → 0 < (a / b) := by
  intro a proof_fact_12_1 b proof_fact_12_2 proof_fact_12_3 proof_fact_12_4
  have proof_fact_12_5 : 0 < a := by
    exact proof_fact_12_3
  have proof_fact_12_6 : 0 < b := by
    exact proof_fact_12_4
  have proof_fact_12_7 : 0 < (a / b) := by
    exact div_pos proof_fact_12_5 proof_fact_12_6
  exact proof_fact_12_7

-- Litex fact f196
theorem fact196 : ∀ u ∈ (Set.univ : Set ℝ), ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a ≤ b → (u + a) ≤ (u + b) := by
  intro u proof_fact_13_1 a proof_fact_13_2 b proof_fact_13_3 proof_fact_13_4
  have proof_fact_13_5 : a ≤ b := by
    exact proof_fact_13_4
  have proof_fact_13_6 : (u + a) ≤ (u + b) := by
    linarith only [proof_fact_13_5]
  exact proof_fact_13_6

-- Litex fact f218
theorem fact218 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ c ∈ (Set.univ : Set ℝ), ∀ d ∈ (Set.univ : Set ℝ), a ≤ b → c ≤ d → (a + c) ≤ (b + d) := by
  intro a proof_fact_14_1 b proof_fact_14_2 c proof_fact_14_3 d proof_fact_14_4 proof_fact_14_5 proof_fact_14_6
  have proof_fact_14_7 : a ≤ b := by
    exact proof_fact_14_5
  have proof_fact_14_8 : c ≤ d := by
    exact proof_fact_14_6
  have proof_fact_14_9 : (a + c) ≤ (b + d) := by
    linarith only [proof_fact_14_7, proof_fact_14_8]
  exact proof_fact_14_9

-- Litex fact f234
theorem fact234 : ∀ u ∈ (Set.univ : Set ℝ), ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), a < b → (u + a) < (u + b) := by
  intro u proof_fact_15_1 a proof_fact_15_2 b proof_fact_15_3 proof_fact_15_4
  have proof_fact_15_5 : a < b := by
    exact proof_fact_15_4
  have proof_fact_15_6 : (u + a) < (u + b) := by
    linarith only [proof_fact_15_5]
  exact proof_fact_15_6

-- Litex fact f256
theorem fact256 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ c ∈ (Set.univ : Set ℝ), ∀ d ∈ (Set.univ : Set ℝ), a < b → c < d → (a + c) < (b + d) := by
  intro a proof_fact_16_1 b proof_fact_16_2 c proof_fact_16_3 d proof_fact_16_4 proof_fact_16_5 proof_fact_16_6
  have proof_fact_16_7 : a < b := by
    exact proof_fact_16_5
  have proof_fact_16_8 : c < d := by
    exact proof_fact_16_6
  have proof_fact_16_9 : (a + c) < (b + d) := by
    linarith only [proof_fact_16_7, proof_fact_16_8]
  exact proof_fact_16_9

-- Litex fact f278
theorem fact278 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ c ∈ (Set.univ : Set ℝ), ∀ d ∈ (Set.univ : Set ℝ), a < b → c ≤ d → (a + c) < (b + d) := by
  intro a proof_fact_17_1 b proof_fact_17_2 c proof_fact_17_3 d proof_fact_17_4 proof_fact_17_5 proof_fact_17_6
  have proof_fact_17_7 : a < b := by
    exact proof_fact_17_5
  have proof_fact_17_8 : c ≤ d := by
    exact proof_fact_17_6
  have proof_fact_17_9 : (a + c) < (b + d) := by
    linarith only [proof_fact_17_7, proof_fact_17_8]
  exact proof_fact_17_9

-- Litex fact f300
theorem fact300 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ c ∈ (Set.univ : Set ℝ), ∀ d ∈ (Set.univ : Set ℝ), a ≤ b → c < d → (a + c) < (b + d) := by
  intro a proof_fact_18_1 b proof_fact_18_2 c proof_fact_18_3 d proof_fact_18_4 proof_fact_18_5 proof_fact_18_6
  have proof_fact_18_7 : a ≤ b := by
    exact proof_fact_18_5
  have proof_fact_18_8 : c < d := by
    exact proof_fact_18_6
  have proof_fact_18_9 : (a + c) < (b + d) := by
    linarith only [proof_fact_18_7, proof_fact_18_8]
  exact proof_fact_18_9

-- Litex fact f319
theorem fact319 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ∀ c ∈ (Set.univ : Set ℝ), a ≤ b → (0 : ℝ) ≤ c → (a - c) ≤ b := by
  intro a proof_fact_19_1 b proof_fact_19_2 c proof_fact_19_3 proof_fact_19_4 proof_fact_19_5
  have proof_fact_19_6 : a ≤ b := by
    exact proof_fact_19_4
  have proof_fact_19_7 : (0 : ℝ) ≤ c := by
    exact proof_fact_19_5
  have proof_fact_19_8 : (a - c) ≤ b := by
    linarith only [proof_fact_19_6, proof_fact_19_7]
  exact proof_fact_19_8

-- Litex fact f332
theorem fact332 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), (0 : ℝ) ≤ b → a ≤ (a + b) := by
  intro a proof_fact_20_1 b proof_fact_20_2 proof_fact_20_3
  have proof_fact_20_4 : (0 : ℝ) ≤ b := by
    exact proof_fact_20_3
  have proof_fact_20_5 : a ≤ (a + b) := by
    linarith only [proof_fact_20_4]
  exact proof_fact_20_5

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

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f34
theorem fact34 : ∀ a ∈ {r : ℝ | 0 < r}, ∀ b ∈ {r : ℝ | 0 < r}, ∀ c ∈ {r : ℝ | 0 < r}, ∀ d ∈ {r : ℝ | 0 < r}, ((a + b) + (c + d)) > 0 := by
  intro a proof_fact_1_1 b proof_fact_1_2 c proof_fact_1_3 d proof_fact_1_4
  have proof_fact_1_5 : (0 : ℝ) < a := by
    have proof_fact_2_1 : a ∈ {r : ℝ | 0 < r} := proof_fact_1_1
    simpa using proof_fact_2_1
  have proof_fact_1_6 : (0 : ℝ) < b := by
    have proof_fact_3_1 : b ∈ {r : ℝ | 0 < r} := proof_fact_1_2
    simpa using proof_fact_3_1
  have proof_fact_1_7 : (0 : ℝ) < c := by
    have proof_fact_4_1 : c ∈ {r : ℝ | 0 < r} := proof_fact_1_3
    simpa using proof_fact_4_1
  have proof_fact_1_8 : (0 : ℝ) < d := by
    have proof_fact_5_1 : d ∈ {r : ℝ | 0 < r} := proof_fact_1_4
    simpa using proof_fact_5_1
  have proof_fact_1_9 : (0 : ℝ) < (a + b) := by
    have proof_fact_6_1 : (0 : ℝ) < a := by
      exact proof_fact_1_5
    have proof_fact_6_2 : (0 : ℝ) < b := by
      exact proof_fact_1_6
    have proof_fact_6_3 : (0 : ℝ) < (a + b) := by
      linarith only [proof_fact_6_1, proof_fact_6_2]
    exact proof_fact_6_3
  have proof_fact_1_10 : (0 : ℝ) ≤ (c + d) := by
    have proof_fact_7_1 : (0 : ℝ) ≤ c := by
      have proof_fact_8_1 : (0 : ℝ) < c := by
        exact proof_fact_1_7
      have proof_fact_8_2 : (0 : ℝ) ≤ c := by
        linarith only [proof_fact_8_1]
      exact proof_fact_8_2
    have proof_fact_7_2 : (0 : ℝ) ≤ d := by
      have proof_fact_9_1 : (0 : ℝ) < d := by
        exact proof_fact_1_8
      have proof_fact_9_2 : (0 : ℝ) ≤ d := by
        linarith only [proof_fact_9_1]
      exact proof_fact_9_2
    have proof_fact_7_3 : (0 : ℝ) ≤ (c + d) := by
      linarith only [proof_fact_7_1, proof_fact_7_2]
    exact proof_fact_7_3
  have proof_fact_1_11 : ((a + b) + (c + d)) > 0 := by
    linarith only [proof_fact_1_9, proof_fact_1_10]
  exact proof_fact_1_11

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f10
theorem fact10 : ∀ {α : Type LitexUniverse} [LitexObject α], ∀ (A : Set α), ∀ (B : Set α), (A ∪ B) = (A ∪ B) := by
  intro _ _ A B
  rfl

-- Litex fact f20
theorem fact20 : ∀ {α2 : Type LitexUniverse} [LitexObject α2], ∀ (A : Set α2), ∀ (B : Set α2), (A ∩ B) = (A ∩ B) := by
  intro _ _ A B
  rfl

-- Litex fact f30
theorem fact30 : ∀ {α4 : Type LitexUniverse} [LitexObject α4], ∀ (A : Set α4), ∀ (B : Set α4), (A \ B) = (A \ B) := by
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
# Native `Set` equalities and membership introduction retain the verifier's
# selected zero-, one-, and two-premise builtin route.

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

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f10
theorem fact10 : ∀ {α : Type LitexUniverse} [LitexObject α], ∀ (A : Set α), ∀ (B : Set α), (A ∪ B) = (B ∪ A) := by
  intro _ _ A B
  ext x
  simp [or_comm]

-- Litex fact f17
theorem fact17 : ∀ {α2 : Type LitexUniverse} [LitexObject α2], ∀ (A : Set α2), (A ∪ A) = A := by
  intro _ _ A
  ext x
  simp 

-- Litex fact f24
theorem fact24 : ∀ {α3 : Type LitexUniverse} [LitexObject α3], ∀ (A : Set α3), (A ∪ ∅) = A := by
  intro _ _ A
  ext x
  simp 

-- Litex fact f34
theorem fact34 : ∀ {α4 : Type LitexUniverse} [LitexObject α4], ∀ (A : Set α4), ∀ (B : Set α4), (A ∩ B) = (B ∩ A) := by
  intro _ _ A B
  ext x
  simp [and_comm]

-- Litex fact f50
theorem fact50 : ∀ {α6 : Type LitexUniverse} [LitexObject α6], ∀ (A : Set α6), ∀ (B : Set α6), ∀ x ∈ A, x ∈ (A ∪ B) := by
  intro _ _ A B x proof_fact_1_1
  have proof_fact_1_2 : x ∈ A := by
    exact proof_fact_1_1
  rw [Set.mem_union]
  exact Or.inl proof_fact_1_2

-- Litex fact f66
theorem fact66 : ∀ {α9 : Type LitexUniverse} [LitexObject α9], ∀ (A : Set α9), ∀ (B : Set α9), ∀ x ∈ A, x ∈ B → x ∈ (A ∩ B) := by
  intro _ _ A B x proof_fact_2_1 proof_fact_2_2
  have proof_fact_2_3 : x ∈ A := by
    exact proof_fact_2_1
  have proof_fact_2_4 : x ∈ B := by
    exact proof_fact_2_2
  rw [Set.mem_inter_iff]
  exact ⟨proof_fact_2_3, proof_fact_2_4⟩

-- Litex fact f82
theorem fact82 : ∀ {α12 : Type LitexUniverse} [LitexObject α12], ∀ (A : Set α12), ∀ (B : Set α12), ∀ x ∈ A, x ∉ B → x ∈ (A \ B) := by
  intro _ _ A B x proof_fact_3_1 proof_fact_3_2
  have proof_fact_3_3 : x ∈ A := by
    exact proof_fact_3_1
  have proof_fact_3_4 : x ∉ B := by
    exact proof_fact_3_2
  rw [Set.mem_diff]
  exact ⟨proof_fact_3_3, proof_fact_3_4⟩

-- Litex fact f92
theorem fact92 : ∀ x ∈ (Set.univ : Set ℝ), (0 : ℝ) ≤ x → abs x = x := by
  intro x proof_fact_4_1 proof_fact_4_2
  have proof_fact_4_3 : (0 : ℝ) ≤ x := by
    exact proof_fact_4_2
  exact abs_of_nonneg proof_fact_4_3

-- Litex fact f102
theorem fact102 : ∀ x ∈ (Set.univ : Set ℝ), x ≠ 0 → (0 : ℝ) < abs x := by
  intro x proof_fact_5_1 proof_fact_5_2
  have proof_fact_5_3 : x ≠ 0 := by
    exact proof_fact_5_2
  exact abs_pos.mpr proof_fact_5_3

-- Litex fact f103
theorem fact103 : litexIsNonemptySet (Set.univ : Set ℕ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f104
theorem fact104 : litexIsNonemptySet (Set.univ : Set ℤ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f105
theorem fact105 : litexIsNonemptySet (Set.univ : Set ℚ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f106
theorem fact106 : litexIsNonemptySet (Set.univ : Set ℝ) := by
  refine ⟨0, ?_⟩
  exact Set.mem_univ 0

-- Litex fact f107
theorem fact107 : litexIsNonemptySet (Set.univ : Set ℂ) := by
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

# Boundary: C+ is intentionally not a Litex standard set because complex
# numbers have no canonical order. The Rust regression rejects `1 $in C+`.
# Evidence: cargo test --release compact_standard_numeric_subsets -- --nocapture
# and cargo test --release closed_compact_numeric_memberships -- --nocapture
# Ledger gate: cargo test --release to_lean_examples_markdown_emits_checked_source -- --nocapture
# Implementation: src/to_lean_ir/obj.rs, src/to_lean_ir/carrier.rs,
# and src/to_lean/to_lean_pipeline.rs.
```

```lean
import Mathlib

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f7
theorem fact7 : ∀ r ∈ {r : ℝ | 0 < r}, r ∈ {r : ℝ | 0 < r} := by
  intro r proof_fact_1_1
  have proof_fact_1_2 : 0 < r := by
    have proof_fact_2_1 : r ∈ {r : ℝ | 0 < r} := proof_fact_1_1
    simpa using proof_fact_2_1
  exact proof_fact_1_1

-- Litex fact f14
theorem fact14 : ∀ n ∈ {n : ℕ | 0 < n}, n ∈ {n : ℕ | 0 < n} := by
  intro n proof_fact_3_1
  exact proof_fact_3_1

-- Litex fact f15
theorem fact15 : {n : ℕ | 0 < n} = {n : ℕ | 0 < n} := by
  rfl

-- Litex fact f22
theorem fact22 : ∀ q ∈ {q : ℚ | 0 < q}, q ∈ {q : ℚ | 0 < q} := by
  intro q proof_fact_4_1
  exact proof_fact_4_1

-- Litex fact f35
theorem fact35 : ∀ z ∈ {z : ℤ | z < 0}, z ∈ {z : ℤ | z < 0} := by
  intro z proof_fact_5_1
  exact proof_fact_5_1

-- Litex fact f48
theorem fact48 : ∀ q ∈ {q : ℚ | q < 0}, q ∈ {q : ℚ | q < 0} := by
  intro q proof_fact_6_1
  exact proof_fact_6_1

-- Litex fact f61
theorem fact61 : ∀ r ∈ {r : ℝ | r < 0}, r ∈ {r : ℝ | r < 0} := by
  intro r proof_fact_7_1
  exact proof_fact_7_1

-- Litex fact f68
theorem fact68 : ∀ z ∈ {z : ℤ | z ≠ 0}, z ∈ {z : ℤ | z ≠ 0} := by
  intro z proof_fact_8_1
  exact proof_fact_8_1

-- Litex fact f75
theorem fact75 : ∀ q ∈ {q : ℚ | q ≠ 0}, q ∈ {q : ℚ | q ≠ 0} := by
  intro q proof_fact_9_1
  exact proof_fact_9_1

-- Litex fact f82
theorem fact82 : ∀ r ∈ {r : ℝ | r ≠ 0}, r ∈ {r : ℝ | r ≠ 0} := by
  intro r proof_fact_10_1
  exact proof_fact_10_1

-- Litex fact f89
theorem fact89 : ∀ c ∈ {c : ℂ | c ≠ 0}, c ∈ {c : ℂ | c ≠ 0} := by
  intro c proof_fact_11_1
  exact proof_fact_11_1

-- Litex fact f90
theorem fact90 : 1 ∈ {n : ℕ | 0 < n} := by
  norm_num

-- Litex fact f91
theorem fact91 : (0 : ℕ) < 1 := by
  norm_num

-- Litex fact f92
theorem fact92 : 1 ∈ {q : ℚ | 0 < q} := by
  norm_num

-- Litex fact f93
theorem fact93 : 2 ∈ {r : ℝ | 0 < r} := by
  norm_num

-- Litex fact f94
theorem fact94 : (0 : ℝ) < 2 := by
  have proof_fact_12_1 : 2 ∈ {r : ℝ | 0 < r} := fact93
  simpa using proof_fact_12_1

-- Litex fact f95
theorem fact95 : (0 - 1) ∈ {z : ℤ | z < 0} := by
  norm_num

-- Litex fact f96
theorem fact96 : (0 - 1 : ℤ) < 0 := by
  norm_num

-- Litex fact f98
theorem fact98 : (0 - 1) ∈ {q : ℚ | q < 0} := by
  norm_num

-- Litex fact f99
theorem fact99 : (0 - 1) ∈ {r : ℝ | r < 0} := by
  norm_num

-- Litex fact f100
theorem fact100 : 1 ∈ {z : ℤ | z ≠ 0} := by
  norm_num

-- Litex fact f101
theorem fact101 : (1 : ℤ) ≠ 0 := by
  norm_num

-- Litex fact f102
theorem fact102 : 1 ∈ {q : ℚ | q ≠ 0} := by
  norm_num

-- Litex fact f103
theorem fact103 : 1 ∈ {r : ℝ | r ≠ 0} := by
  norm_num

-- Litex fact f104
theorem fact104 : 1 ∈ {c : ℂ | c ≠ 0} := by
  norm_num

-- Litex fact f105
theorem fact105 : 0 ∉ {n : ℕ | 0 < n} := by
  norm_num

-- Litex fact f106
theorem fact106 : 0 ∉ {q : ℚ | 0 < q} := by
  norm_num

-- Litex fact f107
theorem fact107 : 0 ∉ {r : ℝ | 0 < r} := by
  norm_num

-- Litex fact f108
theorem fact108 : 0 ∉ {z : ℤ | z < 0} := by
  norm_num

-- Litex fact f109
theorem fact109 : 0 ∉ {q : ℚ | q < 0} := by
  norm_num

-- Litex fact f110
theorem fact110 : 0 ∉ {r : ℝ | r < 0} := by
  norm_num

-- Litex fact f111
theorem fact111 : 0 ∉ {z : ℤ | z ≠ 0} := by
  norm_num

-- Litex fact f112
theorem fact112 : 0 ∉ {q : ℚ | q ≠ 0} := by
  norm_num

-- Litex fact f113
theorem fact113 : 0 ∉ {r : ℝ | r ≠ 0} := by
  norm_num

-- Litex fact f114
theorem fact114 : 0 ∉ {c : ℂ | c ≠ 0} := by
  norm_num

end
```

## builtin_predicates

```litex
# Tracer: native builtin propositions with selected checked proof routes.
#
# Before (Litex verified, strict To-Lean rejected):
# $prime(53)
# forall A, B set:
#     A $subset B
#     =>:
#         B $superset A
# Former behavior: `$prime` had no native Lean predicate, `$superset` and
# proper relations had no proposition lowering, and duality lost its premise.
#
# Now (strict To-Lean): closed prime facts use `Nat.Prime` plus checked
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
# Evidence: cargo test --release to_lean_examples_markdown_emits_checked_source -- --nocapture
```

```lean
import Mathlib

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f1
theorem fact1 : Nat.Prime 53 := by
  norm_num

-- Litex fact f10
theorem fact10 : ¬ Nat.Prime 54 := by
  norm_num

-- Litex fact f38
theorem fact38 : ∀ {α1 : Type LitexUniverse} [LitexObject α1], ∀ (A : Set α1), ∀ (B : Set α1), A ⊆ B → A ⊆ B := by
  intro _ _ A B proof_fact_1_1
  have proof_fact_1_2 : A ⊆ B := by
    exact proof_fact_1_1
  exact proof_fact_1_2

-- Litex fact f66
theorem fact66 : ∀ {α9 : Type LitexUniverse} [LitexObject α9], ∀ (A : Set α9), ∀ (B : Set α9), B ⊆ A → B ⊆ A := by
  intro _ _ A B proof_fact_2_1
  have proof_fact_2_2 : B ⊆ A := by
    exact proof_fact_2_1
  exact proof_fact_2_2

-- Litex fact f79
theorem fact79 : ∀ {α17 : Type LitexUniverse} [LitexObject α17], ∀ (A : Set α17), ∀ (B : Set α17), ¬ (A ⊆ B) → ¬ (A ⊆ B) := by
  intro _ _ A B proof_fact_3_1
  have proof_fact_3_2 : ¬ (A ⊆ B) := by
    exact proof_fact_3_1
  exact proof_fact_3_2

-- Litex fact f92
theorem fact92 : ∀ {α19 : Type LitexUniverse} [LitexObject α19], ∀ (A : Set α19), ∀ (B : Set α19), ¬ (B ⊆ A) → ¬ (B ⊆ A) := by
  intro _ _ A B proof_fact_4_1
  have proof_fact_4_2 : ¬ (B ⊆ A) := by
    exact proof_fact_4_1
  exact proof_fact_4_2

-- Litex fact f117
theorem fact117 : ∀ {α21 : Type LitexUniverse} [LitexObject α21], ∀ (A : Set α21), ∀ (B : Set α21), (A ⊆ B) ∧ A ≠ B → (A ⊆ B) ∧ A ≠ B := by
  intro _ _ A B proof_fact_5_1
  exact proof_fact_5_1

-- Litex fact f127
theorem fact127 : ∀ {α26 : Type LitexUniverse} [LitexObject α26], ∀ (A : Set α26), ∀ (B : Set α26), ¬ (A ⊆ B) ∨ A = B → ¬ (A ⊆ B) ∨ A = B := by
  intro _ _ A B proof_fact_6_1
  exact proof_fact_6_1

-- Litex fact f152
theorem fact152 : ∀ {α28 : Type LitexUniverse} [LitexObject α28], ∀ (A : Set α28), ∀ (B : Set α28), (B ⊆ A) ∧ A ≠ B → (B ⊆ A) ∧ A ≠ B := by
  intro _ _ A B proof_fact_7_1
  exact proof_fact_7_1

-- Litex fact f162
theorem fact162 : ∀ {α33 : Type LitexUniverse} [LitexObject α33], ∀ (A : Set α33), ∀ (B : Set α33), ¬ (B ⊆ A) ∨ A = B → ¬ (B ⊆ A) ∨ A = B := by
  intro _ _ A B proof_fact_8_1
  exact proof_fact_8_1

-- Litex fact f172
theorem fact172 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ¬ (a < b) → ¬ (a < b) := by
  intro a proof_fact_9_1 b proof_fact_9_2 proof_fact_9_3
  exact proof_fact_9_3

-- Litex fact f182
theorem fact182 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ¬ (a ≤ b) → ¬ (a ≤ b) := by
  intro a proof_fact_10_1 b proof_fact_10_2 proof_fact_10_3
  exact proof_fact_10_3

-- Litex fact f192
theorem fact192 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ¬ (a > b) → ¬ (a > b) := by
  intro a proof_fact_11_1 b proof_fact_11_2 proof_fact_11_3
  exact proof_fact_11_3

-- Litex fact f202
theorem fact202 : ∀ a ∈ (Set.univ : Set ℝ), ∀ b ∈ (Set.univ : Set ℝ), ¬ (a ≥ b) → ¬ (a ≥ b) := by
  intro a proof_fact_12_1 b proof_fact_12_2 proof_fact_12_3
  exact proof_fact_12_3

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

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

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

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

## carrier_boundaries

<!-- to-lean: partial -->

```litex
# These statements all verify in Litex. Report-mode To-Lean identifies the
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

-- To-Lean status: incomplete
-- Omitted statements: 11

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- To-Lean omitted statement 1 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:4.
-- Statement: forall #0#n N: #0#n + 1 $in N
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "N: a + b from a in N and b in N" }

-- To-Lean omitted statement 2 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:7.
-- Statement: forall #1#n N: #1#n + 1 $in Z
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Z" }

-- To-Lean omitted statement 3 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:10.
-- Statement: forall #2#z Z: #2#z - 1 $in Z
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "Z closure: arithmetic operands in Z; pow base in Z and exponent in N, or base in N+ and exponent in N" }

-- To-Lean omitted statement 4 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:13.
-- Statement: forall #3#z Z: #3#z / 2 $in Q
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- To-Lean omitted statement 5 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:16.
-- Statement: forall #4#z Z, #5#q Q: #4#z + #5#q $in Q
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- To-Lean omitted statement 6 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:19.
-- Statement: forall #6#z Z, #7#q Q: #6#z / 2 + #7#q $in Q
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "numeric-carrier strategy: structural closure in Q" }

-- To-Lean omitted statement 7 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:22.
-- Statement: forall #8#n N+: #8#n - 1 $in N
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "N: n - 1 from n in N+" }

-- To-Lean omitted statement 8 during IR construction at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:25.
-- Statement: have #10#boundary_natural_two N = 2
-- Reason: have-object equality inferred consequences are not represented by this To-Lean tranche

-- To-Lean omitted statement 9 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:26.
-- Statement: have #12#boundary_integer_two Z = 2
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "number in Z" }

-- To-Lean omitted statement 10 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:27.
-- Statement: have #14#boundary_rational_half Q = 1 / 2
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "number in Q" }

-- To-Lean omitted statement 11 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#carrier_boundaries:28.
-- Statement: have #16#boundary_complex_one C = 1
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "number in C" }

end
```

## partial_boundary

<!-- to-lean: partial -->

```litex
# All three statements verify in Litex. Report-mode To-Lean emits statements
# one and three, marks statement two unsupported, and returns Incomplete.

1 / 2 / 3 / 4 = 1 / 24
sin(0) = 0
1 / 3 + 2 / 3 = 1

# Strict To-Lean intentionally fails on the unsupported trigonometric proof;
# report mode never replaces it with `sorry`, an opaque constant, or an axiom.
```

```lean
import Mathlib

-- To-Lean status: incomplete
-- Omitted statements: 1

noncomputable section

universe LitexUniverse

abbrev LitexFact := Prop

class LitexObject (α : Type LitexUniverse) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type LitexUniverse} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type LitexUniverse} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type LitexUniverse} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type LitexUniverse} (set : Set α) : Prop := set.Finite

-- Litex fact f1
theorem fact1 : (((1 / 2) / 3) / 4 : ℚ) = (1 / 24) := by
  -- native proof view, left fraction: (1 : ℝ) / (((2 : ℝ) * (3 : ℝ)) * (4 : ℝ))
  -- native proof view, right fraction: (1 : ℝ) / (24 : ℝ)
  norm_num

-- To-Lean omitted statement 2 during Lean emission at examples/09_to_lean/litex_to_lean_examples.md#partial_boundary:5.
-- Statement: sin(0) = 0
-- Reason: To-Lean has no checked backend for proof rule OtherUnsupported { name: "trigonometry layer 0: canonical expansion from core values at zero" }

-- Litex fact f3
theorem fact3 : ((1 / 3) + (2 / 3) : ℚ) = 1 := by
  -- native proof view, left fraction: ((3 : ℝ) + ((2 : ℝ) * (3 : ℝ))) / ((3 : ℝ) * (3 : ℝ))
  -- native proof view, right fraction: (1 : ℝ) / (1 : ℝ)
  norm_num

end
```
