# Litex and Lean: Interfaces, Foundations, and a Compilation Bridge

Jiachen Shen and The Litex Team, 2026-05-07. Email: litexlang@outlook.com

Try the examples in browser: https://litexlang.com/doc/Litex_and_Lean

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_and_Lean.md

Related docs:

- [Manual](https://litexlang.com/doc/Manual)
- [FAQ](https://litexlang.com/doc/FAQ)
- [Litex To Python](https://litexlang.com/doc/Litex_To_Python)
- [Complex Scalar Migration](Complex_Scalar_Migration.md)

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [CLI](https://litexlang.com/doc/cli) for the supported language codes.

## Shared Aim, Different Layers

Litex and Lean both make mathematics machine-checkable, but they expose
different layers. Lean provides dependent type theory, proof terms, tactics,
Mathlib, and a mature community. Litex provides a fact-oriented,
set-theoretic surface where objects, relations, and the next verified fact are
the main interface.

Litex is independent and is not intended to replace Lean. The practical
difference is simple: Lean usually asks the user to guide a proof state with
theorems or tactics; Litex lets the user write a target fact and matches it
against context, builtin rules, and known facts.

AI makes this interface question more important, not less. A model can often
generate correct theorem names, tactic calls, side-condition proofs, and other
proof-assistant machinery. That lowers generation cost. It does not by itself
lower the cost for a mathematician to understand the resulting artifact,
change one assumption, or review why a step is valid. Litex's intended role is
to let AI fill routine machine details while keeping the durable source at the
level of recognizable mathematical facts, with the hidden verification route
available for inspection.

This page keeps the existing examples as the main comparison. A narrow
Litex-to-Lean experiment is described near the end: it currently accepts only
verified rational equalities over `R`, recursively exposes their numerator and
denominator structure, and emits `ring` or `field_simp` followed by `ring`.
Exact proof-path replay remains future work and requires structured provenance.

---

## AI Lowers Generation Cost, Not Automatically Understanding Cost

Suppose `0 < epsilon <= 1`, `abs(x) < epsilon`, and `abs(y) < epsilon`. The
mathematical proof that `abs(x * y) < epsilon` is the short estimate

\[
|xy| = |x||y| < \varepsilon^2 \leq \varepsilon.
\]

In a lower-level formal proof, this estimate may also expose reflexivity,
absolute-value nonnegativity, multiplication monotonicity, and strict-versus-
nonstrict order conversions. Those are real obligations. An AI system can
write them cheaply, but a reader may still have to recover the estimate from
the generated interface code.

The following runnable Litex tracer keeps one general product-monotonicity
premise in the context and leaves the main argument as the recognizable
calculation:

```litex
claim:
    ? forall x, y, epsilon R:
        forall a, b, c, d R:
            0 <= a < c
            0 <= b < d
            =>:
                a * b < c * d
        0 < epsilon
        epsilon <= 1
        abs(x) < epsilon
        abs(y) < epsilon
        =>:
            abs(x * y) < epsilon
    0 <= abs(x) < epsilon
    0 <= abs(y) < epsilon
    abs(x * y) = abs(x) * abs(y) < epsilon * epsilon <= epsilon * 1 = epsilon
```

The claim is not that Lean cannot present a concise proof; Lean has powerful
automation, abstractions, and libraries, and AI can use them. The hypothesis
being tested is different: the checked source that survives after generation
should remain a mathematical explanation rather than merely valid generated
code. Litex therefore needs two coupled layers:

1. a short source layer containing definitions, facts, witnesses, cases, and
   calculation chains that mathematicians can read and edit; and
2. an audit layer showing which known fact, definition, builtin rule, theorem,
   or explicit assumption justified each accepted step.

If automation makes the source short but its reasoning cannot be inspected,
Litex has only traded one understanding problem for another.

---

## First Examples

### Main README Example

<!-- litex:skip-test -->
```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

```lean
import Mathlib.Tactic
example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩
```

**What differs.** Litex writes the desired facts directly. The checker stores `x = 2` in the local context, substitutes it into later goals, and closes the arithmetic. Lean names the hypothesis and guides rewriting explicitly through its proof language.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

### Smallest Facts

<!-- litex:skip-test -->
```litex
1 + 1 = 2
1 $in {1, 2}
forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

```lean
import Mathlib
example : 1 + 1 = 2 := by
  norm_num
example : 1 ∈ ({1, 2} : Finset ℕ) := by
  simp
example (a : ℕ) (ha : a ∈ ({1, 2, 3} : Finset ℕ)) :
    a = 1 ∨ a = 2 ∨ a = 3 := by
  simpa using ha
```

**What differs.** Litex writes arithmetic and membership as direct facts. Lean proves them quickly too, but usually after choosing the set-like type and calling simplification. If an object is in an enumerated set such as `{1, 2, 3}`, Litex immediately knows the corresponding disjunction: `a = 1 or a = 2 or a = 3`.

```litex
1 + 1 = 2
1 $in {1, 2}
forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

### One Epsilon Proof, Two Interfaces

For a more substantial comparison, suppose a real sequence `s` converges to
`a`. Multiplying every term by a real constant `c` should produce a sequence
that converges to `c * a`.

Here is a Lean proof using the usual epsilon definition. It splits on `c = 0`;
in the nonzero case it applies convergence at `epsilon / |c|` and then uses
the absolute-value product law.

```lean
import MIL.Common
import Mathlib.Data.Real.Basic

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by
    exact div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hs n ngt) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
```

The Litex proof chooses `epsilon / (abs(c) + 1)` instead. Since the denominator
is always positive, the same estimate covers `c = 0` and `c != 0` without a
case split.

```litex
prop is_eventually_close(s fn(n N) R, a R, epsilon R+, N0 N):
    forall n N:
        n >= N0
        =>:
            abs(s(n) - a) < epsilon

prop converges_to(s fn(n N) R, a R):
    forall epsilon R+:
        exist N0 N st {$is_eventually_close(s, a, epsilon, N0)}

thm converges_to_mul_const:
    ? forall s fn(n N) R, a, c R:
        $converges_to(s, a)
        =>:
            $converges_to(fn(n N) R {c * s(n)}, c * a)
    claim:
        ? forall epsilon R+:
            exist N0 N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)}
        abs(c) + 1 > 0
        epsilon / (abs(c) + 1) $in R+
        obtain N0 from exist K N st {$is_eventually_close(s, a, epsilon / (abs(c) + 1), K)}
        witness exist K N st {$is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, K)} from N0:
            forall n N:
                n >= N0
                =>:
                    abs(s(n) - a) < epsilon / (abs(c) + 1)
                    abs(c * s(n) - c * a) = abs(c * (s(n) - a)) = abs(c) * abs(s(n) - a)
                    abs(c) * abs(s(n) - a) <= (abs(c) + 1) * abs(s(n) - a) < (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    abs(fn(k N) R {c * s(k)}(n) - c * a) < epsilon
            by def $is_eventually_close(fn(n N) R {c * s(n)}, c * a, epsilon, N0)
    by def $converges_to(fn(n N) R {c * s(n)}, c * a)
```

Both proofs use the same mathematical core: obtain a tail bound for a smaller
positive tolerance, reuse the same cutoff, and estimate the scaled absolute
difference. The interface difference is visible in the durable proof text.
Lean exposes named hypotheses, a case split, rewriting, and library lemmas;
Litex exposes the nested convergence facts, the witness, and the inequality
chain directly, while its checker supplies routine arithmetic and definition
folding.

This comparison is not a claim that Lean needs the displayed proof shape or
cannot use the `abs(c) + 1` argument. Lean can formalize that uniform argument
too, and Mathlib offers much broader analysis infrastructure. The example
shows how the two default proof interfaces organize one elementary analysis
argument, not a difference in what mathematics they can express.

---

## The Manual Mental Model

The main Litex model is:

1. **Objects** are the mathematical things being discussed.
2. **Facts** are claims about those objects.
3. **Statements** are proof-script actions that define objects, assert facts, open local proofs, split cases, or provide witnesses.
4. **Execution** grows the current verified context by storing accepted facts and running inference.
5. **The proof process** checks each fact using well-definedness, builtin rules, known facts, and known `forall` facts.
6. **The explicit mathematical background** comes from imported standard packages and local modules; the checker separately supplies its builtin verification rules.

Every factual statement has exactly one of three Litex outcomes: **true**,
**unknown**, or **error**. `true` means the checker found a proof path, such as
a builtin rule, a known fact, or a known `forall` fact. `unknown` means the fact
is meaningful but no available route proved it. `error` means Litex cannot
check the line as a valid fact, usually because of syntax or well-definedness:
an undeclared object, a function argument outside its domain, or `1 / 0`.

This is the best way to compare Litex and Lean. The difference is not one isolated syntax trick. It is a different boundary between surface language, checker behavior, and proof-engine instruction. Lean gives the user access to a powerful general proof environment; Litex asks the user to write mathematical facts and lets context growth, matching, substitution, and explainable provenance do more routine work.

---

## Objects: What Mathematical Things Look Like

Litex presents many everyday mathematical objects directly: numbers, sets, tuples, functions, set-builder expressions, Cartesian products, finite displays, sums, products, and matrices.

Lean can express these ideas too, often with more precision and more generality. But the user usually meets type-level encodings earlier: `Set`, `Finset`, subtypes, coercions, and theorem-library conventions.

### Set-Builder Domains And Functions

These examples belong together because they involve objects whose validity depends on a domain condition or a function definition.

<!-- litex:skip-test -->
```litex
forall x {y R: y > 0}:
    x > 0
```

```lean
import Mathlib
example (x : {y : ℝ // y > 0}) : (x : ℝ) > 0 := by
  exact x.property
```

**What differs.** Litex keeps the domain condition in the parameter. Lean usually packages the value and proof as a subtype.

```litex
forall x {y R: y > 0}:
    x > 0
```

<!-- litex:skip-test -->
```litex
have fn g(x R: x > 0) R = x + 1
g(1) = 2
```

```lean
import Mathlib
def g (x : {x : ℝ // x > 0}) : ℝ := x.val + 1
example : g ⟨1, by norm_num⟩ = 2 := by
  norm_num [g]
```

**What differs.** Litex checks `1 > 0` as background mathematics. Lean passes a subtype value containing both `1` and its proof.

```litex
have fn g(x R: x > 0) R = x + 1

g(1) = 2
```

<!-- litex:skip-test -->
```litex
have fn h(x R) R by cases:
    case x = 2: 3
    case x != 2: 4
h(2) = 3
```

```lean
import Mathlib
noncomputable def h (x : ℝ) : ℝ := if x = 2 then 3 else 4
example : h 2 = 3 := by
  simp [h]
```

**What differs.** Litex's `case` form reads like a piecewise definition. Before storing the
definition, Litex verifies that the cases cover the declared domain and are pairwise mutually
exclusive, so source order is not priority. Lean can faithfully lower that partition to `if` and
unfold it with simplification. Function equality has no negated atomic form: `$fn_eq(f, g)` and
`$fn_eq(g, f)` are symmetric statements, not complementary branches.

```litex
have fn h(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

h(2) = 3
```

<!-- litex:skip-test -->
```litex
have fn k(z R) R by cases:
    case z = 2: 3
    case z != 2: 4
have x R
by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

```lean
import Mathlib
noncomputable def k (z : ℝ) : ℝ := if z = 2 then 3 else 4
example (x : ℝ) : k x > 2 := by
  by_cases h : x = 2
  · simp [k, h]
  · simp [k, h]
```

**What differs.** Litex keeps the cases and the function use close together. Lean introduces a named case assumption and feeds it to `simp`.

```litex
have fn k(z R) R by cases:
    case z = 2: 3
    case z != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

### Application-Flavored Definitions Stay Close To The Formula

Application problems often start from a formula that domain users already know.
For example, the signed area of the parallelogram spanned by two planar vectors
`x` and `y` is `x[1] * y[2] - x[2] * y[1]`.

<!-- litex:skip-test -->
```litex
have fn signed_area(x, y cart(R, R)) R = x[1] * y[2] - x[2] * y[1]

signed_area((1, 0), (0, 1)) = 1 * 1 - 0 * 0 = 1
```

```lean
import Mathlib
def signedArea (x y : ℝ × ℝ) : ℝ :=
  x.1 * y.2 - x.2 * y.1

example : signedArea (1, 0) (0, 1) = 1 := by
  norm_num [signedArea]
```

This matters for applied mathematics. Many users who want to verify a geometry,
physics, economics, or engineering calculation are not trying to study type
theory first. Litex has an advantage in this setting because common applied
objects can be written as ordinary mathematical objects, and the proof script
can stay focused on the formula and the calculation rather than on choosing the
right type-theoretic encoding or library API.

```litex
have fn signed_area(x, y cart(R, R)) R = x[1] * y[2] - x[2] * y[1]

signed_area((1, 0), (0, 1)) = 1 * 1 - 0 * 0 = 1
```

### Frozen Python Extraction Experiment

Litex preserves a frozen experimental extractor for a small set of mathematical
definitions with an obvious programming-language shape. It can verify the
supported source and emit ordinary Python with `litex -python`, but it is not a
general compiler or a production backend.

```litex
have dt R+ = 1 / 100
have fn euler_step(y, dy R) R = y + dt * dy
have algo for euler_step(y, dy):
    y + dt * dy
have fn twice_step(y, dy R) R = euler_step(euler_step(y, dy), dy)
have algo for twice_step(y, dy):
    euler_step(euler_step(y, dy), dy)
```

The current Python extractor emits code shaped like:

```python
dt = (1.0 / 100.0)

def euler_step(y, dy):
    return (y + (dt * dy))

def twice_step(y, dy):
    return euler_step(euler_step(y, dy), dy)
```

The preserved v1 subset emits numeric constants and `R`-parameter
`have algo for` implementations as Python `float` code. Domain-restricted
mathematical functions such as `fn(x R: x > 0) R` remain outside that subset.
The extractor receives compatibility and regression fixes, but its feature
surface is not being expanded. See
[Litex To Python](https://litexlang.com/doc/Litex_To_Python) for the exact
supported subset and trust boundary.

### Anonymous Functions Can Be Passed Directly

Litex treats anonymous functions as ordinary objects. You can pass them directly into `sum`, `product`, or another higher-level mathematical object without first giving the function a separate name. This is useful for nested sums and products, where naming every temporary function would distract from the formula.

<!-- litex:skip-test -->
```litex
eval sum(1, 3, fn(x N+) N+ {sum(1, x, fn(y N+) N+ {x + y})})
```

```lean
def inner (x : ℤ) : ℤ :=
  Finset.sum (Finset.Icc 1 x) (fun y => x + y)
def total : ℤ :=
  Finset.sum (Finset.Icc 1 3) inner
```

**What differs.** Litex can pass an anonymous function object directly to a repeated sum or product. Lean can do the same mathematics, but users often introduce `fun` expressions, named definitions, ranges, coercions, or library conventions around finite sums.

```litex
eval sum(1, 3, fn(x N+) N+ {sum(1, x, fn(y N+) N+ {x + y})})
```

### Set Expressions Are Ordinary Objects

Because Litex is set-theoretic, set expressions are also ordinary objects. A set-builder or a finite set can appear where an object appears, just like `1`, `R`, or a function object. You do not need to define an extra named set first when the expression itself is clear.

<!-- litex:skip-test -->
```litex
{x R: x > 0} = {x R: x > 0}
{1, 2} = {1, 2}
```

```lean
import Mathlib
example : ({x : ℝ | x > 0} : Set ℝ) = {x : ℝ | x > 0} := by
  rfl
example : ({1, 2} : Finset ℕ) = {1, 2} := by
  rfl
```

**What differs.** Litex's set expressions are objects that can be passed around and compared directly without first naming them. Lean also has sets, but the surrounding type (`Set ℝ`, `Finset ℕ`, subtype, and so on) is usually explicit.

```litex
{x R: x > 0} = {x R: x > 0}
{1, 2} = {1, 2}
```

---

## Facts: How Claims Are Written

Litex proof scripts are built from facts. A fact may be atomic, such as equality or membership, or structured, such as a chain, an existential fact, a universal fact, a disjunction, or a conjunction.

Lean also proves propositions. The surface difference is that Lean code usually starts from a theorem goal and then constructs a proof of that goal, while Litex lets many facts appear directly as proof-script lines.

### Calculation Chains

<!-- litex:skip-test -->
```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4
```

```lean
import Mathlib
example (x y : ℝ)
    (h1 : 2 * x + 3 * y = 10)
    (h2 : 4 * x + 5 * y = 14) :
    y = 6 ∧ x = -4 := by
  have hy : y = 6 := by
    calc
      y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) := by linarith
      _ = 2 * 10 - 14 := by rw [h1, h2]
      _ = 6 := by norm_num
  have hx : x = -4 := by
    calc
      x = ((2 * x + 3 * y) - 3 * y) / 2 := by ring
      _ = (10 - 3 * 6) / 2 := by rw [h1, hy]
      _ = -4 := by norm_num
  constructor
  · exact hy
  · exact hx
```

**What differs.** Litex's calculation chain is one factual statement. Lean's explicit version uses named goals, `calc`, rewrites, and tactics.

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4
```

---

## Statements: How A Proof Script Moves

Litex statements are proof-script actions: `have`, `claim`, `witness`, `by cases`, `by contra`, `by enumerate`, `by induc`, and so on.

Lean also has structured proof commands and tactics. The difference is that Litex statements are meant to look like common mathematical proof moves, while Lean tactics operate a very general proof state.

### Witness Statements
<!-- litex:skip-test -->
```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

```lean
import Mathlib
example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

**What differs.** Litex puts the concrete values first. Lean packages values and obligations through constructors.

```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

### Contradiction

<!-- litex:skip-test -->
```litex
abstract_prop p0(x, y)
abstract_prop q0(x, y)
claim:
    ? forall:
        forall a, b R:
            $p0(a, b)
            =>:
                $q0(a, b)
        not $q0(1, 2)
        =>:
            not $p0(1, 2)
    by contra:
        ? not $p0(1, 2)
        impossible $q0(1, 2)
```

```lean
import Mathlib
example (p q : ℝ → ℝ → Prop)
    (h : ∀ a b, p a b → q a b)
    (hnq : ¬ q 1 2) :
    ¬ p 1 2 := by
  intro hp
  exact hnq (h 1 2 hp)
```

**What differs.** Litex writes the contradiction as a proof move. Lean expresses it as a function from an assumption to contradiction.


### Set Equality By Counterexample

<!-- litex:skip-test -->
```litex
by contra:
    ? {a N: a % 4 = 0} != {a N: a % 2 = 0}
    by thm set_builder_member(2, {a N: a % 2 = 0})
    2 $in {a N: a % 2 = 0}
    2 $in {a N: a % 4 = 0}
    impossible 2 % 4 = 0
```

```lean
import Mathlib
example : ({a : ℕ | a % 4 = 0} : Set ℕ) ≠ {a : ℕ | a % 2 = 0} := by
  intro h
  have h2 : (2 : ℕ) ∈ ({a : ℕ | a % 2 = 0} : Set ℕ) := by
    norm_num
  have h4 : (2 : ℕ) ∈ ({a : ℕ | a % 4 = 0} : Set ℕ) := by
    rw [h]
    exact h2
  norm_num at h4
```

**What differs.** Litex uses `2` as the counterexample directly. Under the temporary equality assumption, membership transfers from the even naturals to the multiples of `4`, and the arithmetic contradiction closes the proof. Lean names the equality, rewrites the membership goal, and lets `norm_num` discharge the false modular fact.

```litex
by contra:
    ? {a N: a % 4 = 0} != {a N: a % 2 = 0}
    by thm set_builder_member(2, {a N: a % 2 = 0})
    2 $in {a N: a % 2 = 0}
    2 $in {a N: a % 4 = 0}
    impossible 2 % 4 = 0
```

---

## Proof Process: Why Litex Needs Less Instruction

_A mathematician, like a painter or a poet, is a maker of patterns._

_– G. H. Hardy, *A Mathematician's Apology*_

When Litex checks a fact, the usual loop is:

1. Check that the objects are well-defined.
2. Try builtin mathematical rules.
3. Try matching known facts.
4. Try matching known `forall` facts.

The output status is always one of three cases. If a route succeeds, the fact is
`true`. If the objects are meaningful but no route succeeds, the fact is
`unknown`. If the syntax or well-definedness check fails, the result is
`error`; typical examples are an undeclared object, applying a function outside
its domain, or writing `1 / 0`.

In Lean, the user often chooses the step explicitly: rewrite with this hypothesis, simplify this definition, apply this theorem, run this tactic. This gives very fine control and scales to deep formal developments. Litex chooses a different default for ordinary mathematics: many routine proof paths are tried by the checker.

### Conceptual Verification Correspondence

The following table compares verification responsibilities, not surface syntax
or compiler stages. It is not a claim that every Litex verification route has a
single corresponding Lean primitive, nor is it a list of features supported by
the current Litex-to-Lean compiler. On the Lean side, elaboration, tactics, and
library theorems may construct a proof term; Lean's kernel then checks that
term.

| Litex verification route | Conceptual Lean counterpart |
| --- | --- |
| well-definedness | elaboration and type checking; subtype or dependent-type proof obligations; termination checking for recursive definitions |
| builtin rule | application of a Mathlib theorem, or generation of another proof term checked by Lean |
| direct match with the same known atomic fact | a local hypothesis or theorem used by `exact` or `assumption` |
| equality-compatible matching and substitution | equality transport or rewriting, such as `rw`, `subst`, `Eq.mp`, or `Eq.rec` |
| use of a `prop` definition | definition unfolding or an explicit fold/unfold theorem, often exposed through `rw` or `simp` |
| instantiation of a known `forall` fact | theorem application, treating a universal proof as a function, such as `h a` |
| witness | construction of an existential proof, such as `Exists.intro witness proof` |
| conjunction | construction of both components, such as `And.intro hp hq` |
| cases | elimination of a disjunction or another inductive value, such as `Or.elim` or an inductive recursor |
| contradiction | construction of the target from `False`, such as `False.elim` |
| strategy | a Lean tactic or macro that must ultimately elaborate to a proof term |

Likewise, storing a verified Litex fact in the current context corresponds
conceptually to extending a Lean local context with a proof `h : P`. If the fact
is intended to remain available globally, the closer Lean counterpart is a
named theorem declaration. Litex additionally indexes, matches, and infers from
stored facts automatically, so its runtime environment is not identical to a
Lean local context.

### Less IDE-Centered Proof Writing

Lean's editor support is one of its strengths. In ordinary Lean development,
the IDE is often part of the proof process: a tactic changes the current goal
into new goals, the user reads the updated hypotheses and targets, and the next
command is chosen in response to that state. This is powerful, but it makes much
of the workflow goal-state driven. The proof script is often written by
interactively steering a changing proof state until no goals remain.

Litex is designed to be less dependent on that style of interaction. A Litex
proof usually reads as a sequence of mathematical facts, witnesses, cases,
equalities, and contradictions in roughly the order a person would write the
argument. The user is not primarily satisfying a succession of changing goals
reported by an IDE; the user is writing the intended derivation, and the checker
accepts each line when it follows from the current context. IDE support and good
diagnostics still matter, but the core workflow should remain usable from a
plain file and a command-line verifier.

## Speed Is A Design Signal, Not Just An Optimization

Lean's generality is a real strength. It supports proof terms, elaboration,
typeclass search, tactic programming, large library imports, and highly
composable theorem engineering. Those mechanisms matter for large formal
developments.

But for textbook-style proofs, they are often machinery for a different goal.
The user-facing task is usually not to program a proof object in a general proof
environment. It is to check whether the next ordinary mathematical fact follows
from the current assumptions, previous facts, definitions, and routine
relationships.

This is why speed matters as more than an implementation detail. Litex is not
trying to make Lean's pipeline faster; it changes the default proof interface.
Proofs are checked as a growing sequence of mathematical facts, and many common
relationships are builtin. In this setting, a short feedback loop is a design
signal: the checker is doing the work that the proof script actually asks for,
without requiring the user to pass through a heavier proof-programming layer.
*For example, in a local run, more than 240 runnable examples from The Mechanics of Litex Proof checked in about 13 seconds.*

### AI Mathematical Exploration

This short feedback loop is especially relevant for exploratory mathematical
formalization. Verification efficiency is not only the time spent inside one
checker call. It is the whole loop: write a candidate statement, run it, read
the exact failure, make the next small correction, and grow the local
mathematical background when a missing rule or definition is discovered.

The objective is not to make an AI agent emit fewer tokens for its own sake.
It is to make the accepted artifact cheaper for the next human or agent to
understand, repair, and reuse. Generated proof machinery may be disposable;
the mathematical explanation and its auditable dependencies should not be.

Litex is deliberately friendly to that loop. It runs directly, has a small
surface syntax, and lets many library-like background facts be added as ordinary
Litex statements, builtin rules, or infer rules. This makes it practical to try
many natural formulations and turn failures into small language, library, rule,
or diagnostic improvements. Lean remains much stronger when the task depends on
Mathlib, advanced abstractions, or production formalization; the point is that
Litex can be a faster exploratory verification layer before a development
settles into its final form.

### Federated Mathematical Collaboration

A mature shared library such as Mathlib is a major advantage of Lean. It gives
many contributors common definitions, theorem interfaces, automation, and
reviewed engineering conventions. Litex does not treat that kind of common
vocabulary as a problem to eliminate.

It explores a different collaboration boundary for source-facing mathematics.
An author should be able to formalize a textbook chapter, paper, or local
mathematical development using the definitions and proof route that make sense
there, then expose a small public interface: named definitions, named theorems,
and explicit trusted assumptions where proof debt remains. A later development
can cite that interface without copying the whole source or forcing its local
mathematics into one globally chosen presentation.

```text
source A definitions -> source A theorems -> named cite interface
                                             |
source B definitions -> bridge theorem ------+-> source B proof
```

Different definitions of the same mathematical object can therefore coexist.
They become interoperable only through an explicit, checked bridge theorem;
sharing a name is not enough. This preserves a source's natural argument while
making the point of connection visible to readers and to the verifier.

This is federation, not an absence of standards. Facts that become stable,
fully checkable interfaces used by several independent source families belong
in explicit namespace-qualified `std` packages. Source-specific supporting
facts instead belong in a source-local cite package. The promotion criteria are
documented in the [Reusable Mathematics Policy](Reusable_Mathematics_Policy.md).

The guarantee is deliberately conditional and auditable: a citation is checked
relative to the Litex version, the imported source, builtin rules, and every
visible `trust` boundary in its proof path. That is not yet a claim that Litex
has a complete decentralized package ecosystem. It is a design direction in
which independently authored mathematical sources can be reused through small,
inspectable, reproducibly checked interfaces.

### Message Output Explains Each Step

Lean's most visible interactive output is often state-oriented: after a command,
the user looks at the current hypotheses and goals, then chooses the next proof
command. Litex's message output is more transition-oriented: after a statement,
it reports how the verified environment changed from the previous state to the
current state.

That means Litex output is not only "here is the current context." It is also
"this statement added this definition or fact, these extra facts were inferred,
and this accepted fact was proved by this route." This matters because Litex
asks the user to write facts directly. If the checker closes routine steps
automatically, that automation should be inspectable. The output therefore
records statement effects, newly stored known facts, inferred facts, and
provenance for accepted facts.

The smallest possible example already shows the difference. In Litex, the
program is just the proposition:

```litex
1 = 1
```

One JSON-shaped Litex output for that statement is:

```json
{
  "result": "success",
  "type": "equality fact",
  "line": 1,
  "statement": "1 = 1",
  "verification": {
    "type": "builtin rule",
    "rule": "same expression on both sides"
  },
  "phases": {
    "affect_environment": {
      "status": "success",
      "effects": [
        {
          "kind": "store_fact",
          "fact": "1 = 1",
          "reason": "proved statement"
        }
      ]
    }
  }
}
```

The corresponding Lean code is also tiny:

```lean
example : 1 = 1 := by
  rfl
```

In a Lean-style interactive view, the output before `rfl` is the current goal:

```text
⊢ 1 = 1
```

After `rfl`, the state is closed:

```text
No goals
```

<!-- litex:skip-test -->
```litex
statement:
  1 = 1
verification:
  builtin rule:
    same expression on both sides
environment effect:
  store fact 1 = 1
  reason: proved statement
```

```lean
current proof state:
|- 1 = 1

after rfl:
No goals
```

**What differs.** Lean's interaction usually helps the user inspect the current
proof state. Litex's output emphasizes the delta: what the last statement added,
which facts it inferred, and how the accepted facts were obtained. That makes
successful automation inspectable instead of opaque.

### Known Facts By Matching

<!-- litex:skip-test -->
```litex
abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =>:
        $p(a2, b2)
```

```lean
example (p : α → β → Prop)
    {a a2 : α} {b b2 : β}
    (ha : a = a2) (hb : b = b2) (hp : p a b) :
    p a2 b2 := by
  subst a2
  subst b2
  exact hp
```

**What differs.** Litex reuses known facts by equality-compatible matching. Lean usually transports the fact explicitly.

```litex
abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =>:
        $p(a2, b2)
```

### Known `forall` Facts

<!-- litex:skip-test -->
```litex
abstract_prop p(x)
forall:
    forall x R:
        $p(x)
    =>:
        $p(2)
```

```lean
example (p : ℝ → Prop) (h : ∀ x : ℝ, p x) : p 2 := by
  exact h 2
```

**What differs.** Litex matches the goal against known `forall` facts. Lean applies the universal hypothesis explicitly.


### Known `forall` Matching Inside Anonymous Functions

This example is a sharper version of `forall` reuse. The local fact says
that a predicate `p` is closed under pointwise addition of real-valued
functions. Litex first proves the inner sum function, then matches the final
anonymous-function body against the same known fact again.

<!-- litex:skip-test -->
```litex
abstract_prop p(x)

claim:
    ? forall a, b, c fn(x R) R:
        forall f, g fn(x R) R:
            $p(f)
            $p(g)
            =>:
                $p(fn(x R) R {f(x) + g(x)})
        $p(a)
        $p(b)
        $p(c)
        =>:
            $p(fn(x R) R {a(x) + (b(x) + c(x))})
    $p(fn(x R) R {b(x) + c(x)})
```

```lean
import Mathlib

example (p : (ℝ → ℝ) → Prop)
    (h : ∀ f g : ℝ → ℝ, p f → p g → p (fun x => f x + g x))
    (a b c : ℝ → ℝ) (pa : p a) (pb : p b) (pc : p c) :
    p (fun x => a x + (b x + c x)) := by
  have hbc : p (fun x => b x + c x) := h b c pb pc
  exact h a (fun x => b x + c x) pa hbc
```

**What differs.** In the final Litex goal, the matcher treats
`a(x) + (b(x) + c(x))` as an instance of `f(x) + g(x)`. Since `g` is applied to
the full anonymous-function parameter list `x`, Litex may infer
`g := fn(x R) R {b(x) + c(x)}`. Lean can express the same proof, but the user
normally supplies the intermediate function and applies the universal
hypothesis explicitly.


---

## Builtin Mathematical Background

Ordinary mathematics uses many small background relationships: equality, order, membership, set predicates, function application, tuple projection, finite enumeration, arithmetic normalization, and so on. Each relationship is usually simple. The total number of interactions is large.

Litex builds many of these elementary relationships into the language layer. This makes short mathematical scripts less dependent on a separate globally distributed library for basic steps. It can matter especially in areas where the needed background mathematics is not yet easy to express or package naturally in a type-theoretic library.

This is also why Litex can make a textbook development feel less like library
navigation. The basic mathematical ground is already available to the checker,
so a beginner can often write the next line of the proof instead of first
learning which large package, namespace, theorem name, coercion, or tactic
encodes that move.

Lean's strength is different. Mathlib is a broad, mature, community-built mathematical library. For large formalization projects, advanced abstractions, and deep theorem reuse, that ecosystem is a major advantage.

The design difference is where routine mathematical background lives:

- In Litex, many basic relationships are part of the checker background.
- In Lean, much of the power comes from the library, tactics, and explicit proof terms that users can compose.

---

## Set Theory As A Larger Example

Set theory is a good place to see Litex's design. Litex's surface language treats sets, membership, finite set displays, set-builder domains, power sets, subsets, and cardinality-style facts as basic mathematical material. Lean can express all of these, but the user more often chooses a concrete encoding such as `Set`, `Finset`, subtype, decidable membership, coercions, and library lemmas.

### Nested Finite Sets

<!-- litex:skip-test -->
```litex
{1, 2} $in {{}, {1, 2}}
```

```lean
import Mathlib
example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp
```

**What differs.** Litex writes nested set membership directly. Lean makes the outer element type explicit: `Set (Set ℕ)`.

```litex
{1, 2} $in {{}, {1, 2}}
```

### Finite Enumeration

<!-- litex:skip-test -->
```litex
forall i1 {1, 2}:
    i1 = 1 or i1 = 2
```

```lean
import Mathlib
example {i1 : ℕ} (hi : i1 ∈ ({1, 2} : Finset ℕ)) : i1 = 1 ∨ i1 = 2 := by
  simpa using hi
```

**What differs.** Litex unfolds the finite display as possible values. Lean uses `Finset ℕ` and simplification.

```litex
forall i1 {1, 2}:
    i1 = 1 or i1 = 2
```

### Power Set Membership

<!-- litex:skip-test -->
```litex
{1, 2} $in power_set({1, 2, 3})
```

```lean
import Mathlib
example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  intro x hx
  simp at hx
  simp [hx]
```

**What differs.** Litex writes power-set membership directly. Lean often proves the underlying subset relation.

```litex
{1, 2} $in power_set({1, 2, 3})
```

### Subset Facts Verify Membership Goals

<!-- litex:skip-test -->
```litex
forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

```lean
example {α : Type} {A B : Set α} (hAB : A ⊆ B) {x : α} (hx : x ∈ A) : x ∈ B := by
  exact hAB hx
```

**What differs.** Litex can verify the one-step membership consequence on
demand from the known owner set and subset relation. It does not need to
materialize the lifted membership first. Lean applies the subset hypothesis as
a function.


### Unequal Cardinalities Rule Out Equality

<!-- litex:skip-test -->
```litex
by contra:
    ? {1, 2, 3} != {1, 2}
    finite_set_size({1, 2, 3}) = 3
    finite_set_size({1, 2}) = 2
    finite_set_size({1, 2, 3}) = finite_set_size({1, 2})
    impossible 3 = 2
```

```lean
import Mathlib
example : ({1, 2, 3} : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by
  intro h
  have hcard := congrArg Finset.card h
  norm_num at hcard
```

**What differs.** Litex follows the finite-set-size contradiction directly. Lean uses `Finset.card`, `congrArg`, and simplification.

```litex
by contra:
    ? {1, 2, 3} != {1, 2}
    finite_set_size({1, 2, 3}) = 3
    finite_set_size({1, 2}) = 2
    finite_set_size({1, 2, 3}) = finite_set_size({1, 2})
    impossible 3 = 2
```

These examples are intentionally larger than `1 + 1 = 2` but still much smaller than the prime-number case study. They show why set theory is a natural foundation for Litex: many common mathematical objects are already first-class enough that the proof can stay close to the sentence a mathematician would write.

---

## Case Study: Infinitely Many Primes

Both systems can express the classic proof that there are infinitely many primes:

1. Start with a bound `a`.
2. Build the product `1 * 2 * ... * a`.
3. Consider `product + 1`.
4. Take a prime divisor `k` of that number.
5. If `k <= a`, then `k` divides the product, so `product + 1` has remainder `1` modulo `k`, contradicting that `k` divides it.
6. Therefore `k > a`.

<!-- litex:skip-test -->
```litex
# `$prime(a)` is native. Its symbolic contract is `2 <= a` together with
# `a % b != 0` for every `b` in `range(2, a)`.

claim:
    ? forall a N+:
        forall n, k N+:
            k <= n
            =>:
                product(1, n, fn(x N+) N+ {x}) % k = 0
        forall n N+:
            2 <= n
            =>:
                exist k N+ st {$prime(k), n % k = 0}
        forall n N+:
            n <= product(1, n, fn(x N+) N+ {x})
        2 <= a
        =>:
            exist k N+ st {k > a, $prime(k)}
    2 <= a <= product(1, a, fn(x N+) N+ {x}) <= product(1, a, fn(x N+) N+ {x}) + 1
    obtain k from exist k N+ st {$prime(k), (product(1, a, fn(x N+) N+ {x}) + 1) % k = 0}
    by cases:
        ? k > a
        case k <= a:
            product(1, a, fn(x N+) N+ {x}) % k = 0
            (product(1, a, fn(x N+) N+ {x}) + 1) % k = (product(1, a, fn(x N+) N+ {x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, fn(x N+) N+ {x}) + 1) % k = 0
        case k > a
    witness exist k N+ st {k > a, $prime(k)} from k
```

```lean
import Mathlib
example (N : ℕ) : ∃ p ≥ N, Nat.Prime p := by
  have hN0 : 0 < N ! := by exact Nat.factorial_pos N
  have hN2 : 2 ≤ N ! + 1 := by omega
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ N ! + 1 :=
    Nat.exists_prime_and_dvd hN2
  obtain ⟨k, hk⟩ := hpN
  use p
  constructor
  · by_contra hlt
    have hp_dvd_factorial : p ∣ N ! := Nat.Prime.dvd_factorial hp (Nat.le_of_not_gt hlt)
    have hp_dvd_one : p ∣ 1 := by
      have hp_dvd_sum : p ∣ (N ! + 1) - N ! := Nat.dvd_sub hpN hp_dvd_factorial
      simpa using hp_dvd_sum
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  · exact hp
```

**What differs.** Litex puts the background lemmas in the premise of the `claim` and keeps the final argument as a direct proof spine. Lean often interleaves lemmas with proof-state transformations. Both carry real proof burden; they organize it differently.

What Litex is trying to show is different. The user states the facts and witnesses they want, while the checker matches those targets against builtin rules and known information. Chains expose order/transitivity goals, `obtain ... from exist ...` exposes an existential pattern, `by cases` exposes branches, and `witness` exposes the object that should close an existential goal.

> The `prop` block defines the vocabulary. The premise of the `claim` lists the background mathematics. The main proof is the part after that premise.

> The Lean example above is adapted from *Mathematics in Lean*, which is an excellent introduction to Lean and formalized mathematics. It takes 6 pages to teach the reader how to prove this simple example. The point here is not that the Lean version is bad; it is carefully teaching the reader how two language philosophies can be used to express the same proof.


---

## More Technical Differences

This section is for readers who already care about theorem-prover foundations. These differences are not the first thing a beginner needs, but they explain why Litex and Lean feel different at a deeper level.

### Facts Are Not Objects

Litex keeps objects and facts separate. A `prop` defines a predicate form. Applying that predicate to objects creates a fact.

This is not Litex:
```text
forall P Prop:
    # proof body omitted
```

**What differs.** Lean can quantify over `P : Prop` and treat proofs as terms. Litex does not make facts ordinary objects, keeping the object/fact split explicit.

### Proposition Composition Uses a Canonical Surface Grammar

Lean propositions compose recursively. A universal proposition, a conjunction,
and a disjunction are all propositions again, so Lean can directly write a
shape such as:

```lean
example (α : Type) (P : α → Prop) (Q R : Prop) (h : ∀ x, P x) :
    (∀ x, P x) ∨ (Q ∧ R) :=
  Or.inl h
```

Litex makes a smaller parser and AST choice. A flat `and` contains atomic
facts, while the outer `or` collects atomic, chain, or completed flat-`and`
branches. A `forall` is not one of those `or` branch shapes. Consequently, the
following anonymous recursive shape is not Litex syntax:

```text
(forall x R: x = x) or (1 = 1 and 2 = 2)
```

This is a surface-expressiveness trade-off, not a claim that the mathematical
proposition is meaningless. A closed compound proposition can first be given
a zero-parameter `prop` name. The resulting prop call is atomic and can occupy
the outer branch position:

```litex
prop all_reals_reflexive():
    forall x R:
        x = x

by def $all_reals_reflexive()
$all_reals_reflexive() or 1 = 1 and 2 = 2
```

The `prop` definition makes `$all_reals_reflexive()` definitionally equivalent
to its `forall` body; it does not assert either side merely by being declared.
Here `by def` verifies the body and stores the atomic call. If the compound
subclaim has free mathematical objects, those objects should be parameters of
the named `prop` rather than hidden in a zero-parameter declaration.

**What differs.** Lean keeps arbitrary anonymous proposition composition in
the term language. Litex keeps a canonical set of directly parsed fact shapes
and asks the user to name a compound subclaim when it must cross that shape
boundary. The named call is still a fact interface, not a first-class `Prop`
object or a proof term.

### Statements And Proofs As Values is not Litex

This difference goes further than `P : Prop`. In Lean, propositions and proofs live inside the same type-theoretic world as other terms. A previous theorem, a proof of a proposition, or a function from one proof to another can be passed as an argument to a later theorem.

This is not Litex:
```text
have h = (x = 2)
some_statement(h)
```

**What differs.** Lean supports higher-order proof programming: propositions, proofs, and theorem arguments can be manipulated as terms. Litex keeps statements as proof actions and facts as context information, not as first-class objects.

---

## Fair Trade-Offs

Use Lean when you need:

- Mathlib coverage and a mature theorem-proving ecosystem;
- a large professional user community with accumulated examples and expertise;
- advanced type-theoretic abstractions;
- production-grade formalization;
- dependent induction, custom recursors, and deep automation;
- community-proven tooling for large projects.

Use Litex when you want:

- a set-theoretic surface close to ordinary mathematics;
- direct mathematical objects such as sets, functions, tuples, and set-builders;
- direct facts rather than many named proof terms;
- proof statements that look like common mathematical moves;
- builtin relationships among basic mathematical objects;
- matching and substitution that reduce proof-engine bookkeeping;
- proof-trail verification for early failure detection.

Both systems require mathematics. Litex is not a way to avoid proving things. It changes where many routine steps live: more basic relationships are built into the language, and more reuse happens through fact matching and substitution. Lean gives the user a much more general engine, backed by a rich library and a large expert community; Litex tries to make common mathematical reasoning feel direct.

---

## Ongoing Project: Compiling Litex To Lean

The current experiment runs the Litex verifier first and then handles only its
declared rational-equality subset:

```text
Litex source
  -> execute and verify with Litex
  -> retain a closed direct equality or one universal equality over R
  -> recursively lower each side to (numerator, denominator)
  -> emit a named Lean theorem using norm_num, ring, or field_simp; ring
  -> ask Lean and Mathlib to check the generated file
```

### Chosen Contract: Faithful Materialization

The intended correctness-oriented backend should faithfully materialize the
verified execution, rather than merely ask Lean to rediscover the final result.
Every source fact and every inferred fact stored by Litex should appear as a
Lean declaration or local `have`. Later facts should refer to those generated
proofs explicitly:

```lean
have haA : a ∈ A := ...
have hAB : A ⊆ B := ...
have haB : a ∈ B := hAB haA
```

This output is deliberately verbose. Its primary purpose is not to produce
small, idiomatic Lean source; it is to provide an independently checked,
human-readable audit of what the Litex verifier did. A reader can inspect the
Lean proof for each individual fact and the proof-term connection between
facts. If either a fact or a dependency edge is invalid, Lean rejects the
generated file at a local, identifiable point.

The faithful artifact should preserve:

- every accepted source fact;
- every inferred fact added to the Litex environment, including unused ones;
- the rule and earlier facts used to justify each generated proof;
- lexical scope, assumptions, witnesses, branches, and contradiction scopes;
- stable source, fact, rule, and dependency IDs linking Litex output to Lean.

An optimized dependency slice may eventually be useful as a secondary export,
but it should not replace the full artifact used for correctness auditing.
Generated size is an acceptable cost for that artifact because the aim is
transparency and independent checking, not handwritten-code quality.

There are several other possible correspondence designs:

| Design | What Lean checks | Limitation for the Litex audit |
| --- | --- | --- |
| final-result-only export | one final theorem | does not expose intermediate inference or environment changes |
| statement reconstruction | each source statement is translated, then Lean tactics rediscover a proof | checks the translated claims but not the proof route taken by Litex |
| used dependency slice | only inferred facts needed by a later result are emitted | omits successful verifier actions and facts that happened not to be used |
| faithful materialization | every stored source and inferred fact, with explicit dependencies | chosen design; larger output |
| structured proof-certificate replay | Lean checks a machine-readable Litex trace with a small certificate checker | a useful future implementation of faithful materialization, but requires a stable trace schema and a reviewed checker |
| deep semantic embedding | Litex syntax, environments, rules, and execution are defined in Lean and the verifier is related to that model | strongest route toward a general soundness theorem, but a substantially larger formalization project |

These designs are not all mutually exclusive. The compiler can emit readable
`have` blocks from a structured proof certificate, while a feature-conformance
suite checks each Rust verifier rule against a small generated Lean example.
The correspondence can then be tested at several levels:

1. **Representation:** each supported Litex object and proposition lowers to
   the intended Lean type and proposition.
2. **Local rule:** each builtin, matching, substitution, definition, or
   quantifier rule produces a Lean-checkable proof term.
3. **Dependency edge:** each inferred fact refers to the exact earlier facts
   that justify it.
4. **Environment transition:** facts enter and leave scope in Lean where they
   enter and leave the Litex environment.
5. **Whole execution:** the complete generated file checks without `sorry`,
   `admit`, or generated axioms.

Passing all five levels gives strong executable evidence for each supported
Litex run and makes disagreements locally auditable. It is still important not
to overstate the result: checking generated traces does not by itself prove a
universal soundness theorem about every Rust execution. Such a theorem would
also require a formal semantics and a proof relating the implementation to it.
The faithful Lean artifact instead certifies the particular materialized run,
within the supported lowering and with every trust boundary disclosed.

The faithful materialization contract above is a future target, not current
coverage. The actual experiment has one representative mapping.

Litex:

```text
forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x
```

Generated Lean ends with:

```lean
theorem litex_rational_1 (a b x : ℝ) (h1 : x ≠ 0) :
    (a + b) / x = a / x + b / x := by
  calc
    (a + b) / x = (a + b) / x := by
      solve
        | field_simp [h1]
        | field_simp [h1] <;> ring
    _ = (a * x + b * x) / (x * x) := by
      solve
        | field_simp [h1]
        | field_simp [h1] <;> ring
    _ = a / x + b / x := by
      solve
        | field_simp [h1]
        | field_simp [h1] <;> ring
```

Closed numeric equalities use `norm_num`; variable-only polynomial equalities
use `ring` directly. The recursive lowering handles numbers, real atoms,
addition, subtraction, multiplication, division, and literal natural powers.
For example, the left-associative expression `1 / 2 / 3 / 4` lowers
structurally to `1 / ((2 * 3) * 4)`, which `norm_num` can compare with
`1 / 24`. Definitions, named theorem bodies, claims, conjunctions,
transcendental and complex objects, implicit denominator evidence,
complete-module translation, and exact proof-path replay are intentionally
rejected. No `sorry`, `admit`, or Lean axiom is generated.

## Appendix: Foundations And Design Intent

Litex is less interested in redefining every basic concept from a deeper user-facing abstraction, and more interested in the relationships between the concepts that ordinary mathematics already uses. Equality supports substitution. Membership in a number set gives sign or nonzero information. Subset facts give membership consequences. Function-domain facts make applications well-defined.

For this reason, Litex treats its builtin mathematical concepts as primitive at the surface level. Sets, elements, functions, relations, numbers, order, membership, and equality are part of the shared mathematical vocabulary of the language. They are not first presented to the user as consequences of a more abstract layer that must be unfolded before ordinary reasoning can begin.

Lean makes a different foundational choice. Its kernel is based on dependent type theory, which is more abstract and more general than the set-theoretic picture used in much informal mathematics. Type theory can encode set theory and many other mathematical structures, and Lean can support highly abstract mathematics such as category theory in libraries on top of that kernel. In this sense, Lean is stronger for foundational flexibility, large abstractions, and developments that need precise control over the underlying representation.

This does not mean one system is simply better at mathematics. Lean is a powerful proof assistant and functional programming language with a very general foundation. It also has the practical advantage of Mathlib, an active expert community, and years of accumulated formalization practice. Litex is intentionally narrower: it aims to make ordinary mathematical proof scripts read like checked facts over familiar concepts. The design cost is less foundational generality; the design benefit is a surface where common mathematical relationships are builtin and directly usable.

Put another way: Lean is a formal mathematics ecosystem; Litex is exploring a
readable verification layer for ordinary mathematical reasoning, local proof
feedback, and AI-assisted repair loops.
