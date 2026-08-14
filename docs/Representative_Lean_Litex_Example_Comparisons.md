# Representative Lean–Litex Example Comparisons

Created and maintained by Jiachen Shen.

Try the examples in browser:
https://litexlang.com/doc/Representative_Lean_Litex_Example_Comparisons

Markdown source:
https://github.com/litexlang/golitex/blob/main/docs/Representative_Lean_Litex_Example_Comparisons.md

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

This page presents a small set of representative examples rather than a
complete language comparison. Lean and Litex both make mathematics
machine-checkable, but expose different default interfaces:

- Lean provides dependent type theory, proof terms, tactics, Mathlib, mature
  tooling, and a large community.
- Litex provides a fact-oriented, set-theoretic surface in which users usually
  write the next mathematical fact and the checker searches for its support.

These are differences of emphasis, not absolute capability boundaries. Lean
can support concise automation and forward reasoning; Litex also has explicit
goals, named theorems, case splits, induction, and other structured proof
forms. The Lean proofs below are intentionally explicit enough to expose the
comparison, not claims about the shortest Lean proof.

Every Litex code block on this page is self-contained and checked by the
repository documentation test. The Lean blocks use Mathlib directly and do not
depend on the *Mathematics in Lean* book package. Syntax and automation in
either project may continue to evolve.

For the larger design argument, see the [Litex
Blueprint](https://litexlang.com/doc/Litex_Blueprint). For language details,
see the [Manual](https://litexlang.com/doc/Manual) and [System
Map](https://litexlang.com/doc/Litex_System_Map). The current Litex-to-Lean
experiment has a deliberately narrow boundary documented in the
[compiler README](https://github.com/litexlang/golitex/blob/main/src/compile_to_lean/README.md).

The complete `Group` comparison is kept in the Blueprint rather than repeated
here. This page concentrates on examples that add distinct evidence.

---

## 1. Direct Facts, Short Estimates, and Typed Domains

### Direct local consequences

Suppose a real number is known to equal `2`. In Litex, that fact enters the
local context and the desired consequences are stated directly:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

An explicit Lean proof can name the assumption and direct the two rewrites:

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

The mathematical content is the same. The Litex source foregrounds the two
results; its checker supplies substitution and arithmetic support. The Lean
source foregrounds a route for constructing the conjunction, while the
kernel ultimately checks the resulting proof term.

<a id="ai-lowers-generation-cost-not-automatically-understanding-cost"></a>

### Keep the mathematical estimate visible

Suppose `0 < epsilon <= 1`, `abs(x) < epsilon`, and `abs(y) < epsilon`. The
reason that `abs(x * y) < epsilon` is the short estimate

\[
|xy| = |x||y| < \varepsilon^2 \leq \varepsilon.
\]

Here is an explicit Lean calculation:

```lean
import Mathlib

example (x y epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (epsilon_le_one : epsilon ≤ 1)
    (hx : |x| < epsilon)
    (hy : |y| < epsilon) :
    |x * y| < epsilon := by
  rw [abs_mul]
  calc
    |x| * |y| < epsilon * epsilon := by
      nlinarith [abs_nonneg x, abs_nonneg y]
    _ ≤ epsilon * 1 := by
      exact mul_le_mul_of_nonneg_left epsilon_le_one (le_of_lt epsilon_pos)
    _ = epsilon := mul_one epsilon
```

The corresponding Litex tracer keeps one general product-monotonicity premise
in the context and leaves the durable argument as the recognizable estimate:

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

AI can generate either proof cheaply. The interface question is what remains
easy for a mathematician to inspect and edit afterward. Litex aims to keep the
mathematical spine in source while its output records whether each step came
from a known fact, a universal instance, a definition, a builtin rule, a named
theorem, or an explicit assumption.

### Domains carried by mathematical objects

Litex can place a condition directly in an object's declared domain and then
use that condition when the object is passed to a function:

```litex
forall x {y R: y > 0}:
    x > 0

have fn positive_successor(x R: x > 0) R = x + 1

positive_successor(1) = 2
```

One natural Lean representation packages the real value and proof as a
subtype:

```lean
import Mathlib

example (x : {y : ℝ // y > 0}) : (x : ℝ) > 0 := by
  exact x.property

def positiveSuccessor (x : {y : ℝ // y > 0}) : ℝ := x.val + 1

example : positiveSuccessor ⟨1, by norm_num⟩ = 2 := by
  norm_num [positiveSuccessor]
```

Litex keeps the condition where a mathematician normally writes the domain.
Lean's subtype makes the dependency precise inside its type-theoretic object
language. Neither system eliminates the obligation that the argument satisfy
the condition; the obligation appears at a different surface layer.

---

## 2. Scalar Multiplication Preserves Convergence

Suppose a real sequence `s` converges to `a`. Multiplying every term by a real
constant `c` should produce a sequence converging to `c * a`.

The Lean proof below uses the usual epsilon definition. It splits on `c = 0`;
in the nonzero case it applies convergence at `epsilon / |c|` and uses the
absolute-value product law.

```lean
import Mathlib

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
    |c * s n - c * a| = |c| * |s n - a| := by
      rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) :=
      mul_lt_mul_of_pos_left (hs n ngt) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
```

The Litex proof chooses `epsilon / (abs(c) + 1)`. Since the denominator is
always positive, one estimate covers both `c = 0` and `c != 0`.

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

Both proofs use the same core idea: obtain a tail bound for a smaller positive
tolerance, reuse the same cutoff, and estimate the scaled absolute difference.
The Lean proof exposes a case split, named hypotheses, rewriting, and library
lemmas. The Litex proof exposes nested convergence facts, a witness, and the
inequality chain, while the checker supplies routine arithmetic and definition
folding.

This does not claim that Lean requires this proof shape or cannot use the
uniform `abs(c) + 1` argument. It compares two natural ways of organizing the
same elementary analysis proof.

---

## 3. Calculation Chains

Litex treats a chain as one factual statement. For a two-equation system, the
intermediate expressions can be written in the same order as a handwritten
calculation:

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4
```

An explicit Lean proof can present the same calculations inside two named
subproofs:

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
  exact ⟨hy, hx⟩
```

The visible difference is not whether either system can express a calculation
chain. It is which parts the user normally directs: Litex asks for meaningful
intermediate equalities and searches for their support; this Lean proof names
the subresults and specifies tactics and rewrites that build them.

---

## 4. Witnesses, Contradiction, and Counterexamples

### A concrete witness

Litex places the witness values directly next to the existential statement:

```litex
witness exist a, b, c, d N+ st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

Lean packages the same values and remaining obligation through the
existential constructors:

```lean
import Mathlib

example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

The proof burden is not removed: Litex still checks that the supplied objects
belong to `N+` and satisfy the substituted equation.

### Contraposition by contradiction

The next example uses abstract predicates so that only the logical shape is
at issue:

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

Litex exposes the familiar move “assume the negated target fails and derive an
impossible fact.” Lean expresses the proof as a function from the temporary
assumption to a contradiction. Both are rigorous representations of the same
logical argument.

### A set counterexample

To show that the multiples of `4` are not the even natural numbers, `2` is the
decisive counterexample:

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

example : ({a : ℕ | a % 4 = 0} : Set ℕ) ≠
    {a : ℕ | a % 2 = 0} := by
  intro h
  have h2 : (2 : ℕ) ∈ ({a : ℕ | a % 2 = 0} : Set ℕ) := by
    norm_num
  have h4 : (2 : ℕ) ∈ ({a : ℕ | a % 4 = 0} : Set ℕ) := by
    rw [h]
    exact h2
  norm_num at h4
```

The Litex proof states the counterexample and resulting contradiction. The
Lean proof names the set equality and memberships, rewrites with the assumed
equality, and discharges the false modular fact.

---

## 5. Set-Theoretic Objects at the Surface

Nested sets, power-set membership, and subset transport can all be written as
ordinary mathematical facts in Litex:

```litex
{1, 2} $in {{}, {1, 2}}

{1, 2} $in power_set({1, 2, 3})

forall A, B set, x A:
    A $subset B
    =>:
        x $in B
```

Lean expresses the same mathematics while making the relevant ambient types
and set representation explicit:

```lean
import Mathlib

example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp

example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  simp

example {α : Type} {A B : Set α}
    (hAB : A ⊆ B) {x : α} (hx : x ∈ A) :
    x ∈ B := by
  exact hAB hx
```

Litex's surface begins with sets, objects, membership, and functions between
declared domains. Lean's surface begins with typed terms, so the examples say
`Set ℕ`, `Set (Set ℕ)`, and a general ambient type `α`. Lean's representation
is more general and deeply integrated with dependent type theory; Litex's is
intended to put the set-theoretic reading first.

### Intersections preserve inclusion

Here is an explicit unfolding proof from the sets chapter of *Mathematics in
Lean*. If `s` is a subset of `t`, intersecting both sets with the same set `u`
preserves that inclusion:

```lean
import Mathlib.Data.Set.Lattice

open Set

example {alpha : Type*} (s t u : Set alpha) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
```

The corresponding Litex fact is the mathematical statement itself:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

The mathematical argument is simply that a member of `intersect(s, u)` lies
in both `s` and `u`; subset transport puts it in `t`, hence in
`intersect(t, u)`. In Litex's default interface, a learner does not need to
remember unfolding names and proof commands such as `subset_def`, `inter_def`,
`rw`, or `simp only [mem_setOf]` just to expose that argument. This lowers the
initial learning burden and keeps this routine proof at the level of sets and
membership.

This is not a claim that Lean requires the explicit script above: Lean also
supports a shorter elementwise proof and stronger automation. It illustrates
a difference in the default division of labor. Litex's checker performs the
routine unfolding and membership transport, which also places those rules
inside Litex's implementation and audit surface; Lean lets a proof author
expose or control those steps through terms and tactics.

Structures over a carrier set are illustrated by the complete group-identity
example in the [Litex
Blueprint](https://litexlang.com/doc/Litex_Blueprint#a-small-but-complete-comparison-uniqueness-of-the-identity-in-a-group).

---

## 6. Case Study: Infinitely Many Primes

Both systems can express Euclid's argument in the following form:

1. Start with a positive bound `a`.
2. Form `1 * 2 * ... * a + 1`.
3. Choose a prime divisor `k` of that number.
4. If `k <= a`, then `k` divides the product, while the product plus one has
   remainder `1` modulo `k`, a contradiction.
5. Therefore `k > a`.

The Litex claim places the background lemmas in its premise and keeps the main
argument as a direct proof spine:

```litex
# `$prime(a)` is native. Its symbolic contract is `2 <= a` together with
# `a % b != 0` for every `b` in `range(2, a)`.

claim:
    ? forall a N+:
        forall n, d N+:
            d <= n
            =>:
                product(1, n, fn(x N+) N+ {x}) % d = 0
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
            2 <= k
            (product(1, a, fn(x N+) N+ {x}) + 1) % k = (product(1, a, fn(x N+) N+ {x}) % k + 1 % k) % k
            1 % k = 1
            (0 + 1) % k = 1 % k = 1
            (product(1, a, fn(x N+) N+ {x}) + 1) % k = (product(1, a, fn(x N+) N+ {x}) % k + 1 % k) % k = (0 + 1) % k = 1
            0 = (product(1, a, fn(x N+) N+ {x}) + 1) % k = 1
            impossible 0 = 1
        case k > a
    witness exist prime_larger N+ st {prime_larger > a, $prime(prime_larger)} from k
```

A Lean proof can use Mathlib's factorial and prime-divisor interfaces:

```lean
import Mathlib

example (N : ℕ) : ∃ p ≥ N, Nat.Prime p := by
  have hN0 : 0 < Nat.factorial N := Nat.factorial_pos N
  have hN_ne_one : Nat.factorial N + 1 ≠ 1 := by omega
  obtain ⟨p, hp, hpN⟩ :
      ∃ p : ℕ, Nat.Prime p ∧ p ∣ Nat.factorial N + 1 :=
    Nat.exists_prime_and_dvd hN_ne_one
  use p
  constructor
  · by_contra hlt
    have hp_le_N : p ≤ N := by omega
    have hp_dvd_factorial : p ∣ Nat.factorial N :=
      (Nat.Prime.dvd_factorial hp).2 hp_le_N
    have hp_dvd_one : p ∣ 1 := by
      have hp_dvd_sum : p ∣ (Nat.factorial N + 1) - Nat.factorial N :=
        Nat.dvd_sub hpN hp_dvd_factorial
      simpa using hp_dvd_sum
    exact Nat.Prime.not_dvd_one hp hp_dvd_one
  · exact hp
```

Litex makes the assumed background mathematics visible at the front of the
claim, then shows `obtain`, a case split, the modular calculation, and the
witness. Lean draws on a mature theorem library and constructs the result
through named divisibility facts. The two examples do not have identical
library boundaries, so line count is not a meaningful score; the comparison
is about the shape of the remaining proof text.

---

## 7. A Technical Boundary: Facts Are Not First-Class Objects

Lean propositions and proofs inhabit its type-theoretic term language. Lean
can quantify over `P : Prop`, pass theorem proofs as arguments, and recursively
compose propositions. Litex deliberately separates mathematical objects from
facts: a `prop` declaration defines a fact interface, and a call to that
predicate is a fact rather than an ordinary object.

For example, Lean can directly place a universal proposition inside a
disjunction:

```lean
example (α : Type) (P : α → Prop) (Q R : Prop) (h : ∀ x, P x) :
    (∀ x, P x) ∨ (Q ∧ R) :=
  Or.inl h
```

Litex uses a smaller canonical surface grammar. A flat `and` contains atomic
facts, and an outer `or` accepts atomic, chain, or completed flat-`and`
branches; a `forall` is not directly one of those branch shapes. Therefore
this anonymous recursive form is not Litex syntax:

```text
(forall x R: x = x) or (1 = 1 and 2 = 2)
```

A closed compound fact can instead receive a predicate name. Its call is
atomic and can occupy the outer branch position:

```litex
prop all_reals_reflexive():
    forall x R:
        x = x

by def $all_reals_reflexive()

$all_reals_reflexive() or 1 = 1 and 2 = 2
```

The `prop` declaration makes `$all_reals_reflexive()` definitionally
equivalent to its body; declaration alone does not assert the call. The `by
def` line verifies the body and stores the atomic fact. If a compound subclaim
has free mathematical objects, those objects should be parameters of the
named predicate.

Similarly, these higher-order proof-programming shapes are not Litex:

```text
forall P Prop:
    # proof body omitted

have h = (x = 2)
some_statement(h)
```

This is a real expressiveness trade-off. Lean offers a highly general term
language for propositions and proofs. Litex keeps a narrower object/fact split
and asks users to name compound subclaims when they cross the directly parsed
fact shapes. The benefit sought is a smaller, more canonical mathematical
surface; the cost should be stated plainly rather than treated as an
implementation detail.

---

## Reading the Comparison Fairly

The examples support a limited conclusion: Litex can keep many elementary
proofs close to a sequence of mathematical facts while moving routine
matching, substitution, and small builtin steps into the checker. They do not
show that Litex has Lean's generality, library coverage, kernel architecture,
or production experience.

Litex also does not remove a trusted computing base. Its checker, builtin and
inference rules, imported assumptions, and every explicit `trust` or `axiom`
matter to the result. A short source file is useful only when the checker
reports enough provenance for accepted steps and the implementation remains
open to tests and audit.

Use the following documents for questions intentionally kept out of this
example collection:

- [Litex Blueprint](https://litexlang.com/doc/Litex_Blueprint): design goals
  and the complete `Group` comparison;
- [Manual](https://litexlang.com/doc/Manual): syntax and proof forms;
- [System Map](https://litexlang.com/doc/Litex_System_Map): parser, verifier,
  runtime, and trust boundaries;
- [Litex-to-Lean compiler
  README](https://github.com/litexlang/golitex/blob/main/src/compile_to_lean/README.md):
  the exact supported compilation subset and current limitations.
