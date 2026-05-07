# Litex vs Lean

Jiachen Shen and The Litex Team, 2026-05-07. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean.md

## Two styles of formal mathematics

Litex and Lean are both attempts to make mathematical reasoning checkable by a computer. They are not trying to be the same language.

Lean is a mature theorem prover with a powerful type-theoretic foundation, a large ecosystem, and Mathlib, one of the most impressive formal mathematics libraries in the world. Litex is much younger and more experimental. Its goal is narrower: make many everyday mathematical arguments look close to the way people write them on paper, while still checking them strictly.

So this page is not a ranking. It is a comparison of style.

- Lean exposes a very general proof engine. The user works with theorem statements, hypotheses, terms, proof states, tactics, and library lemmas.
- Litex exposes a more mathematical surface. The user writes objects, facts, and statements, and the checker tries builtin rules, known facts, and known `forall` facts by matching and substitution.

The trade-off is real. Lean is stronger for large formal developments and advanced abstractions. Litex aims to be easier to read and easier to start using for ordinary mathematics.

---

## The main difference

The smallest useful comparison is this:

**Litex**

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

**Lean**

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

**What differs.** Lean can prove this very well, and often very shortly. The difference is the level of interaction. In Lean, the user names the hypothesis `h`, creates intermediate facts, rewrites with `rw [h]`, and asks `norm_num` to finish numeric goals. In Litex, the user writes the facts directly. The checker remembers `x = 2`, substitutes it when a later goal matches, and closes the arithmetic goals.

This difference appears again and again:

- **Foundation.** Litex presents a set-theoretic surface: sets, elements, functions, tuples, relations, and facts. Lean is based on dependent type theory and exposes more type-level structure.
- **Surface language.** Litex statements are close to ordinary math prose: `forall`, `exist`, `have`, `claim`, `witness`, `by cases`. Lean has a precise theorem-and-proof-state workflow.
- **Less proof-engine instruction.** Litex uses matching, substitution, and builtin relationships among basic mathematical concepts to find routine proof paths. In many everyday steps, the user does not need to tell the checker exactly which lemma or tactic proves the goal.
- **Less dependence on a standard library for basic steps.** Litex builds many elementary relationships into the language layer. This can matter in areas where the needed background mathematics is not yet easy to express or package naturally in a type-theoretic library.

---

## Calculation and rewriting

### Visible calculation chains

**Litex**

```litex
forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4
```

**Lean**

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

**What differs.** Both languages can either show the intermediate algebra or delegate it to automation. Lean can solve the original goals with `linarith`, and Litex could also package a similar linear-arithmetic pattern as a builtin rule or user theorem. Litex is also less dependent on importing a broad standard library for this kind of basic algebra: many routine arithmetic and equality relationships are already part of its builtin background. The comparison here is about the visible style: Litex's calculation chain is a direct factual statement, while Lean's explicit version writes the same path through named intermediate goals, `calc`, rewrites, and tactics.

### Routine arithmetic

**Litex**

```litex
1 + 1 = 2
```

**Lean**

```lean
import Mathlib

example : 1 + 1 = 2 := by
  norm_num
```

**What differs.** In Litex, basic arithmetic is part of the checker background. In Lean, the same result is usually discharged by a tactic. The mathematical fact is the same; the proof interface is different.

---

## Functions and domains

### Mixed-domain functions

**Litex**

```litex
have fn f(x R, y Z) R = x * y

f(1, 2) = 1 * 2 = 2
```

**Lean**

```lean
import Mathlib

def f (x : ℝ) (y : ℤ) : ℝ := x * (y : ℝ)

example : f 1 2 = 2 := by
  norm_num [f]
```

**What differs.** Litex writes the mixed-domain function in the same line as its formula. Lean makes the types and coercion explicit, which is more general and precise, but less like a blackboard definition.

### Restricted domains

**Litex**

```litex
have fn g(x R: x > 0) R = x + 1

g $in fn(x R: x > 0) R
```

**Lean**

```lean
import Mathlib

def g (x : {x : ℝ // x > 0}) : ℝ := x.val + 1

example : g ⟨1, by norm_num⟩ = 2 := by
  norm_num [g]
```

**What differs.** In Litex, the domain condition stays next to the variable. In Lean, one natural encoding is a subtype, which is very expressive but introduces another abstraction for the user to learn.

### Piecewise definitions

**Litex**

```litex
have fn h(x R) R :
    case x = 2: 3
    case x != 2: 4

h(2) = 3
```

**Lean**

```lean
import Mathlib

noncomputable def h (x : ℝ) : ℝ := if x = 2 then 3 else 4

example : h 2 = 3 := by
  simp [h]
```

**What differs.** Litex's `case` form is close to a piecewise mathematical definition. Lean's `if` form is compact and powerful, but the proof normally asks the simplifier to unfold the definition.

---

## Sets and membership

### Finite set membership

**Litex**

```litex
1 $in {1, 2}
```

**Lean**

```lean
import Mathlib

example : 1 ∈ ({1, 2} : Finset ℕ) := by
  simp
```

**What differs.** Litex treats finite display sets as ordinary mathematical objects in the surface language. Lean distinguishes the relevant set-like type, such as `Finset`, and then uses library simplification.

### Sets whose elements are sets

**Litex**

```litex
{1, 2} $in {{}, {1, 2}}
```

**Lean**

```lean
import Mathlib

example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp
```

**What differs.** Litex's set-theoretic surface makes nested sets feel direct. Lean is explicit about the type of each set expression, which prevents ambiguity and supports large developments.

### Set-builder membership

**Litex**

```litex
forall x {y R: y > 0}:
    x > 0
```

**Lean**

```lean
import Mathlib

example (x : {y : ℝ // y > 0}) : (x : ℝ) > 0 := by
  exact x.property
```

**What differs.** Litex lets a set-builder expression appear directly as a parameter domain. Lean often represents the same idea with a subtype, making the witness value and its proof field explicit.

### Inclusion through known universal facts

**Litex**

```litex
have a nonempty_set, b nonempty_set, c nonempty_set

know forall x a:
    x $in b

know forall x b:
    x $in c

have x a
x $in b
x $in c
```

**Lean**

```lean
import Mathlib

example {A B C : Set α} (hab : A ⊆ B) (hbc : B ⊆ C) (x : A) :
    (x : α) ∈ C := by
  exact hbc (hab x.property)
```

**What differs.** Litex records membership consequences and reuses them as facts in the local context. Lean expresses the same reasoning through subset functions and proof terms.

---

## Witnesses and existence

### A simple witness

**Litex**

```litex
witness exist x R st {x = 2} from 2:
    2 = 2
```

**Lean**

```lean
import Mathlib

example : ∃ x : ℝ, x = 2 := by
  use 2
```

**What differs.** Litex puts the witness, the existential shape, and the verification block in one visible structure. Lean's `use` tactic is short, but the user is still operating the proof state.

### A concrete counterexample

**Litex**

```litex
witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481:
    95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4
```

**Lean**

```lean
import Mathlib

example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num
```

**What differs.** Litex highlights the mathematical witnesses first. Lean packages the witnesses and proof obligations through constructors, which is more general but less like the written phrase "take these values."

---

## Proof structure

### Claims and local proofs

**Litex**

```litex
claim:
    prove:
        1 + 1 = 2
    1 + 1 = 2
```

**Lean**

```lean
import Mathlib

example : 1 + 1 = 2 := by
  norm_num
```

**What differs.** Litex separates a local proof block from the fact that is exported back to the surrounding context. Lean normally starts from a target theorem and transforms the proof state until the target is solved.

### Contradiction

**Litex**

```litex
abstract_prop p0(x, y)
abstract_prop q0(x, y)

know forall a, b R:
    $p0(a, b)
    =>:
        $q0(a, b)

know not $q0(1, 2)

by contra:
    prove:
        not $p0(1, 2)
    $p0(1, 2)
    impossible $q0(1, 2)
```

**Lean**

```lean
import Mathlib

example (p q : ℝ → ℝ → Prop)
    (h : ∀ a b, p a b → q a b)
    (hnq : ¬ q 1 2) :
    ¬ p 1 2 := by
  intro hp
  exact hnq (h 1 2 hp)
```

**What differs.** Litex exposes the contradiction as an ordinary mathematical line: assume the positive form, derive an impossible fact. Lean expresses the same argument as a function from the assumed proof to contradiction.

### Case splits

**Litex**

```litex
have fn k(z R) R :
    case z = 2: 3
    case z != 2: 4

have x R
x = 2 or x != 2

by cases:
    prove:
        k(x) > 2
    case x = 2:
        k(x) = 3
        k(x) > 2
    case x != 2:
        k(x) = 4
        k(x) > 2
```

**Lean**

```lean
import Mathlib

noncomputable def k (z : ℝ) : ℝ := if z = 2 then 3 else 4

example (x : ℝ) : k x > 2 := by
  by_cases h : x = 2
  · simp [k, h]
  · simp [k, h]
```

**What differs.** Litex keeps the proof split close to the displayed disjunction. Lean's `by_cases` is concise, but it introduces named case assumptions that the user then feeds to simplification.

---

## Finite enumeration and small algorithms

### Finite enumeration

**Litex**

```litex
by enumerate finite_set:
    prove:
        forall x {2, 4}:
            x = 2 or x = 4
    do_nothing
```

**Lean**

```lean
import Mathlib

example (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp
```

**What differs.** Litex has a direct surface form for checking a finite list of cases. Lean has strong enumeration tools too, but the exact tool depends on the type being enumerated.

### Bounded integer ranges

**Litex**

```litex
by for:
    prove:
        forall i range(0, 10):
            i < 10
    do_nothing
```

**Lean**

```lean
import Mathlib

example (i : ℤ) (hi : i ∈ Finset.range 10) : i < 10 := by
  exact_mod_cast Finset.mem_range.mp hi
```

**What differs.** Litex's `by for` presents the bounded walk as a proof shell over a range. Lean can encode the same idea precisely, but the encoding follows the library representation of finite ranges.

### Small algorithms

**Litex**

```litex
have fn m(x N_pos) R:
    case x = 1: 1
    case x != 1: 0

algo m(x):
    case x = 1: 1
    case x != 1: 0

eval m(1)
m(1) = 1
```

**Lean**

```lean
import Mathlib

def m (x : ℕ) : ℕ := if x = 1 then 1 else 0

example : m 1 = 1 := by
  simp [m]
```

**What differs.** Litex can keep a small algorithm, an evaluation, and the resulting fact in the same proof script. Lean's function definitions and computation are more general and integrate with the theorem prover's reduction and simplification machinery.

---

## Induction and large developments

**Litex**

```litex
abstract_prop p(n)

know:
    $p(0)
    forall n Z:
        n >= 0
        $p(n)
        =>:
            $p(n + 1)

by induc n from 0:
    prove:
        $p(n)
```

**Lean**

```lean
example (p : ℕ → Prop)
    (h0 : p 0)
    (hs : ∀ n, p n → p (n + 1)) :
    ∀ n, p n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih
```

**What differs.** Litex can display a simple textbook induction skeleton. Lean is stronger for advanced induction, dependent induction, custom eliminators, and large proofs that rely on a mature library. Litex should be read as lighter for simple induction patterns, not as a replacement for Lean's full induction machinery.

---

## Case study: infinitely many primes

Both systems can express the classic proof that there are infinitely many primes:

1. Start with a bound `a`.
2. Build the product `1 * 2 * ... * a`.
3. Consider `product + 1`.
4. Take a prime divisor `k` of that number.
5. If `k <= a`, then `k` divides the product, so `product + 1` has remainder `1` modulo `k`, contradicting that `k` divides it.
6. Therefore `k > a`.

In Litex, the main proof spine can be written as a claim with known background lemmas stated up front:

```text
know:
    every k <= a divides product(1, a, ...)
    every number >= 2 has a prime divisor
    a <= product(1, a, ...)

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    build product(1, a, ...) + 1
    take a prime divisor k
    by cases k > a:
        case k <= a:
            derive remainder 1
            impossible divisor remainder 0
        case k > a:
            done
    witness k
```

In Lean, the same mathematical idea often appears as a tactic proof that interleaves the background facts with the proof state:

```text
example (N : Nat) : exists p >= N, Prime p := by
  prove product + 1 is at least 2
  obtain a prime divisor p of product + 1
  split cases on the divisor witness
  prove p cannot divide the product
  use p
  finish the inequality and primality goals
```

**What differs.** Litex's `know` is not "cheating." It is the same lemma burden that Lean carries through `have`, `obtain`, `apply`, `calc`, case splits, and library lemmas. Litex tends to separate the lemma block from the main argument block, like a paper proof outline. Lean tends to interleave the lemmas with proof-state transformations. Lean's approach scales well with a large library; Litex's approach aims to make the proof spine easy to read.

---

## Fair trade-offs

Use Lean when you need:

- Mathlib coverage and a mature theorem-proving ecosystem;
- advanced type-theoretic abstractions;
- production-grade formalization;
- dependent induction, custom recursors, and deep automation;
- community-proven tooling for large projects.

Use Litex when you want:

- a set-theoretic surface close to ordinary mathematics;
- short proof scripts for teaching and everyday arguments;
- direct facts rather than many named proof terms;
- builtin relationships among basic mathematical objects;
- matching and substitution that reduce proof-engine bookkeeping.

Both systems require mathematics. Litex is not a way to avoid proving things. It changes where many routine steps live: more basic relationships are built into the language, and more reuse happens through fact matching and substitution. Lean gives the user a much more general engine; Litex tries to make common mathematical reasoning feel direct.
