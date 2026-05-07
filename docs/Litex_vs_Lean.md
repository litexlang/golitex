# Litex vs Lean

Jiachen Shen and The Litex Team, 2026-05-07. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean.md

## Two Styles Of Formal Mathematics

Litex and Lean both make mathematical reasoning checkable by a computer. They are not trying to be the same language.

Lean is a mature theorem prover with a powerful type-theoretic foundation, a large ecosystem, and Mathlib, one of the most impressive formal mathematics libraries in the world. Litex is younger and more experimental. Its goal is narrower: make many everyday mathematical arguments look close to the way people write them on paper, while still checking them strictly.

This page is not a ranking. It compares expression style and proof interaction.

- Lean exposes a very general proof engine. The user works with theorem statements, hypotheses, terms, proof states, tactics, and library lemmas.
- Litex exposes a mathematical surface built from objects, facts, and statements. The checker then tries builtin rules, known facts, and known `forall` facts by matching and substitution.

The trade-off is real. Lean is stronger for large formal developments and advanced abstractions. Litex aims to be easier to read and easier to start using for ordinary mathematics.

Most comparisons below use a Rosetta-stone layout: Litex on the left, Lean on the right, then a short note about what differs. The fenced `litex` block after each note is the runnable version used by the documentation test.

---

## First Examples

### Main README Example

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3
        x^2 = 4</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib.Tactic

example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre>
</td>
</tr>
</table>

**What differs.** Litex writes the desired facts directly. The checker remembers `x = 2`, substitutes it into later goals, and closes the arithmetic. Lean names the hypothesis and guides rewriting explicitly.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

### Smallest Facts

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>1 + 1 = 2

1 $in {1, 2}</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : 1 + 1 = 2 := by
  norm_num

example : 1 ∈ ({1, 2} : Finset ℕ) := by
  simp</code></pre>
</td>
</tr>
</table>

**What differs.** Litex writes arithmetic and membership as direct facts. Lean proves them quickly too, but usually after choosing the set-like type and calling simplification.

```litex
1 + 1 = 2
1 $in {1, 2}
```

---

## The Manual Mental Model

The main Litex model is:

1. **Objects** are the mathematical things being discussed.
2. **Facts** are claims about those objects.
3. **Statements** are proof-script actions that define objects, assert facts, open local proofs, split cases, or provide witnesses.
4. **The proof process** checks each fact using well-definedness, builtin rules, known facts, and known `forall` facts.
5. **The builtin mathematical background** contains many small relationships among basic mathematical concepts.

This is the best way to compare Litex and Lean. The difference is not one isolated syntax trick. It is where the system puts mathematical structure and how much proof-engine instruction the user writes.

---

## Objects: What Mathematical Things Look Like

Litex presents many everyday mathematical objects directly: numbers, sets, tuples, functions, set-builder expressions, Cartesian products, finite displays, sums, products, and matrices.

Lean can express these ideas too, often with more precision and more generality. But the user usually meets type-level encodings earlier: `Set`, `Finset`, subtypes, coercions, and theorem-library conventions.

### Set-Builder Domains And Functions

These examples belong together because they involve objects whose validity depends on a domain condition or a function definition.

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>forall x {y R: y &gt; 0}:
    x &gt; 0</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example (x : {y : ℝ // y &gt; 0}) : (x : ℝ) &gt; 0 := by
  exact x.property</code></pre>
</td>
</tr>
</table>

**What differs.** Litex keeps the domain condition in the parameter. Lean usually packages the value and proof as a subtype.

```litex
forall x {y R: y > 0}:
    x > 0
```

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>have fn g(x R: x &gt; 0) R = x + 1

g(1) = 2</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

def g (x : {x : ℝ // x &gt; 0}) : ℝ := x.val + 1

example : g ⟨1, by norm_num⟩ = 2 := by
  norm_num [g]</code></pre>
</td>
</tr>
</table>

**What differs.** Litex checks `1 > 0` as background mathematics. Lean passes a subtype value containing both `1` and its proof.

```litex
have fn g(x R: x > 0) R = x + 1

g(1) = 2
```

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>have fn h(x R) R :
    case x = 2: 3
    case x != 2: 4

h(2) = 3</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

noncomputable def h (x : ℝ) : ℝ := if x = 2 then 3 else 4

example : h 2 = 3 := by
  simp [h]</code></pre>
</td>
</tr>
</table>

**What differs.** Litex's `case` form reads like a piecewise definition. Lean uses `if` and unfolds it with simplification.

```litex
have fn h(x R) R :
    case x = 2: 3
    case x != 2: 4

h(2) = 3
```

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>have fn k(z R) R :
    case z = 2: 3
    case z != 2: 4

have x R

by cases k(x) &gt; 2:
    case x = 2:
        k(x) = 3 &gt; 2
    case x != 2:
        k(x) = 4 &gt; 2</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

noncomputable def k (z : ℝ) : ℝ := if z = 2 then 3 else 4

example (x : ℝ) : k x &gt; 2 := by
  by_cases h : x = 2
  · simp [k, h]
  · simp [k, h]</code></pre>
</td>
</tr>
</table>

**What differs.** Litex keeps the cases and the function use close together. Lean introduces a named case assumption and feeds it to `simp`.

```litex
have fn k(z R) R :
    case z = 2: 3
    case z != 2: 4

have x R

by cases k(x) > 2:
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

---

## Facts: How Claims Are Written

Litex proof scripts are built from facts. A fact may be atomic, such as equality or membership, or structured, such as a chain, an existential fact, a universal fact, a disjunction, or a conjunction.

Lean also proves propositions. The surface difference is that Lean code usually starts from a theorem goal and then constructs a proof of that goal, while Litex lets many facts appear directly as proof-script lines.

### Calculation Chains

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =&gt;:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

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
  · exact hx</code></pre>
</td>
</tr>
</table>

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

Litex statements are proof-script actions: `have`, `know`, `claim`, `witness`, `by cases`, `by contra`, `by enumerate`, `by induc`, and so on.

Lean also has structured proof commands and tactics. The difference is that Litex statements are meant to look like common mathematical proof moves, while Lean tactics operate a very general proof state.

### Witness Statements

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>witness exist x R st {x = 2} from 2:
    2 = 2</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : ∃ x : ℝ, x = 2 := by
  use 2</code></pre>
</td>
</tr>
</table>

**What differs.** Litex shows the witness and its check together. Lean uses `use` inside the proof state.

```litex
witness exist x R st {x = 2} from 2:
    2 = 2
```

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481:
    95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : ∃ a b c d : ℕ,
    a &gt; 0 ∧ b &gt; 0 ∧ c &gt; 0 ∧ d &gt; 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num</code></pre>
</td>
</tr>
</table>

**What differs.** Litex puts the concrete values first. Lean packages values and obligations through constructors.

```litex
witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481:
    95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4
```

### Contradiction

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>abstract_prop p0(x, y)
abstract_prop q0(x, y)

know forall a, b R:
    $p0(a, b)
    =&gt;:
        $q0(a, b)

know not $q0(1, 2)

by contra not $p0(1, 2):
    $p0(1, 2)
    impossible $q0(1, 2)</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example (p q : ℝ → ℝ → Prop)
    (h : ∀ a b, p a b → q a b)
    (hnq : ¬ q 1 2) :
    ¬ p 1 2 := by
  intro hp
  exact hnq (h 1 2 hp)</code></pre>
</td>
</tr>
</table>

**What differs.** Litex writes the contradiction as a proof move. Lean expresses it as a function from an assumption to contradiction.

```litex
abstract_prop p0(x, y)
abstract_prop q0(x, y)

know forall a, b R:
    $p0(a, b)
    =>:
        $q0(a, b)

know not $q0(1, 2)

by contra not $p0(1, 2):
    $p0(1, 2)
    impossible $q0(1, 2)
```

---

## Proof Process: Why Litex Needs Less Instruction

When Litex checks a fact, the usual loop is:

1. Check that the objects are well-defined.
2. Try builtin mathematical rules.
3. Try matching known facts.
4. Try matching known `forall` facts.

In Lean, the user often chooses the step explicitly: rewrite with this hypothesis, simplify this definition, apply this theorem, run this tactic. This gives very fine control and scales to deep formal developments. Litex chooses a different default for ordinary mathematics: many routine proof paths are tried by the checker.

### Message Output Explains Each Step

Litex also reports what happened. Its message output shows each statement, the facts inferred from it, and often where each proved fact came from. **This is useful because you can see how every step was obtained**, not only that the final result passed. It helps users trust successful proofs, debug failed proofs, and learn how Litex is using builtin rules, known facts, matching, and substitution.

<table>
<tr><th>Litex</th><th>Message idea</th></tr>
<tr>
<td valign="top">
<pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3</code></pre>
</td>
<td valign="top">
<pre><code>known fact:
  x = 2

goal:
  x + 1 = 3

proof:
  resolve x by x = 2
  reduce 2 + 1 by builtin arithmetic
  conclude x + 1 = 3</code></pre>
</td>
</tr>
</table>

**What differs.** Litex's output explains how each fact was obtained. That makes successful automation inspectable instead of opaque.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
```

### Known Facts By Matching

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =&gt;:
        $p(a2, b2)</code></pre>
</td>
<td valign="top">
<pre><code>example (p : α → β → Prop)
    {a a2 : α} {b b2 : β}
    (ha : a = a2) (hb : b = b2) (hp : p a b) :
    p a2 b2 := by
  subst a2
  subst b2
  exact hp</code></pre>
</td>
</tr>
</table>

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

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>abstract_prop p(x)

know forall x R:
    $p(x)

$p(2)</code></pre>
</td>
<td valign="top">
<pre><code>example (p : ℝ → Prop) (h : ∀ x : ℝ, p x) : p 2 := by
  exact h 2</code></pre>
</td>
</tr>
</table>

**What differs.** Litex matches the goal against known `forall` facts. Lean applies the universal hypothesis explicitly.

```litex
abstract_prop p(x)

know forall x R:
    $p(x)

$p(2)
```

---

## Builtin Mathematical Background

Ordinary mathematics uses many small background relationships: equality, order, membership, set predicates, function application, tuple projection, finite enumeration, arithmetic normalization, and so on. Each relationship is usually simple. The total number of interactions is large.

Litex builds many of these elementary relationships into the language layer. This makes short mathematical scripts less dependent on a separate standard library for basic steps. It can matter especially in areas where the needed background mathematics is not yet easy to express or package naturally in a type-theoretic library.

Lean's strength is different. Mathlib is a broad, mature, community-built mathematical library. For large formalization projects, advanced abstractions, and deep theorem reuse, that ecosystem is a major advantage.

The design difference is where routine mathematical background lives:

- In Litex, many basic relationships are part of the checker background.
- In Lean, much of the power comes from the library, tactics, and explicit proof terms that users can compose.

---

## Set Theory As A Larger Example

Set theory is a good place to see Litex's design. Litex's surface language treats sets, membership, finite set displays, set-builder domains, power sets, subsets, and cardinality-style facts as basic mathematical material. Lean can express all of these, but the user more often chooses a concrete encoding such as `Set`, `Finset`, subtype, decidable membership, coercions, and library lemmas.

### Nested Finite Sets

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>{1, 2} $in {{}, {1, 2}}</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : ({1, 2} : Set ℕ) ∈ ({∅, {1, 2}} : Set (Set ℕ)) := by
  simp</code></pre>
</td>
</tr>
</table>

**What differs.** Litex writes nested set membership directly. Lean makes the outer element type explicit: `Set (Set ℕ)`.

```litex
{1, 2} $in {{}, {1, 2}}
```

### Finite Enumeration

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>forall i {1, 2}:
    i = 1 or i = 2</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example {i : ℕ} (hi : i ∈ ({1, 2} : Finset ℕ)) : i = 1 ∨ i = 2 := by
  simpa using hi</code></pre>
</td>
</tr>
</table>

**What differs.** Litex unfolds the finite display as possible values. Lean uses `Finset ℕ` and simplification.

```litex
forall i {1, 2}:
    i = 1 or i = 2
```

### Power Set Membership

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>{1, 2} $in power_set({1, 2, 3})</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  intro x hx
  simp at hx
  simp [hx]</code></pre>
</td>
</tr>
</table>

**What differs.** Litex writes power-set membership directly. Lean often proves the underlying subset relation.

```litex
{1, 2} $in power_set({1, 2, 3})
```

### Subset Facts Produce Membership Facts

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B</code></pre>
</td>
<td valign="top">
<pre><code>example {α : Type} {A B : Set α} (hAB : A ⊆ B) {x : α} (hx : x ∈ A) : x ∈ B := by
  exact hAB hx</code></pre>
</td>
</tr>
</table>

**What differs.** Litex infers membership consequences from `A $subset B`. Lean applies the subset hypothesis as a function.

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

### Unequal Cardinalities Rule Out Equality

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>by contra:
    prove:
        {1, 2, 3} != {1, 2}
    count({1, 2, 3}) = 3
    count({1, 2}) = 2
    count({1, 2, 3}) = count({1, 2})
    impossible 3 = 2</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example : ({1, 2, 3} : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by
  intro h
  have hcard := congrArg Finset.card h
  norm_num at hcard</code></pre>
</td>
</tr>
</table>

**What differs.** Litex follows the count contradiction directly. Lean uses `Finset.card`, `congrArg`, and simplification.

```litex
by contra:
    prove:
        {1, 2, 3} != {1, 2}
    count({1, 2, 3}) = 3
    count({1, 2}) = 2
    count({1, 2, 3}) = count({1, 2})
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

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>prop prime(a N_pos):
    2 &lt;= a
    forall b N_pos:
        2 &lt;= b &lt; a
        =&gt;:
            a % b != 0

know:
    forall a, k N_pos:
        k &lt;= a
        =&gt;:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 &lt;= a
        =&gt;:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a &lt;= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 &lt;= a =&gt; exist k N_pos st {k &gt; a, $prime(k)}:
    2 &lt;= a &lt;= product(1, a, 'N_pos(x){x}) &lt;= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k &gt; a:
        case k &lt;= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k &gt; a:
            do_nothing
    witness exist k N_pos st {k &gt; a, $prime(k)} from k</code></pre>
</td>
<td valign="top">
<pre><code>import Mathlib

example (N : ℕ) : ∃ p ≥ N, Nat.Prime p := by
  have hN0 : 0 &lt; N ! := by exact Nat.factorial_pos N
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
  · exact hp</code></pre>
</td>
</tr>
</table>

**What differs.** Litex separates background lemmas from the `claim` spine. Lean often interleaves lemmas with proof-state transformations. Both carry real proof burden; they organize it differently.

The `prop` and `know` blocks are the background mathematics. The part that actually performs the proof is the `claim`, and that main proof is only a little more than ten lines. Each line is a direct mathematical move: build the number, take a prime divisor, split on `k > a`, derive the contradiction, and return the witness.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

---

## More Technical Differences

This section is for readers who already care about theorem-prover foundations. These differences are not the first thing a beginner needs, but they explain why Litex and Lean feel different at a deeper level.

### Facts Are Not Objects

Litex keeps objects and facts separate. A `prop` defines a predicate form. Applying that predicate to objects creates a fact.

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>abstract_prop positive(x)

know forall x R:
    x &gt; 0
    =&gt;:
        $positive(x)

forall x R:
    x &gt; 0
    =&gt;:
        $positive(x)

This is not Litex:

forall P Prop:
    ...</code></pre>
</td>
<td valign="top">
<pre><code>example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP</code></pre>
</td>
</tr>
</table>

**What differs.** Lean can quantify over `P : Prop` and treat proofs as terms. Litex does not make facts ordinary objects, keeping the object/fact split explicit.

```litex
abstract_prop positive(x)

know forall x R:
    x > 0
    =>:
        $positive(x)

forall x R:
    x > 0
    =>:
        $positive(x)
```

### Statements And Proofs As Values

This difference goes further than `P : Prop`. In Lean, propositions and proofs live inside the same type-theoretic world as other terms. A previous theorem, a proof of a proposition, or a function from one proof to another can be passed as an argument to a later theorem.

<table>
<tr><th>Litex</th><th>Lean</th></tr>
<tr>
<td valign="top">
<pre><code>x = 2

This is not Litex:

have h = (x = 2)
some_statement(h)</code></pre>
</td>
<td valign="top">
<pre><code>example (P Q : Prop) (hP : P) (h : P → Q) : Q := by
  exact h hP</code></pre>
</td>
</tr>
</table>

**What differs.** Lean supports higher-order proof programming: propositions, proofs, and theorem arguments can be manipulated as terms. Litex keeps statements as proof actions and facts as context information, not as first-class objects.

```litex
forall x R:
    x = 2
    =>:
        x = 2
```

---

## Fair Trade-Offs

Use Lean when you need:

- Mathlib coverage and a mature theorem-proving ecosystem;
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
- matching and substitution that reduce proof-engine bookkeeping.

Both systems require mathematics. Litex is not a way to avoid proving things. It changes where many routine steps live: more basic relationships are built into the language, and more reuse happens through fact matching and substitution. Lean gives the user a much more general engine; Litex tries to make common mathematical reasoning feel direct.
# Litex vs Lean

Jiachen Shen and The Litex Team, 2026-05-07. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean.md

## Two styles of formal mathematics

Litex and Lean both make mathematical reasoning checkable by a computer. They are not trying to be the same language.

Lean is a mature theorem prover with a powerful type-theoretic foundation, a large ecosystem, and Mathlib, one of the most impressive formal mathematics libraries in the world. 

Litex is younger and more experimental. Its goal is narrower: make many everyday mathematical arguments look close to the way people write them on paper, while still checking them strictly.

This page is not a ranking. It compares expression style and proof interaction.

- Lean exposes a very general proof engine. The user works with theorem statements, hypotheses, terms, proof states, tactics, and library lemmas.
- Litex exposes a mathematical surface built from objects, facts, and statements. The checker then tries builtin rules, known facts, and known `forall` facts by matching and substitution.

The trade-off is real. Lean is stronger for large formal developments and advanced abstractions. Litex aims to be easier to read and easier to start using for ordinary mathematics.

---

## First examples

Before the larger structure, here are the examples that show the intended feel.

### Main README example

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

**What differs.** Litex writes the desired facts directly. The checker remembers `x = 2`, substitutes it into later goals, and closes the arithmetic. Lean names the hypothesis and guides rewriting explicitly.

### Arithmetic

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

**What differs.** Litex writes arithmetic as a fact. Lean usually calls `norm_num`.

### Membership

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

**What differs.** Litex uses the finite display directly. Lean chooses `Finset ℕ` and simplifies.

These examples are deliberately small. They are not the whole comparison; they are a quick entry point before the Manual-style structure below.

---

## The manual mental model

The main Litex model is:

1. **Objects** are the mathematical things being discussed.
2. **Facts** are claims about those objects.
3. **Statements** are proof-script actions that define objects, assert facts, open local proofs, split cases, or provide witnesses.
4. **The proof process** checks each fact using well-definedness, builtin rules, known facts, and known `forall` facts.
5. **The builtin mathematical background** contains many small relationships among basic mathematical concepts.

This is the best way to compare Litex and Lean. The difference is not one isolated syntax trick. It is where the system puts mathematical structure and how much proof-engine instruction the user writes.

---

## Objects: what mathematical things look like

Litex presents many everyday mathematical objects directly: numbers, sets, tuples, functions, set-builder expressions, Cartesian products, finite displays, sums, products, and matrices.

Lean can express these ideas too, often with more precision and more generality. But the user usually meets type-level encodings earlier: `Set`, `Finset`, subtypes, coercions, and theorem-library conventions.

### Set-builder domains and functions

These examples belong together because they all involve objects whose validity depends on a domain condition or a function definition.

**Set-builder domain in Litex**

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

**What differs.** Litex keeps the domain condition in the parameter. Lean usually packages the value and proof as a subtype.

**Restricted function in Litex**

**Litex**

```litex
have fn g(x R: x > 0) R = x + 1

g(1) = 2
```

**Lean**

```lean
import Mathlib

def g (x : {x : ℝ // x > 0}) : ℝ := x.val + 1

example : g ⟨1, by norm_num⟩ = 2 := by
  norm_num [g]
```

**What differs.** Litex checks `1 > 0` as background mathematics. Lean passes a subtype value containing both `1` and its proof.

**Piecewise function in Litex**

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

**What differs.** Litex's `case` form reads like a piecewise definition. Lean uses `if` and unfolds it with simplification.

**Case analysis around a function**

**Litex**

```litex
have fn k(z R) R :
    case z = 2: 3
    case z != 2: 4

have x R

by cases k(x) > 2:
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
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

**What differs.** Litex keeps the cases and the function use close together. Lean introduces a named case assumption and feeds it to `simp`.

---

## Facts: how claims are written

Litex proof scripts are built from facts. A fact may be atomic, such as equality or membership, or structured, such as a chain, an existential fact, a universal fact, a disjunction, or a conjunction.

Lean also proves propositions, of course. The surface difference is that Lean code usually starts from a theorem goal and then constructs a proof of that goal, while Litex lets many facts appear directly as proof-script lines.

### Calculation chains

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

**What differs.** Litex's calculation chain is one factual statement. Lean's explicit version uses named goals, `calc`, rewrites, and tactics.

---

## Statements: how a proof script moves

Litex statements are proof-script actions: `have`, `know`, `claim`, `witness`, `by cases`, `by contra`, `by enumerate`, `by induc`, and so on.

Lean also has structured proof commands and tactics. The difference is that Litex statements are meant to look like common mathematical proof moves, while Lean tactics operate a very general proof state.

### Witness statements


**Litex**

```litex
witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
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

**What differs.** Litex checks the exist fact by replacing the objects in the existential fact with the concrete values. Lean packages values and obligations through constructors.

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

by contra not $p0(1, 2):
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

**What differs.** Litex writes the contradiction as a proof move. Lean expresses it as a function from an assumption to contradiction.

---

## Proof process: why Litex needs less instruction

When Litex checks a fact, the usual loop is:

1. Check that the objects are well-defined.
2. Try builtin mathematical rules.
3. Try matching known facts.
4. Try matching known `forall` facts.

In Lean, the user often chooses the step explicitly: rewrite with this hypothesis, simplify this definition, apply this theorem, run this tactic. This gives very fine control and scales to deep formal developments. Litex chooses a different default for ordinary mathematics: many routine proof paths are tried by the checker.

### Message output explains each step

Litex also reports what happened. Its message output shows each statement, the facts inferred from it, and often where each proved fact came from. **This is useful because you can see how every step was obtained**, not only that the final result passed. It helps users trust successful proofs, debug failed proofs, and learn how Litex is using builtin rules, known facts, matching, and substitution.

For example, this proof is short:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
```

The output looks like this:

```text
{
  "result": "success",
  "type": "Fact",
  "line": 1,
  "stmt": "forall x R:\n    x = 2\n    =>:\n        x + 1 = 3",
  "verified_by": [
    {
      "type": "builtin rule",
      "rule": "calculation"
    }
  ],
  "infer_facts": [],
  "inside_results": []
}

```

This is useful when a proof succeeds, because you can see why. It is even more useful when a proof fails, because the message points to the exact fact Litex could not justify.

### Known facts by matching

**Litex**

```litex
abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =>:
        $p(a2, b2)
```

**Lean**

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

### Known `forall` facts

**Litex**

```litex
abstract_prop p(x)

know forall x R:
    $p(x)

$p(2)
```

**Lean**

```lean
example (p : ℝ → Prop) (h : ∀ x : ℝ, p x) : p 2 := by
  exact h 2
```

**What differs.** Litex matches the goal against known `forall` facts. Lean applies the universal hypothesis explicitly.

---

## Builtin mathematical background

Ordinary mathematics uses many small background relationships: equality, order, membership, set predicates, function application, tuple projection, finite enumeration, arithmetic normalization, and so on. Each relationship is usually simple. The total number of interactions is large.

Litex builds many of these elementary relationships into the language layer. This makes short mathematical scripts less dependent on a separate standard library for basic steps. It can matter especially in areas where the needed background mathematics is not yet easy to express or package naturally in a type-theoretic library.

Lean's strength is different. Mathlib is a broad, mature, community-built mathematical library. For large formalization projects, advanced abstractions, and deep theorem reuse, that ecosystem is a major advantage.

The design difference is where routine mathematical background lives:

- In Litex, many basic relationships are part of the checker background.
- In Lean, much of the power comes from the library, tactics, and explicit proof terms that users can compose.

---

## Set theory as a larger example

Set theory is a good place to see Litex's design. Litex's surface language treats sets, membership, finite set displays, set-builder domains, power sets, subsets, and cardinality-style facts as basic mathematical material. Lean can express all of these, but the user more often chooses a concrete encoding such as `Set`, `Finset`, subtype, decidable membership, coercions, and library lemmas.

**Nested finite sets**

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

**What differs.** Litex writes nested set membership directly. Lean makes the outer element type explicit: `Set (Set ℕ)`.

**Finite enumeration**

**Litex**

```litex
forall i {1, 2}:
    i = 1 or i = 2
```

**Lean**

```lean
import Mathlib

example {i : ℕ} (hi : i ∈ ({1, 2} : Finset ℕ)) : i = 1 ∨ i = 2 := by
  simpa using hi
```

**What differs.** Litex unfolds the finite display as possible values. Lean uses `Finset ℕ` and simplification.

**Power set membership**

**Litex**

```litex
{1, 2} $in power_set({1, 2, 3})
```

**Lean**

```lean
import Mathlib

example : ({1, 2} : Set ℕ) ⊆ ({1, 2, 3} : Set ℕ) := by
  intro x hx
  simp at hx
  simp [hx]
```

**What differs.** Litex writes power-set membership directly. Lean often proves the underlying subset relation.

**Subset facts produce membership facts**

**Litex**

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

**Lean**

```lean
example {α : Type} {A B : Set α} (hAB : A ⊆ B) {x : α} (hx : x ∈ A) : x ∈ B := by
  exact hAB hx
```

**What differs.** Litex infers membership consequences from `A $subset B`. Lean applies the subset hypothesis as a function.

**Unequal cardinalities rule out equality**

**Litex**

```litex
by contra:
    prove:
        {1, 2, 3} != {1, 2}
    count({1, 2, 3}) = 3
    count({1, 2}) = 2
    count({1, 2, 3}) = count({1, 2})
    impossible 3 = 2
```

**Lean**

```lean
import Mathlib

example : ({1, 2, 3} : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by
  intro h
  have hcard := congrArg Finset.card h
  norm_num at hcard
```

**What differs.** Litex follows the count contradiction directly. Lean uses `Finset.card`, `congrArg`, and simplification.

These examples are intentionally larger than `1 + 1 = 2` but still much smaller than the prime-number case study. They show why set theory is a natural foundation for Litex: many common mathematical objects are already first-class enough that the proof can stay close to the sentence a mathematician would write.

---

## Case study: infinitely many primes

Both systems can express the classic proof that there are infinitely many primes:

1. Start with a bound `a`.
2. Build the product `1 * 2 * ... * a`.
3. Consider `product + 1`.
4. Take a prime divisor `k` of that number.
5. If `k <= a`, then `k` divides the product, so `product + 1` has remainder `1` modulo `k`, contradicting that `k` divides it.
6. Therefore `k > a`.

In Litex, the main proof spine can be written as a `claim` with known background lemmas stated up front:

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

The `prop` and `know` blocks are the background mathematics. The part that actually performs the proof is the `claim`, and that main proof is only a little more than ten lines. Each line is a direct mathematical move: build the number, take a prime divisor, split on `k > a`, derive the contradiction, and return the witness.

In Lean, the same mathematical idea often appears as a tactic proof that interleaves the background facts with the proof state:

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

**What differs.** Litex separates background lemmas from the `claim` spine. Lean often interleaves lemmas with proof-state transformations. Both carry real proof burden; they organize it differently.

---

## More technical differences

This section is for readers who already care about theorem-prover foundations. These differences are not the first thing a beginner needs, but they explain why Litex and Lean feel different at a deeper level.

### Facts are not objects

Litex keeps objects and facts separate. A `prop` defines a predicate form. Applying that predicate to objects creates a fact.

**Litex**

```litex
abstract_prop positive(x)

know forall x R:
    x > 0
    =>:
        $positive(x)

forall x R:
    x > 0
    =>:
        $positive(x)
```

But Litex does not treat propositions as objects that can be passed through the parameter list:

```text
This is not Litex:

forall P Prop:
    ...
```

**Lean**

```lean
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP
```

**What differs.** Lean can quantify over `P : Prop` and treat proofs as terms. Litex does not make facts ordinary objects, keeping the object/fact split explicit.

### Statements and proofs as values

This difference goes further than `P : Prop`. In Lean, propositions and proofs live inside the same type-theoretic world as other terms. A previous theorem, a proof of a proposition, or a function from one proof to another can be passed as an argument to a later theorem.

```lean
example (P Q : Prop) (hP : P) (h : P → Q) : Q := by
  exact h hP
```

Here `hP` is not just remembered background. It is a proof object passed to `h`.

Litex is intentionally different. A statement such as `x = 2` can become a known fact in the proof context, and later facts can use it by matching and substitution. But the previous statement itself is not an object that can be passed as a parameter to another statement.

```text
This is not Litex:

have h = (x = 2)
some_statement(h)
```

**What differs.** Lean supports higher-order proof programming: propositions, proofs, and theorem arguments can be manipulated as terms. Litex keeps statements as proof actions and facts as context information, not as first-class objects. This makes Litex less abstract, but closer to ordinary mathematical writing.

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
- direct mathematical objects such as sets, functions, tuples, and set-builders;
- direct facts rather than many named proof terms;
- proof statements that look like common mathematical moves;
- builtin relationships among basic mathematical objects;
- matching and substitution that reduce proof-engine bookkeeping.

Both systems require mathematics. Litex is not a way to avoid proving things. It changes where many routine steps live: more basic relationships are built into the language, and more reuse happens through fact matching and substitution.
