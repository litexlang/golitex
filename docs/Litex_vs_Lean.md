# Litex vs Lean

Jiachen Shen and The Litex Team, 2026-05-07. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean.md

Related docs:

- [Soundness and Limitations](https://litexlang.com/doc/Soundness_and_Limitations)
- [Research Positioning](https://litexlang.com/doc/Research_Positioning)

_You can check out any time you like. But you can never leave._

_— Hotel California_

## Two Styles Of Formal Mathematics

Litex and Lean both make mathematical reasoning checkable by a computer. They are not trying to be the same language, and they expose different models of formal proof to the user.

Lean is a mature theorem prover with a powerful type-theoretic foundation, a large ecosystem, and Mathlib, one of the most impressive formal mathematics libraries in the world. Its user community is large, active, and highly professional, and this gives Lean a significant present-day advantage in library coverage, tooling, examples, and expert support. Litex is younger and more experimental. Its goal is narrower: make many everyday mathematical arguments look close to the way people write them on paper, while still checking them strictly.

- Lean exposes a very general proof engine. The user works with theorem statements, hypotheses, terms, proof states, tactics, and library lemmas.

- Litex exposes a fact-oriented mathematical surface built from objects, facts, and statements, starting from a set-theoretic picture: sets, elements, functions, and relations—the kind of informal foundation many people meet in everyday mathematics. Users write facts; Litex grows a verified context by checking them, storing them, inferring routine consequences, and explaining how accepted facts were proved.

One useful way to say the difference is: Lean often asks the user to choose proof commands explicitly, while Litex lets the user state the target fact and asks the kernel to match it against builtin rules, known facts, and known `forall` facts. A Litex statement is both something a mathematician can read and a shape the checker can use for matching.

> In short, in Lean, you often remember the names of facts and use `by` to explicitly tell Lean how to prove the goal; in Litex, *the shape of a fact already tells Litex what kind of proof path to try*.

This is not just a syntactic convenience. Litex tries to keep the main cognitive load on mathematical patterns: equality chains, subset arguments, existential witnesses, contradiction proofs, finite case splits, membership in a displayed set, and so on. The checker uses those patterns to search builtin rules, known facts, and known `forall` facts. The user is asked to remember the mathematical structure of the argument, not the name of the tactic or library lemma that packages the same move—as G. H. Hardy put it, *A mathematician, like a painter or poet, is a maker of patterns*.

This is a large reduction in friction for ordinary proofs. Even the largest library cannot package every future argument in exactly the final shape a user needs; eventually the user still has to write the mathematics. Litex's bet is that the remembered material should stay close to that mathematics. Remembering library and tactic names is useful in a system like Lean, but it is not the mathematical content the proof is trying to expose.

This is why Litex can be described as **the language where mathematics verifies itself**.

Litex also lets a development start from an abstract interface. A user can name
domains, relations, and axioms first, then reason from that structure before
choosing a concrete model. The current complete example is the
[Hilbert Axioms of Euclidean Geometry](https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry)
tutorial, where points, lines, planes, incidence, betweenness, and congruence
are introduced as abstract mathematical data rather than reduced to coordinates
at the start.

The trade-off is real. Lean is stronger for large formal developments and advanced abstractions, and at present its ecosystem advantage is substantial. Litex aims to make a different part of the design space feel natural: ordinary mathematical arguments where the proof script reads like a sequence of checked facts.

Lean is a powerful formal mathematics ecosystem. Litex explores a different
layer: a readable, fact-oriented verification interface for ordinary
mathematical reasoning and AI repair loops.

This matters for AI mathematical discovery as well as for human-written
examples. A discovery attempt may produce a long proof trail: intermediate
claims, reductions, computations, and local lemmas. Litex is aimed at checking
that trail as it is produced, so wrong turns can fail early and remaining
assumptions can be made explicit instead of hidden in fluent prose.

This page is not a ranking. It compares expression style, proof interaction, and where each system places routine mathematical structure. Most comparisons below use a Rosetta-stone layout: Litex on the left, Lean on the right, then a short note about what differs. The fenced `litex` block after each note is the runnable version used by the documentation test.

---

## First Examples

### Main README Example

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib.Tactic
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

**What differs.** Litex writes the desired facts directly. The checker stores `x = 2` in the local context, substitutes it into later goals, and closes the arithmetic. Lean names the hypothesis and guides rewriting explicitly through its proof language.

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

### Smallest Facts

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>1 + 1 = 2
1 &#36;in {1, 2}
forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
example : 1 + 1 = 2 := by
  norm_num
example : 1 ∈ ({1, 2} : Finset ℕ) := by
  simp
example (a : ℕ) (ha : a ∈ ({1, 2, 3} : Finset ℕ)) :
    a = 1 ∨ a = 2 ∨ a = 3 := by
  simpa using ha</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex writes arithmetic and membership as direct facts. Lean proves them quickly too, but usually after choosing the set-like type and calling simplification. If an object is in an enumerated set such as `{1, 2, 3}`, Litex immediately knows the corresponding disjunction: `a = 1 or a = 2 or a = 3`.

```litex
1 + 1 = 2
1 $in {1, 2}
forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

---

## The Manual Mental Model

The main Litex model is:

1. **Objects** are the mathematical things being discussed.
2. **Facts** are claims about those objects.
3. **Statements** are proof-script actions that define objects, assert facts, open local proofs, split cases, or provide witnesses.
4. **Execution** grows the current verified context by storing accepted facts and running inference.
5. **The proof process** checks each fact using well-definedness, builtin rules, known facts, and known `forall` facts.
6. **The builtin mathematical background** contains many small relationships among basic mathematical concepts.

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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x {y R: y > 0}:
    x > 0</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
example (x : {y : ℝ // y > 0}) : (x : ℝ) > 0 := by
  exact x.property</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex keeps the domain condition in the parameter. Lean usually packages the value and proof as a subtype.

```litex
forall x {y R: y > 0}:
    x > 0
```

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>have fn g(x R: x > 0) R = x + 1
g(1) = 2</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
def g (x : {x : ℝ // x > 0}) : ℝ := x.val + 1
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>have fn h(x R) R by cases:
    case x = 2: 3
    case x != 2: 4
h(2) = 3</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
noncomputable def h (x : ℝ) : ℝ := if x = 2 then 3 else 4
example : h 2 = 3 := by
  simp [h]</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex's `case` form reads like a piecewise definition. Lean uses `if` and unfolds it with simplification.

```litex
have fn h(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

h(2) = 3
```

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>have fn k(z R) R by cases:
    case z = 2: 3
    case z != 2: 4
have x R
by cases k(x) > 2:
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
noncomputable def k (z : ℝ) : ℝ := if z = 2 then 3 else 4
example (x : ℝ) : k x > 2 := by
  by_cases h : x = 2
  · simp [k, h]
  · simp [k, h]</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex keeps the cases and the function use close together. Lean introduces a named case assumption and feeds it to `simp`.

```litex
have fn k(z R) R by cases:
    case z = 2: 3
    case z != 2: 4

have x R

by cases k(x) > 2:
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

### Application-Flavored Definitions Stay Close To The Formula

Application problems often start from a formula that domain users already know.
For example, the signed area of the parallelogram spanned by two planar vectors
`x` and `y` is `x[1] * y[2] - x[2] * y[1]`.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>have fn signed_area(x, y cart(R, R)) R = x[1] * y[2] - x[2] * y[1]

signed_area((1, 0), (0, 1)) = 1 * 1 - 0 * 0 = 1</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
def signedArea (x y : ℝ × ℝ) : ℝ :=
  x.1 * y.2 - x.2 * y.1

example : signedArea (1, 0) (0, 1) = 1 := by
  norm_num [signedArea]</code></pre>
    </td>
  </tr>
</table>

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

### Anonymous Functions Can Be Passed Directly

Litex treats anonymous functions as ordinary objects. You can pass them directly into `sum`, `product`, or another higher-level mathematical object without first giving the function a separate name. This is useful for nested sums and products, where naming every temporary function would distract from the formula.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>eval sum(1, 3, 'Z(x){sum(1, x, 'Z(y){x + y})})</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>def inner (x : ℤ) : ℤ :=
  Finset.sum (Finset.Icc 1 x) (fun y => x + y)
def total : ℤ :=
  Finset.sum (Finset.Icc 1 3) inner</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex can pass an anonymous function object directly to a repeated sum or product. Lean can do the same mathematics, but users often introduce `fun` expressions, named definitions, ranges, coercions, or library conventions around finite sums.

```litex
eval sum(1, 3, 'Z(x){sum(1, x, 'Z(y){x + y})})
```

### Set Expressions Are Ordinary Objects

Because Litex is set-theoretic, set expressions are also ordinary objects. A set-builder or a finite set can appear where an object appears, just like `1`, `R`, or a function object. You do not need to define an extra named set first when the expression itself is clear.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>{x R: x > 0} = {x R: x > 0}
{1, 2} = {1, 2}</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
example : ({x : ℝ | x > 0} : Set ℝ) = {x : ℝ | x > 0} := by
  rfl
example : ({1, 2} : Finset ℕ) = {1, 2} := by
  rfl</code></pre>
    </td>
  </tr>
</table>

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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
    =>:
        y = 2 * (2 * x + 3 * y) - (4 * x + 5 * y) = 6
        x = ((2 * x + 3 * y) - 3 * y) / 2 = -4</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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
<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
example : ∃ a b c d : ℕ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4 := by
  refine ⟨95800, 217519, 414560, 422481, ?_⟩
  norm_num</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex puts the concrete values first. Lean packages values and obligations through constructors.

```litex
witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481
```

### Contradiction

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>abstract_prop p0(x, y)
abstract_prop q0(x, y)
know forall a, b R:
    &#36;p0(a, b)
    =>:
        &#36;q0(a, b)
know not &#36;q0(1, 2)
by contra not &#36;p0(1, 2):
    &#36;p0(1, 2)
    impossible &#36;q0(1, 2)</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

### Set Equality By Counterexample

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>by contra {a N: a % 4 = 0} != {a N: a % 2 = 0}:
    2 &#36;in {a N: a % 2 = 0}
    2 &#36;in {a N: a % 4 = 0}
    impossible 2 % 4 = 0</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
example : ({a : ℕ | a % 4 = 0} : Set ℕ) ≠ {a : ℕ | a % 2 = 0} := by
  intro h
  have h2 : (2 : ℕ) ∈ ({a : ℕ | a % 2 = 0} : Set ℕ) := by
    norm_num
  have h4 : (2 : ℕ) ∈ ({a : ℕ | a % 4 = 0} : Set ℕ) := by
    rw [h]
    exact h2
  norm_num at h4</code></pre>
    </td>
  </tr>
</table>

**What differs.** Litex uses `2` as the counterexample directly. Under the temporary equality assumption, membership transfers from the even naturals to the multiples of `4`, and the arithmetic contradiction closes the proof. Lean names the equality, rewrites the membership goal, and lets `norm_num` discharge the false modular fact.

```litex
by contra {a N: a % 4 = 0} != {a N: a % 2 = 0}:
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

Litex is deliberately friendly to that loop. It runs directly, has a small
surface syntax, and lets many library-like background facts be added as ordinary
Litex statements, builtin rules, or infer rules. This makes it practical to try
many natural formulations and turn failures into small language, library, rule,
or diagnostic improvements. Lean remains much stronger when the task depends on
Mathlib, advanced abstractions, or production formalization; the point is that
Litex can be a faster exploratory verification layer before a development
settles into its final form.

### Message Output Explains Each Step

Litex also reports what happened. Its message output shows each statement, the facts inferred from it, and often where each proved fact came from. **This is useful because you can see how every step was obtained**, not only that the final result passed. It helps users trust successful proofs, debug failed proofs, and learn how Litex is using builtin rules, known facts, matching, and substitution.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x R:
    x = 2
    =>:
        x + 1 = 3</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>known fact:
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    &#36;p(a, b)
    =>:
        &#36;p(a2, b2)</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example (p : α → β → Prop)
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>abstract_prop p(x)
know forall x R:
    &#36;p(x)
&#36;p(2)</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example (p : ℝ → Prop) (h : ∀ x : ℝ, p x) : p 2 := by
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

### Known `forall` Matching Inside Anonymous Functions

This example is a sharper version of known-`forall` reuse. The known fact says
that a predicate `p` is closed under pointwise addition of real-valued
functions. Litex first proves the inner sum function, then matches the final
anonymous-function body against the same known fact again.

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>abstract_prop p(x)

know forall f, g fn(x R) R:
    &#36;p(f)
    &#36;p(g)
    =&gt;:
        &#36;p('R(x){f(x) + g(x)})

claim:
    prove:
        forall a, b, c fn(x R) R:
            &#36;p(a)
            &#36;p(b)
            &#36;p(c)
            =&gt;:
                &#36;p('R(x){a(x) + (b(x) + c(x))})
    &#36;p('R(x){b(x) + c(x)})</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib

example (p : (ℝ → ℝ) → Prop)
    (h : ∀ f g : ℝ → ℝ, p f → p g → p (fun x =&gt; f x + g x))
    (a b c : ℝ → ℝ) (pa : p a) (pb : p b) (pc : p c) :
    p (fun x =&gt; a x + (b x + c x)) := by
  have hbc : p (fun x =&gt; b x + c x) := h b c pb pc
  exact h a (fun x =&gt; b x + c x) pa hbc</code></pre>
    </td>
  </tr>
</table>

**What differs.** In the final Litex goal, the matcher treats
`a(x) + (b(x) + c(x))` as an instance of `f(x) + g(x)`. Since `g` is applied to
the full anonymous-function parameter list `x`, Litex may infer
`g := 'R(x){b(x) + c(x)}`. Lean can express the same proof, but the user
normally supplies the intermediate function and applies the universal
hypothesis explicitly.

```litex
abstract_prop p(x)

know forall f, g fn(x R) R:
    $p(f)
    $p(g)
    =>:
        $p('R(x){f(x) + g(x)})

claim:
    prove:
        forall a, b, c fn(x R) R:
            $p(a)
            $p(b)
            $p(c)
            =>:
                $p('R(x){a(x) + (b(x) + c(x))})
    $p('R(x){b(x) + c(x)})
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>{1, 2} &#36;in {{}, {1, 2}}</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall i {1, 2}:
    i = 1 or i = 2</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>{1, 2} &#36;in power_set({1, 2, 3})</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>prove:
    let A, B set:
        A &#36;subset B
    forall x A:
        x &#36;in B</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>example {α : Type} {A B : Set α} (hAB : A ⊆ B) {x : α} (hx : x ∈ A) : x ∈ B := by
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>by contra:
    prove:
        {1, 2, 3} != {1, 2}
    count({1, 2, 3}) = 3
    count({1, 2}) = 2
    count({1, 2, 3}) = count({1, 2})
    impossible 3 = 2</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>prop prime(a N_pos):
    2 &lt;= a
    forall b N_pos:
        2 &lt;= b &lt; a
        =>:
            a % b != 0
know:
    forall a, k N_pos:
        k &lt;= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0
    forall a N_pos:
        2 &lt;= a
        =>:
            exist k N_pos st {&#36;prime(k), a % k = 0}
    forall a N_pos:
        a &lt;= product(1, a, 'N_pos(x){x})
claim forall! a N_pos: 2 &lt;= a => exist k N_pos st {k > a, &#36;prime(k)}:
    2 &lt;= a &lt;= product(1, a, 'N_pos(x){x}) &lt;= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {&#36;prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k &lt;= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, &#36;prime(k)} from k</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib
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

What Litex is trying to show is different. The user states the facts and witnesses they want, while the checker matches those targets against builtin rules and known information. Chains expose order/transitivity goals, `have by exist ...` exposes an existential pattern, `by cases` exposes branches, and `witness` exposes the object that should close an existential goal.

> The `prop` and `know` blocks are the background mathematics. The part that actually performs the proof is the `claim`, and that main proof is only a little more than ten lines.

> The Lean example above is adapted from *Mathematics in Lean*, which is an excellent introduction to Lean and formalized mathematics. It takes 6 pages to teach the reader how to prove this simple example. The point here is not that the Lean version is bad; it is carefully teaching the reader how two language philosophies can be used to express the same proof.

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

This is not Litex:
```text
forall P Prop:
    ...
```

**What differs.** Lean can quantify over `P : Prop` and treat proofs as terms. Litex does not make facts ordinary objects, keeping the object/fact split explicit.

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

## Appendix: Foundations And Design Intent

Litex is less interested in redefining every basic concept from a deeper user-facing abstraction, and more interested in the relationships between the concepts that ordinary mathematics already uses. Equality supports substitution. Membership in a number set gives sign or nonzero information. Subset facts give membership consequences. Function-domain facts make applications well-defined.

For this reason, Litex treats its builtin mathematical concepts as primitive at the surface level. Sets, elements, functions, relations, numbers, order, membership, and equality are part of the shared mathematical vocabulary of the language. They are not first presented to the user as consequences of a more abstract layer that must be unfolded before ordinary reasoning can begin.

Lean makes a different foundational choice. Its kernel is based on dependent type theory, which is more abstract and more general than the set-theoretic picture used in much informal mathematics. Type theory can encode set theory and many other mathematical structures, and Lean can support highly abstract mathematics such as category theory in libraries on top of that kernel. In this sense, Lean is stronger for foundational flexibility, large abstractions, and developments that need precise control over the underlying representation.

This does not mean one system is simply better at mathematics. Lean is a powerful proof assistant and functional programming language with a very general foundation. It also has the practical advantage of Mathlib, an active expert community, and years of accumulated formalization practice. Litex is intentionally narrower: it aims to make ordinary mathematical proof scripts read like checked facts over familiar concepts. The design cost is less foundational generality; the design benefit is a surface where common mathematical relationships are builtin and directly usable.

Put another way: Lean is a formal mathematics ecosystem; Litex is exploring a
readable verification layer for ordinary mathematical reasoning, local proof
feedback, and AI-assisted repair loops.
