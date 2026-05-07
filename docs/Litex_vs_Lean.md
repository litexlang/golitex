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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>forall&nbsp;x&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;=&nbsp;2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x^2&nbsp;=&nbsp;4</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib.Tactic</code><br>
<br>
<code>example&nbsp;(x&nbsp;:&nbsp;ℝ)&nbsp;(h&nbsp;:&nbsp;x&nbsp;=&nbsp;2)&nbsp;:&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3&nbsp;∧&nbsp;x&nbsp;^&nbsp;2&nbsp;=&nbsp;4&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;have&nbsp;h_add&nbsp;:&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;rw&nbsp;[h]</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num</code><br>
<code>&nbsp;&nbsp;have&nbsp;h_square&nbsp;:&nbsp;x&nbsp;^&nbsp;2&nbsp;=&nbsp;4&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;rw&nbsp;[h]</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num</code><br>
<code>&nbsp;&nbsp;exact&nbsp;⟨h_add,&nbsp;h_square⟩</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>1&nbsp;+&nbsp;1&nbsp;=&nbsp;2</code><br>
<br>
<code>1&nbsp;$in&nbsp;{1,&nbsp;2}</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;1&nbsp;+&nbsp;1&nbsp;=&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;norm_num</code><br>
<br>
<code>example&nbsp;:&nbsp;1&nbsp;∈&nbsp;({1,&nbsp;2}&nbsp;:&nbsp;Finset&nbsp;ℕ)&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;simp</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>forall&nbsp;x&nbsp;{y&nbsp;R:&nbsp;y&nbsp;&gt;&nbsp;0}:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;&gt;&nbsp;0</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;(x&nbsp;:&nbsp;{y&nbsp;:&nbsp;ℝ&nbsp;//&nbsp;y&nbsp;&gt;&nbsp;0})&nbsp;:&nbsp;(x&nbsp;:&nbsp;ℝ)&nbsp;&gt;&nbsp;0&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;exact&nbsp;x.property</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>have&nbsp;fn&nbsp;g(x&nbsp;R:&nbsp;x&nbsp;&gt;&nbsp;0)&nbsp;R&nbsp;=&nbsp;x&nbsp;+&nbsp;1</code><br>
<br>
<code>g(1)&nbsp;=&nbsp;2</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>def&nbsp;g&nbsp;(x&nbsp;:&nbsp;{x&nbsp;:&nbsp;ℝ&nbsp;//&nbsp;x&nbsp;&gt;&nbsp;0})&nbsp;:&nbsp;ℝ&nbsp;:=&nbsp;x.val&nbsp;+&nbsp;1</code><br>
<br>
<code>example&nbsp;:&nbsp;g&nbsp;⟨1,&nbsp;by&nbsp;norm_num⟩&nbsp;=&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;norm_num&nbsp;[g]</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>have&nbsp;fn&nbsp;h(x&nbsp;R)&nbsp;R&nbsp;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;x&nbsp;=&nbsp;2:&nbsp;3</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;x&nbsp;!=&nbsp;2:&nbsp;4</code><br>
<br>
<code>h(2)&nbsp;=&nbsp;3</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>noncomputable&nbsp;def&nbsp;h&nbsp;(x&nbsp;:&nbsp;ℝ)&nbsp;:&nbsp;ℝ&nbsp;:=&nbsp;if&nbsp;x&nbsp;=&nbsp;2&nbsp;then&nbsp;3&nbsp;else&nbsp;4</code><br>
<br>
<code>example&nbsp;:&nbsp;h&nbsp;2&nbsp;=&nbsp;3&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;simp&nbsp;[h]</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>have&nbsp;fn&nbsp;k(z&nbsp;R)&nbsp;R&nbsp;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;z&nbsp;=&nbsp;2:&nbsp;3</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;z&nbsp;!=&nbsp;2:&nbsp;4</code><br>
<br>
<code>have&nbsp;x&nbsp;R</code><br>
<br>
<code>by&nbsp;cases&nbsp;k(x)&nbsp;&gt;&nbsp;2:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;x&nbsp;=&nbsp;2:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;k(x)&nbsp;=&nbsp;3&nbsp;&gt;&nbsp;2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;x&nbsp;!=&nbsp;2:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;k(x)&nbsp;=&nbsp;4&nbsp;&gt;&nbsp;2</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>noncomputable&nbsp;def&nbsp;k&nbsp;(z&nbsp;:&nbsp;ℝ)&nbsp;:&nbsp;ℝ&nbsp;:=&nbsp;if&nbsp;z&nbsp;=&nbsp;2&nbsp;then&nbsp;3&nbsp;else&nbsp;4</code><br>
<br>
<code>example&nbsp;(x&nbsp;:&nbsp;ℝ)&nbsp;:&nbsp;k&nbsp;x&nbsp;&gt;&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;by_cases&nbsp;h&nbsp;:&nbsp;x&nbsp;=&nbsp;2</code><br>
<code>&nbsp;&nbsp;·&nbsp;simp&nbsp;[k,&nbsp;h]</code><br>
<code>&nbsp;&nbsp;·&nbsp;simp&nbsp;[k,&nbsp;h]</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>forall&nbsp;x,&nbsp;y&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y&nbsp;=&nbsp;10</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;4&nbsp;*&nbsp;x&nbsp;+&nbsp;5&nbsp;*&nbsp;y&nbsp;=&nbsp;14</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;y&nbsp;=&nbsp;2&nbsp;*&nbsp;(2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y)&nbsp;-&nbsp;(4&nbsp;*&nbsp;x&nbsp;+&nbsp;5&nbsp;*&nbsp;y)&nbsp;=&nbsp;6</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;=&nbsp;((2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y)&nbsp;-&nbsp;3&nbsp;*&nbsp;y)&nbsp;/&nbsp;2&nbsp;=&nbsp;-4</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;(x&nbsp;y&nbsp;:&nbsp;ℝ)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;(h1&nbsp;:&nbsp;2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y&nbsp;=&nbsp;10)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;(h2&nbsp;:&nbsp;4&nbsp;*&nbsp;x&nbsp;+&nbsp;5&nbsp;*&nbsp;y&nbsp;=&nbsp;14)&nbsp;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;y&nbsp;=&nbsp;6&nbsp;∧&nbsp;x&nbsp;=&nbsp;-4&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;have&nbsp;hy&nbsp;:&nbsp;y&nbsp;=&nbsp;6&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;calc</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;y&nbsp;=&nbsp;2&nbsp;*&nbsp;(2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y)&nbsp;-&nbsp;(4&nbsp;*&nbsp;x&nbsp;+&nbsp;5&nbsp;*&nbsp;y)&nbsp;:=&nbsp;by&nbsp;linarith</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_&nbsp;=&nbsp;2&nbsp;*&nbsp;10&nbsp;-&nbsp;14&nbsp;:=&nbsp;by&nbsp;rw&nbsp;[h1,&nbsp;h2]</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_&nbsp;=&nbsp;6&nbsp;:=&nbsp;by&nbsp;norm_num</code><br>
<code>&nbsp;&nbsp;have&nbsp;hx&nbsp;:&nbsp;x&nbsp;=&nbsp;-4&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;calc</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;=&nbsp;((2&nbsp;*&nbsp;x&nbsp;+&nbsp;3&nbsp;*&nbsp;y)&nbsp;-&nbsp;3&nbsp;*&nbsp;y)&nbsp;/&nbsp;2&nbsp;:=&nbsp;by&nbsp;ring</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_&nbsp;=&nbsp;(10&nbsp;-&nbsp;3&nbsp;*&nbsp;6)&nbsp;/&nbsp;2&nbsp;:=&nbsp;by&nbsp;rw&nbsp;[h1,&nbsp;hy]</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;_&nbsp;=&nbsp;-4&nbsp;:=&nbsp;by&nbsp;norm_num</code><br>
<code>&nbsp;&nbsp;constructor</code><br>
<code>&nbsp;&nbsp;·&nbsp;exact&nbsp;hy</code><br>
<code>&nbsp;&nbsp;·&nbsp;exact&nbsp;hx</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>witness&nbsp;exist&nbsp;x&nbsp;R&nbsp;st&nbsp;{x&nbsp;=&nbsp;2}&nbsp;from&nbsp;2:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;=&nbsp;2</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;∃&nbsp;x&nbsp;:&nbsp;ℝ,&nbsp;x&nbsp;=&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;use&nbsp;2</code>
    </td>
  </tr>
</table>

**What differs.** Litex shows the witness and its check together. Lean uses `use` inside the proof state.

```litex
witness exist x R st {x = 2} from 2:
    2 = 2
```

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>witness&nbsp;exist&nbsp;a,&nbsp;b,&nbsp;c,&nbsp;d&nbsp;N_pos&nbsp;st&nbsp;{a&nbsp;^&nbsp;4&nbsp;+&nbsp;b&nbsp;^&nbsp;4&nbsp;+&nbsp;c&nbsp;^&nbsp;4&nbsp;=&nbsp;d&nbsp;^&nbsp;4}&nbsp;from&nbsp;95800,&nbsp;217519,&nbsp;414560,&nbsp;422481:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;95800&nbsp;^&nbsp;4&nbsp;+&nbsp;217519&nbsp;^&nbsp;4&nbsp;+&nbsp;414560&nbsp;^&nbsp;4&nbsp;=&nbsp;422481&nbsp;^&nbsp;4</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;∃&nbsp;a&nbsp;b&nbsp;c&nbsp;d&nbsp;:&nbsp;ℕ,</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;a&nbsp;&gt;&nbsp;0&nbsp;∧&nbsp;b&nbsp;&gt;&nbsp;0&nbsp;∧&nbsp;c&nbsp;&gt;&nbsp;0&nbsp;∧&nbsp;d&nbsp;&gt;&nbsp;0&nbsp;∧</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;a&nbsp;^&nbsp;4&nbsp;+&nbsp;b&nbsp;^&nbsp;4&nbsp;+&nbsp;c&nbsp;^&nbsp;4&nbsp;=&nbsp;d&nbsp;^&nbsp;4&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;refine&nbsp;⟨95800,&nbsp;217519,&nbsp;414560,&nbsp;422481,&nbsp;?_⟩</code><br>
<code>&nbsp;&nbsp;norm_num</code>
    </td>
  </tr>
</table>

**What differs.** Litex puts the concrete values first. Lean packages values and obligations through constructors.

```litex
witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481:
    95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4
```

### Contradiction

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>abstract_prop&nbsp;p0(x,&nbsp;y)</code><br>
<code>abstract_prop&nbsp;q0(x,&nbsp;y)</code><br>
<br>
<code>know&nbsp;forall&nbsp;a,&nbsp;b&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;$p0(a,&nbsp;b)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$q0(a,&nbsp;b)</code><br>
<br>
<code>know&nbsp;not&nbsp;$q0(1,&nbsp;2)</code><br>
<br>
<code>by&nbsp;contra&nbsp;not&nbsp;$p0(1,&nbsp;2):</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;$p0(1,&nbsp;2)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;impossible&nbsp;$q0(1,&nbsp;2)</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;(p&nbsp;q&nbsp;:&nbsp;ℝ&nbsp;→&nbsp;ℝ&nbsp;→&nbsp;Prop)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;(h&nbsp;:&nbsp;∀&nbsp;a&nbsp;b,&nbsp;p&nbsp;a&nbsp;b&nbsp;→&nbsp;q&nbsp;a&nbsp;b)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;(hnq&nbsp;:&nbsp;¬&nbsp;q&nbsp;1&nbsp;2)&nbsp;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;¬&nbsp;p&nbsp;1&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;intro&nbsp;hp</code><br>
<code>&nbsp;&nbsp;exact&nbsp;hnq&nbsp;(h&nbsp;1&nbsp;2&nbsp;hp)</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>forall&nbsp;x&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;=&nbsp;2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>known&nbsp;fact:</code><br>
<code>&nbsp;&nbsp;x&nbsp;=&nbsp;2</code><br>
<br>
<code>goal:</code><br>
<code>&nbsp;&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3</code><br>
<br>
<code>proof:</code><br>
<code>&nbsp;&nbsp;resolve&nbsp;x&nbsp;by&nbsp;x&nbsp;=&nbsp;2</code><br>
<code>&nbsp;&nbsp;reduce&nbsp;2&nbsp;+&nbsp;1&nbsp;by&nbsp;builtin&nbsp;arithmetic</code><br>
<code>&nbsp;&nbsp;conclude&nbsp;x&nbsp;+&nbsp;1&nbsp;=&nbsp;3</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>abstract_prop&nbsp;p(x,&nbsp;y)</code><br>
<code>forall&nbsp;a,&nbsp;b,&nbsp;a2,&nbsp;b2&nbsp;set:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;a&nbsp;=&nbsp;a2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;b&nbsp;=&nbsp;b2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;$p(a,&nbsp;b)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$p(a2,&nbsp;b2)</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>example&nbsp;(p&nbsp;:&nbsp;α&nbsp;→&nbsp;β&nbsp;→&nbsp;Prop)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;{a&nbsp;a2&nbsp;:&nbsp;α}&nbsp;{b&nbsp;b2&nbsp;:&nbsp;β}</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;(ha&nbsp;:&nbsp;a&nbsp;=&nbsp;a2)&nbsp;(hb&nbsp;:&nbsp;b&nbsp;=&nbsp;b2)&nbsp;(hp&nbsp;:&nbsp;p&nbsp;a&nbsp;b)&nbsp;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;p&nbsp;a2&nbsp;b2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;subst&nbsp;a2</code><br>
<code>&nbsp;&nbsp;subst&nbsp;b2</code><br>
<code>&nbsp;&nbsp;exact&nbsp;hp</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>abstract_prop&nbsp;p(x)</code><br>
<br>
<code>know&nbsp;forall&nbsp;x&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;$p(x)</code><br>
<br>
<code>$p(2)</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>example&nbsp;(p&nbsp;:&nbsp;ℝ&nbsp;→&nbsp;Prop)&nbsp;(h&nbsp;:&nbsp;∀&nbsp;x&nbsp;:&nbsp;ℝ,&nbsp;p&nbsp;x)&nbsp;:&nbsp;p&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;exact&nbsp;h&nbsp;2</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>{1,&nbsp;2}&nbsp;$in&nbsp;{{},&nbsp;{1,&nbsp;2}}</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;({1,&nbsp;2}&nbsp;:&nbsp;Set&nbsp;ℕ)&nbsp;∈&nbsp;({∅,&nbsp;{1,&nbsp;2}}&nbsp;:&nbsp;Set&nbsp;(Set&nbsp;ℕ))&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;simp</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>forall&nbsp;i&nbsp;{1,&nbsp;2}:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;i&nbsp;=&nbsp;1&nbsp;or&nbsp;i&nbsp;=&nbsp;2</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;{i&nbsp;:&nbsp;ℕ}&nbsp;(hi&nbsp;:&nbsp;i&nbsp;∈&nbsp;({1,&nbsp;2}&nbsp;:&nbsp;Finset&nbsp;ℕ))&nbsp;:&nbsp;i&nbsp;=&nbsp;1&nbsp;∨&nbsp;i&nbsp;=&nbsp;2&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;simpa&nbsp;using&nbsp;hi</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>{1,&nbsp;2}&nbsp;$in&nbsp;power_set({1,&nbsp;2,&nbsp;3})</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;({1,&nbsp;2}&nbsp;:&nbsp;Set&nbsp;ℕ)&nbsp;⊆&nbsp;({1,&nbsp;2,&nbsp;3}&nbsp;:&nbsp;Set&nbsp;ℕ)&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;intro&nbsp;x&nbsp;hx</code><br>
<code>&nbsp;&nbsp;simp&nbsp;at&nbsp;hx</code><br>
<code>&nbsp;&nbsp;simp&nbsp;[hx]</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>prove:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;let&nbsp;A,&nbsp;B&nbsp;set:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;A&nbsp;$subset&nbsp;B</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;forall&nbsp;x&nbsp;A:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;$in&nbsp;B</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>example&nbsp;{α&nbsp;:&nbsp;Type}&nbsp;{A&nbsp;B&nbsp;:&nbsp;Set&nbsp;α}&nbsp;(hAB&nbsp;:&nbsp;A&nbsp;⊆&nbsp;B)&nbsp;{x&nbsp;:&nbsp;α}&nbsp;(hx&nbsp;:&nbsp;x&nbsp;∈&nbsp;A)&nbsp;:&nbsp;x&nbsp;∈&nbsp;B&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;exact&nbsp;hAB&nbsp;hx</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>by&nbsp;contra:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;{1,&nbsp;2,&nbsp;3}&nbsp;!=&nbsp;{1,&nbsp;2}</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,&nbsp;2,&nbsp;3})&nbsp;=&nbsp;3</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,&nbsp;2})&nbsp;=&nbsp;2</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;count({1,&nbsp;2,&nbsp;3})&nbsp;=&nbsp;count({1,&nbsp;2})</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;impossible&nbsp;3&nbsp;=&nbsp;2</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;:&nbsp;({1,&nbsp;2,&nbsp;3}&nbsp;:&nbsp;Finset&nbsp;ℕ)&nbsp;≠&nbsp;({1,&nbsp;2}&nbsp;:&nbsp;Finset&nbsp;ℕ)&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;intro&nbsp;h</code><br>
<code>&nbsp;&nbsp;have&nbsp;hcard&nbsp;:=&nbsp;congrArg&nbsp;Finset.card&nbsp;h</code><br>
<code>&nbsp;&nbsp;norm_num&nbsp;at&nbsp;hcard</code>
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
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>prop&nbsp;prime(a&nbsp;N_pos):</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;&lt;=&nbsp;a</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;forall&nbsp;b&nbsp;N_pos:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;&lt;=&nbsp;b&nbsp;&lt;&nbsp;a</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;a&nbsp;%&nbsp;b&nbsp;!=&nbsp;0</code><br>
<br>
<code>know:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;forall&nbsp;a,&nbsp;k&nbsp;N_pos:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;k&nbsp;&lt;=&nbsp;a</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;%&nbsp;k&nbsp;=&nbsp;0</code><br>
<br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;forall&nbsp;a&nbsp;N_pos:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;&lt;=&nbsp;a</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;exist&nbsp;k&nbsp;N_pos&nbsp;st&nbsp;{$prime(k),&nbsp;a&nbsp;%&nbsp;k&nbsp;=&nbsp;0}</code><br>
<br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;forall&nbsp;a&nbsp;N_pos:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;a&nbsp;&lt;=&nbsp;product(1,&nbsp;a,&nbsp;'N_pos(x){x})</code><br>
<br>
<code>claim&nbsp;forall!&nbsp;a&nbsp;N_pos:&nbsp;2&nbsp;&lt;=&nbsp;a&nbsp;=&gt;&nbsp;exist&nbsp;k&nbsp;N_pos&nbsp;st&nbsp;{k&nbsp;&gt;&nbsp;a,&nbsp;$prime(k)}:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;2&nbsp;&lt;=&nbsp;a&nbsp;&lt;=&nbsp;product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;&lt;=&nbsp;product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;+&nbsp;1</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;have&nbsp;by&nbsp;exist&nbsp;k&nbsp;N_pos&nbsp;st&nbsp;{$prime(k),&nbsp;(product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;+&nbsp;1)&nbsp;%&nbsp;k&nbsp;=&nbsp;0}:&nbsp;k</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;by&nbsp;cases&nbsp;k&nbsp;&gt;&nbsp;a:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;k&nbsp;&lt;=&nbsp;a:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;%&nbsp;k&nbsp;=&nbsp;0</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;+&nbsp;1)&nbsp;%&nbsp;k&nbsp;=&nbsp;(product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;%&nbsp;k&nbsp;+&nbsp;1&nbsp;%&nbsp;k)&nbsp;%&nbsp;k&nbsp;=&nbsp;(0&nbsp;+&nbsp;1)&nbsp;%&nbsp;k&nbsp;=&nbsp;1</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;impossible&nbsp;(product(1,&nbsp;a,&nbsp;'N_pos(x){x})&nbsp;+&nbsp;1)&nbsp;%&nbsp;k&nbsp;=&nbsp;0</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;case&nbsp;k&nbsp;&gt;&nbsp;a:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;do_nothing</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;witness&nbsp;exist&nbsp;k&nbsp;N_pos&nbsp;st&nbsp;{k&nbsp;&gt;&nbsp;a,&nbsp;$prime(k)}&nbsp;from&nbsp;k</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>import&nbsp;Mathlib</code><br>
<br>
<code>example&nbsp;(N&nbsp;:&nbsp;ℕ)&nbsp;:&nbsp;∃&nbsp;p&nbsp;≥&nbsp;N,&nbsp;Nat.Prime&nbsp;p&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;have&nbsp;hN0&nbsp;:&nbsp;0&nbsp;&lt;&nbsp;N&nbsp;!&nbsp;:=&nbsp;by&nbsp;exact&nbsp;Nat.factorial_pos&nbsp;N</code><br>
<code>&nbsp;&nbsp;have&nbsp;hN2&nbsp;:&nbsp;2&nbsp;≤&nbsp;N&nbsp;!&nbsp;+&nbsp;1&nbsp;:=&nbsp;by&nbsp;omega</code><br>
<code>&nbsp;&nbsp;obtain&nbsp;⟨p,&nbsp;hp,&nbsp;hpN⟩&nbsp;:&nbsp;∃&nbsp;p&nbsp;:&nbsp;ℕ,&nbsp;Nat.Prime&nbsp;p&nbsp;∧&nbsp;p&nbsp;∣&nbsp;N&nbsp;!&nbsp;+&nbsp;1&nbsp;:=</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;Nat.exists_prime_and_dvd&nbsp;hN2</code><br>
<code>&nbsp;&nbsp;obtain&nbsp;⟨k,&nbsp;hk⟩&nbsp;:=&nbsp;hpN</code><br>
<code>&nbsp;&nbsp;use&nbsp;p</code><br>
<code>&nbsp;&nbsp;constructor</code><br>
<code>&nbsp;&nbsp;·&nbsp;by_contra&nbsp;hlt</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;have&nbsp;hp_dvd_factorial&nbsp;:&nbsp;p&nbsp;∣&nbsp;N&nbsp;!&nbsp;:=&nbsp;Nat.Prime.dvd_factorial&nbsp;hp&nbsp;(Nat.le_of_not_gt&nbsp;hlt)</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;have&nbsp;hp_dvd_one&nbsp;:&nbsp;p&nbsp;∣&nbsp;1&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;have&nbsp;hp_dvd_sum&nbsp;:&nbsp;p&nbsp;∣&nbsp;(N&nbsp;!&nbsp;+&nbsp;1)&nbsp;-&nbsp;N&nbsp;!&nbsp;:=&nbsp;Nat.dvd_sub&nbsp;hpN&nbsp;hp_dvd_factorial</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;simpa&nbsp;using&nbsp;hp_dvd_sum</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;exact&nbsp;Nat.Prime.not_dvd_one&nbsp;hp&nbsp;hp_dvd_one</code><br>
<code>&nbsp;&nbsp;·&nbsp;exact&nbsp;hp</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>abstract_prop&nbsp;positive(x)</code><br>
<br>
<code>know&nbsp;forall&nbsp;x&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;&gt;&nbsp;0</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$positive(x)</code><br>
<br>
<code>forall&nbsp;x&nbsp;R:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;x&nbsp;&gt;&nbsp;0</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;=&gt;:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$positive(x)</code><br>
<br>
<code>This&nbsp;is&nbsp;not&nbsp;Litex:</code><br>
<br>
<code>forall&nbsp;P&nbsp;Prop:</code><br>
<code>&nbsp;&nbsp;&nbsp;&nbsp;...</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>example&nbsp;(P&nbsp;Q&nbsp;:&nbsp;Prop)&nbsp;(hP&nbsp;:&nbsp;P)&nbsp;(hPQ&nbsp;:&nbsp;P&nbsp;→&nbsp;Q)&nbsp;:&nbsp;Q&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;exact&nbsp;hPQ&nbsp;hP</code>
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

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>x&nbsp;=&nbsp;2</code><br>
<br>
<code>This&nbsp;is&nbsp;not&nbsp;Litex:</code><br>
<br>
<code>have&nbsp;h&nbsp;=&nbsp;(x&nbsp;=&nbsp;2)</code><br>
<code>some_statement(h)</code>
    </td>
    <td style="border: 1px solid black; padding: 4px; line-height: 1.45; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<code>example&nbsp;(P&nbsp;Q&nbsp;:&nbsp;Prop)&nbsp;(hP&nbsp;:&nbsp;P)&nbsp;(h&nbsp;:&nbsp;P&nbsp;→&nbsp;Q)&nbsp;:&nbsp;Q&nbsp;:=&nbsp;by</code><br>
<code>&nbsp;&nbsp;exact&nbsp;h&nbsp;hP</code>
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
