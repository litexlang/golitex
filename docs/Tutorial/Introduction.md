# Tutorial Introduction

Try all snippets in browser: https://litexlang.com/doc/Tutorial/Introduction

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/Introduction.md


Jiachen Shen and The Litex Team

## What is Litex?

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex is a simple and intuitive open-source computer language for mathematical proofs. It encodes a philosophy of everyday mathematical thinking — the non-expert’s angle — where the problem leads and notation follows.

In the best case, what you write is organized around the problem — not bent to satisfy the formal language you happen to be using. Litex is an attempt to move practice closer to that ideal. Here is an example of how Litex code looks like:

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
    <code>forall x R, y R:</code><br>
    <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
    <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br>
    <code>&nbsp;&nbsp;=>:</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * (2 * x + 3 * y) = 2 * 10 = 4 * x + 6 * y</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;y = (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 = 6</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 3 * 6 = 10</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 18 - 18 = 10 - 18 = -8</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;x = (2 * x) / 2 = -8 / 2 = -4</code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

As you can see, Litex is much more concise and readable than Lean. It doesn't require you to memorize and recall known facts and inference rules by hand, making it possible for you to write complex statements with ease at 2-10 times efficiency than Lean. In fact, it even runs 2-10 times faster than Lean.
