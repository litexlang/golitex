## Litex: Scale Formal Reasoning In AI Age

Litex[^1]是一门**简单易学、表达力强的形式化语言**，让每一步**逻辑推理**、每一段关键代码、每一个 AI Agent 都能被形式化验证所**守护并加速**。**它能把构建形式化数据集的成本和门槛降低10倍。**

例1：多元线性方程组：解方程 2x + 3y = 10 和 4x + 5y = 14。

<table style="border-collapse: collapse; width: 100%; font-size: 12px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 30%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 70%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
      <code>obj x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br><br>
      <code>2 * (2 * x + 3 * y) = 2 * 10</code><br>
      <code>4* x + 6 * y = 2 * 10</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = y</code><br>
      <code>y = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18</code><br>
      <code>2 * x + 18 - 18 = -8</code><br>
      <code>(2 * x) / 2 = -8 / 2</code><br>
      <code>(2 * x) / 2 = x</code><br>
      <code>x = -4</code>
    </td>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
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


| 方面       | Litex            | Lean                      |
| ----------- | ---------------- | ------------------------- |
| **书写** | 直接写计算步骤，类似自然语言    | 语法不直观。数学本身是一门很难的学科，而翻译成Lean的工作量甚至比思考数学本身还大得多。Lean的库只能部分减轻其负担 |
| **阅读** | 未经训练的普通人就能直观地理解         | 需掌握 tactic / type / rw / ring / simp / exact / ring_exp / norm_num 等。初等方程尚且如此，可想而知进阶数学有多复杂 |
| **语义** | 每步清晰语义，AI 易训练与验证 | 严重依赖复杂的 tactic，需要给一切已知事实取名字记忆，严重增加用户负担，不同数学领域有不同常用词，学习成本极高 |
| **门槛** | 初中生即可上手，适合众包       | 即便是使用它训练 AI 的研究者，也往往无法理解模型生成的证明过程，只能依赖 API 进行验证，难以掌控模型实际学到了什么 |
| **数据成本** | 1倍于正常写数学        | 陶哲轩提到，Lean的表达复杂度10倍于正常写数学。如果能将成本降低到1倍，形式化所有数学书、知识的时机就成熟了[^2] |

Litex 让逻辑推理像编程一样可控、可拓展，实现真正的可验证与可规模化。它的语法简单，更多人能轻松上手形式化语言，将其应用到各自领域，为未来 AI 的安全性、通用性与功能性提供保障。

[^1]: 在官网上试试Litex: https://litexlang.org/playground . Litex 源代码：https://github.com/litexlang/litex . 邮件联系：litexlang@outlook.com

[^2]: Terence Tao: AI Will Become Mathematicians’ ‘Co-Pilot’. 2024.6. https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/