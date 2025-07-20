## Litex: Scale Formal Reasoning In AI Age

Litex是一门简单直观、易学易用的形式化语言。它让每一步逻辑推理、每一段关键代码、每一个 AI Agent 都能被形式化验证所守护并加速。相比主流形式化语言如Lean，Litex把构建形式化数据集的成本和门槛降低了10倍。创始人沈嘉辰，洪昭宣。

例1：多元线性方程组：解方程 2x + 3y = 10 和 4x + 5y = 14。您可以在官网沙盒[1]上运行这个和更多例子。

<table style="border-collapse: collapse; width: 100%; font-size: 12px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 30%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 70%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px;line-height: 1.5">
      <code>obj x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br>
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
      <code>import Mathlib.Tactic</code><br>
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

| 方面         | Litex                          | Lean                                                         |
| ------------ | ------------------------------ | ------------------------------------------------------------ |
| **书写**     | 直接写计算步骤，类似自然语言   | 语法不直观。数学本身是一门很难的学科，而翻译成Lean的工作量甚至比思考数学本身还大得多。Lean的库只能部分减轻其负担 |
| **阅读**     | 未经训练的普通人就能直观地理解 | 需掌握 tactic / type / rw / ring / simp / exact / ring_exp / norm_num 等。初等方程尚且如此，可想而知进阶数学有多复杂 |
| **语义**     | 每步清晰语义，AI 易训练与验证  | 严重依赖复杂的 tactic，需要给一切已知事实取名字记忆，严重增加用户负担，不同数学领域有不同常用词，学习成本极高 |
| **门槛**     | 初中生即可上手，适合众包       | 用Lean训练 AI 的研究者，也只有不到20%能理解模型生成的证明过程，只能依赖 API 进行验证，难以掌控模型实际学到了什么 |
| **数据成本** | 1倍于正常写数学                | 陶哲轩提到，Lean的表达复杂度10倍于正常写数学。如果能将成本降低到1倍，形式化所有数学书、知识的时机就成熟了[2] |

官网的 Litex to LaTeX Compiler\[1] 可将 Litex 代码转换为 LaTeX，降低用户上手门槛。如今 DeepSeek、Google、Meta、OpenAI 等正重金布局形式化语言，Litex 有望成为 AI 推理与智能体开发的基础设施，成为 AI 淘金热中的类 CUDA 铲子型工具。我们的愿景是让形式化语言和日常表达一样简单，让所有人都能轻松使用形式化语言。

<div style="font-size: 11px; line-height: 1.1; border-collapse: collapse; width: 100%;">
[1] 官网沙盒: https://litexlang.org/playground . 源代码：https://github.com/litexlang/golitex . 邮件联系：litexlang@outlook.com. 
</div>

<div style="font-size: 11px; line-height: 1.1; border-collapse: collapse; width: 100%;">
[2] 陶哲轩关于AI和形式化语言如何改变数学的采访 https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/
</div>