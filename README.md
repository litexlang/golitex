<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Simply Scale Formal Reasoning

**version v0.1.10-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team*

[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.org)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.org/playground)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)

</div>

## Litex: The First Formal Language Learnable in 1–2 Hours

*Visit [Official Website](https://litexlang.org/) to learn more about Litex. Visit [Tutorial](https://litexlang.org/doc/Tutorial/Introduction) to learn how to use Litex and try some examples. Visit [Start](https://litexlang.org/doc/Start) to start using Litex (online, locally, in Python, in Jupyter Notebook, etc.).*

Litex is a simple and intuitive formal language for coding reasoning. It ensures every step of your reasoning is correct, and is actually the first reasoning formal language (or formal language for short) that can be learned by anyone in 1–2 hours, even without math or programming background.

Its goal is to scale formal reasoning in AI age. Scaling formal reasoning has several meanings: 1. Scaling the number of people who can use formal reasoning; 2. Scaling the complexity of the problems that can be solved by formal reasoning. 3. Scaling AI to perform formal reasoning.

Traditional formal languages are too complex. Litex lowers the barrier by 10x, making formalization as easy and fast as natural writing. Here is an comparison between Litex and Lean 4 (a traditional formal language) about finding out the solution to a linear equation. Kids can solve it in Litex in 2 minutes, while it require an experienced expert hours of work in Lean 4.

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>let x R, y R:</code><br>
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

The simplicity of Litex enables both the large-scale adoption of formal languages and their deep integration into AI systems. In Litex, there is no foreign keywords, twisted syntax, or complex semantics, just plain reasoning. Litex benefits both AI research and the math community. 

Scaling formal reasoning has several meanings: 1. Scaling the number of people who can use formal reasoning; 2. Scaling the complexity of the problems that can be solved by formal reasoning. 3. Scaling AI to perform formal reasoning.

## Contact & Contribute to Litex

Hi, I’m Jiachen Shen, creator of Litex. You’re warmly invited to join the Litex community and grow with us. Our key directions:

Dataset – from elementary problems to IMO, textbooks, and research papers. This dataset powers AI training and reasoning.

Litex + AI – embedding Litex into AI workflows to make reasoning scalable, reliable, and 10x more accessible.

Our source code is on [Github](https://github.com/litexlang/golitex). The source code of the tutorial is on [Tutorial](https://github.com/litexlang/litex-tutorial). The Python package of Litex is [pylitex](https://github.com/litexlang/pylitex)

MAKE MONEY BY CONTRIBUTING! Visit [Task Board](https://litexlang.org/task-board) to earn by solving tasks, or [Collaboration](https://litexlang.org/collaboration) to discuss bigger projects.

Contact me via [email](mailto:litexlang@outlook.com) or join the [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/).

## Special Thanks

Throughout this journey of designing, implementing, and growing Litex into a community, I (Jiachen Shen, creator of Litex) have been fortunate to receive tremendous help from friends and colleagues. Without their support, Litex would not have had the chance to succeed.

I owe special thanks to my coworker Zhaoxuan Hong, who built Litex’s powerful toolchains and has supported the project from the very beginning. The Litex project is also deeply grateful to Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Sheng Xu, Siqi Guo, Haoyang Shi, and Chengyang Zhu for their invaluable contributions.

Moreover, I cannot fully express my gratitude to all those who have actively contributed to the Litex community. I am certain this list of special thanks will only grow longer in the future.

We warmly invite you to join us. The best way to predict future is to create it. Let’s build the future together!