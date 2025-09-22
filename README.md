<div align="center">
<img src="./logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Simply Scale Formal Reasoning In AI Era

**version v0.1.10-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team*

[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Online Playground](https://img.shields.io/badge/Online%20Playground-darkgreen?logo=playground)](https://litexlang.com/playground)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)

</div>

## Litex: The First Formal Language Learnable in 1–2 Hours

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex([website](https://litexlang.com)) is a simple, intuitive, and open-source formal language for coding reasoning ([Star the repo!](https://github.com/litexlang/golitex)). It ensures every step of your reasoning is correct, and is actually the first reasoning formal language (or formal language for short) that can be learned by anyone in 1–2 hours, even without math or programming background.

Making Litex intuitive to both human and AI is the mission of Litex. That is how Litex scales formal reasoning: making it accessible to more people, applicable to more complex problems, and usable by large-scale AI systems. Here is a comparison between Litex and traditional formal language Lean.

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
      <code>2 * (2 * x + 3 * y) = 2 * 10 = 4 * x + 6 * y</code><br>
      <code>y = (4 * x + 6 * y) - (4 * x + 5 * y) = 2 * 10 - 14 = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18 = -8</code><br>
      <code>x = (2 * x) / 2 = -8 / 2 = -4</code><br>
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

Even Kids can formalize the multivariate equation in Litex in 2 minutes, while it require an experienced expert hours of work in Lean 4. It is a typical example of how Litex lowers the entrance barrier by 10x, lowers the cost of constructing formalized proofs by 10x, making formalization as easy and fast as natural writing. No foreign keywords, no twisted syntax, or complex semantics. Just plain reasoning.

## Resources And Community

_The best way to predict future is to create it._

_-- Alan Kay_

Litex is nothing without its community and technical ecosystem. Here is a list of resources and community for Litex:

1. Our official [website](https://litexlang.com) contains tutorials, cheatsheets, examples, documentation, collaboration opportunities, and more for Litex. All documents on our [website](https://litexlang.com) are open-sourced [here](https://github.com/litexlang/litex-official-documents)
2. Learn Litex [online](https://litexlang.com/doc/Tutorial/Introduction). A short list of major Litex statements and their usage are shown in the [cheat sheet](https://litexlang.com/doc/Litex_Cheatsheet).
3. You can run litex on your own computer， start from [here](https://litexlang.com/doc/Start)
4. [Litex standard library](https://github.com/litexlang/litex-stdlib) is under active development. **Contribute to it and earn impact rewards!**
5. Use [pylitex](https://github.com/litexlang/pylitex) to call Litex in Python
6. Litex achieves 100% accuracy on gsm8k dataset without any training [Github](https://github.com/litexlang/litex-gsm8k-killer)
7. [Litex Dataset](https://huggingface.co/litexlang) is on Hugging Face. **Contribute to it and earn impact rewards!**
8. Here is a really powerful Litex Agent [Github](https://github.com/litexlang/litex-agent). It is so powerful that much code in our standard library is generated by it!
9. AI researchers interested in Litex might find [Litex LLM Dev](https://github.com/litexlang/litex-llm-dev) useful. Contact us if you are interested in collaborating on this project!
10. Our Community is on [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/). Email me [here](mailto:litexlang@outlook.com) if you are interested in joining!

All of our [repositories](https://github.com/orgs/litexlang/repositories) are open-sourced. Just issue PRs and tell us any ideas about Litex! Maybe we can build the future together!

## Special Thanks

_Sometimes it is the very people who no one imagines anything of who do the things that no one can imagine._

_– Alan Turing_

I, Jiachen Shen, creator of Litex, have been fortunate to receive tremendous help from friends and colleagues throughout this journey of designing, implementing, and growing Litex into a community. Without their support, Litex would not have had the chance to succeed.

I owe special thanks to my friend Zhaoxuan Hong, who built Litex’s powerful toolchains and has supported the project from the very beginning. I am also deeply grateful to Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Siqi Guo, Haoyang Shi, Chengyang Zhu, Chenxuan Huang for their invaluable contributions. I am certain this list of special thanks will only grow longer in the future.