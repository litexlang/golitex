<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: A Simple Formal Language Learnable in 2 Hours, Not 1 Year

**version v0.1.10-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team*

[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)

</div>

## Simple, Intuitive, Expressive — Learnable For Humans & AI 

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

[Congratulations! Litex achieves top 10 on Hacker News on 2025-09-27!!](https://news.ycombinator.com/item?id=45369629)

Litex([website](https://litexlang.com)) is a simple, intuitive, and expressive open-source formal language for coding reasoning ([Star the repo!](https://github.com/litexlang/golitex)). It ensures every step of your reasoning is correct, and is actually the first formal language that can be learned by anyone in 2 hours. In fact, Litex is so close to natural language that sometimes it makes you forget you are using a formal language!

Making Litex intuitive to both humans and AI is Litex's core mission. Just like how Python lowers the barrier of programming by 10x compared with C/C++, Litex lowers the barrier of formal reasoning by 10x compared with previous formal languages like Lean. This is how Litex scales formal reasoning: by making it accessible to more people, applicable to more complex problems, and usable by large-scale AI systems. Here is an example:

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

While Lean 4 is a powerful and rigorous proof assistant ideal, it requires months of training and years of experience to master. Litex takes a different approach: prioritizing accessibility and ease of use, enabling even beginners to formalize naive tasks like multivariate equations in minutes. For many everyday reasoning tasks, especially when rapid prototyping and intuitive syntax matter most, Litex offers a more approachable path. Each tool has its place — choose the one that best fits your needs and experience level!

Our mission is to make Litex the most accessible and usable formal language for coding reasoning. We aim to solve the most challenging problems faced by the AI community, i.e. the challenge of efficient, scalable, and reliable coding reasoning. Let's build the future together!

## Resources And Community

_The best way to predict future is to create it._

_-- Alan Kay_

Litex is nothing without its community and technical ecosystem.

Resources for Litex users:

1. Our official [website](https://litexlang.com) contains tutorials, cheat sheets, examples, documentation, collaboration opportunities, and more for Litex. All documents on our [website](https://litexlang.com) are open-sourced [here](https://github.com/litexlang/litex-official-documents)
2. Learn Litex [online](https://litexlang.com/doc/Tutorial/Introduction). A short list of major Litex statements and their usage are shown in the [cheat sheet](https://litexlang.com/doc/Litex_Cheatsheet).
3. You can run litex on your own computer， start from [here](https://litexlang.com/doc/Quick_Start)
4. [Litex standard library](https://github.com/litexlang/litex-stdlib) is under active development. **Contribute to it and earn impact rewards!**
5. Use [pylitex](https://github.com/litexlang/pylitex) to call Litex in Python
6. Our Community is on [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)!
7. Email us [here](mailto:litexlang@outlook.com).

Resources for AI researchers who want to develop Litex-based AI systems, mostly developed by the Litex open-source community:

1. Litex achieves 100% accuracy on gsm8k dataset without any training [Github](https://github.com/litexlang/litex-gsm8k-killer)
2. [Litex Dataset](https://huggingface.co/litexlang) is on Hugging Face. **Contribute to it and earn impact rewards!**
3. Here is a really powerful Litex Agent [Github](https://github.com/litexlang/litex-agent). It is so powerful that much code in our standard library is generated by it!
4. AI researchers interested in Litex might find [Litex LLM Dev](https://github.com/litexlang/litex-llm-dev) useful. Contact us if you are interested in collaborating on this project!

All of our [repositories](https://github.com/orgs/litexlang/repositories) are open-sourced. Just issue PRs and tell us any ideas about Litex! Maybe we can build the future together!

## Special Thanks

_Sometimes it is the very people who no one imagines anything of who do the things that no one can imagine._

_– Alan Turing_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. It is so fortunate to receive tremendous help from friends and colleagues throughout this journey of designing, implementing, and growing Litex into a community. Without their support, Litex would not have had the chance to succeed.

I am deeply grateful to Zhaoxuan Hong, Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Siqi Guo, Haoyang Shi, Chengyang Zhu, Chenxuan Huang, Yan Lu for their invaluable contributions. I am certain this list of special thanks will only grow longer in the future.