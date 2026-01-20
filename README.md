<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: A Simple Formal Language Learnable in 2 Hours

## For Verifiable Intellectual Discovery in AI Age

**version v0.2-beta (not yet ready for production use)**  
*Jiachen Shen and The Litex Team*

[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)

</div>

## What is Litex?

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex is a simple open-source computer language for mathematical proofs. It aims to express mathematics as code with verified correctness while staying as close to natural language as possible. This is really an eye-opening exploration of finding `what mathematics is`! ([Github](https://github.com/litexlang/golitex), [Official Site](https://litexlang.com))

Formal code written in Litex is typically 2-10x simpler than traditional formal languages, and looks almost the same as how math is written in natural language, meaning Litex could be a game changer for both non-formal-language experts from STEM background and frontier AI research.

Here is an example of how Litex code looks like:

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

Here is a thorough collection of comparison between Litex and Lean: [Litex vs Lean Set Theory Examples](https://litexlang.com/doc/Litex_vs_Lean/Set_Theory). Visit our [website](https://litexlang.com) for more details. Dataset on [Hugging Face](https://huggingface.co/litexlang) is also available.

## How Litex Works

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_— David Hilbert_

Litex achieves its simplicity by imitating how people reason and how mathematics works. Litex is based on set theory. It searches for known facts mechanically and effectively to prove new facts for you. The user no longer has to memorize and recall known facts and inference rules by hand. Each Litex statement has and only has some of the following 4 effects: define, verify, memorize and infer, which is printed out in the output, making the user easy to know how the proof process works.

Among the 4 effects, verification is the most important one. Litex uses `match and substitution` to use `forall` facts to verify the correctness of the statements. It's impossible to explain how it works in a few words. So we put an example here. When `forall x human => $intelligent(x)` is already stored in memory and `Jordan $in human` is also stored in memory, when the users type `$intelligent(Jordan)`, Litex will substitute `Jordan` with `x` in the statement `forall x human => $intelligent(x)` and check if the statement is true. If it is, the statement is verified.

Think of this: when the user inputs a fact with proposition name `intelligent`, Litex will search all known facts with proposition name `intelligent` (including `forall` facts like `forall x human => $intelligent(x)` and specific facts like `$intelligent(Jordan)`) and check if the given fact matches the known fact. If matched, then it is correct. It works like `ctrl+f` in your browser. The reason why Lean cannot do this is that Lean can pass prop as forall parameter, so its search space is the whole memory, instead of the memory of the current proposition.

Even for 10-year-old beginners, Litex is straightforward to learn and use. Visit our [How Litex Works](https://litexlang.com/doc/How_Litex_Works/Introduction) for more details.

## Resources And Community

_The best way to predict future is to create it._

_-- Alan Kay_

Litex is nothing without its community and technical ecosystem.

Resources for Litex users:

1. Our official [website](https://litexlang.com) contains tutorials, cheat sheets, examples, documentation, collaboration opportunities, and more for Litex. All documents on our [website](https://litexlang.com) are open-sourced [here](https://github.com/litexlang/litex-official-documents)
2. Use [pylitex](https://github.com/litexlang/pylitex) to call Litex in Python
3. Our Community is on [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)!
4. Email us [here](mailto:litexlang@outlook.com).
5. [Congratulations! Litex achieves top 10 on Hacker News on 2025-09-27!!](https://news.ycombinator.com/item?id=45369629)
6. Our organization's Github is [here](https://github.com/litexlang/). The kernel is [here](https://github.com/litexlang/golitex).
7. Our dataset on Hugging Face is [here](https://huggingface.co/litexlang).

## References

_If I have seen further [than others], it is by standing on the shoulders of giants._

_- Isaac Newton_

Although Litex is a very pragmatic language which contains and only contains the proof methods, axioms, keywords, etc. that people need in their daily mathematical work—things that are often so taken for granted that people usually don't even notice them —- it is equally important to note that Litex indeed has gained great conceptual inspiration from the masters.

Mathematics references:

1. Avigad Jeremy: Foundations https://arxiv.org/abs/2009.09541
2. Terence Tao: Analysis I Fourth edition, 2022. https://terrytao.wordpress.com/books/analysis-i/
3. Weyl Hermann: Philosophy of Mathematics and Natural Science https://www.jstor.org/stable/j.ctv1t1kftd
4. Bertrand Russell: Introduction to Mathematical Philosophy https://people.umass.edu/klement/imp/imp.pdf
5. David Hilbert: Foundations of Geometry https://math.berkeley.edu/~wodzicki/160/Hilbert.pdf

AI references:

1. DeepSeek-R1: Boosting Reasoning Capability in LLMs via Reinforcement Learning
2. AlphaGeometry: An Olympiad-level AI system for geometry 
3. Seed-Prover: Deep and Broad Reasoning for Automated Theorem Proving

## Special Thanks

_巴黎挺好，未来一定更好。未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. It is so fortunate to receive tremendous help from friends and colleagues throughout this journey of designing, implementing, and growing Litex into a community. Without their support, Litex would not have had the chance to succeed.

I am deeply grateful to Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Siqi Guo, Haoyang Shi, Chengyang Zhu, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Lei Bai for their emotional support and insightful advice. I am certain this list of special thanks will only grow longer in the future.