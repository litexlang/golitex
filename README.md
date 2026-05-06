<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: A Simple Formal Language Learnable in 2 Hours

**version 0.9.73-beta (not yet ready for production use)**  
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

Litex is a simple and intuitive open-source computer language for mathematical proofs. It is built around a practical idea: everyday mathematics should be easy to write down as code, checked rigorously by a computer, and still scale to larger proofs.

Litex is designed to feel friendly for a few reasons:

1. **It starts from set theory.** Litex uses the mathematical foundation most people already meet in ordinary mathematics: sets, elements, functions, tuples, numbers, and relations. You do not need to start by thinking in an abstract type-theory style.
2. **Its basic pieces are easy to read.** A statement says what action you are taking, an object is the mathematical thing you are talking about, and a fact is a claim such as `x = 2` or `x $in R`. Each piece is simple on its own. The hard part is that basic mathematics has many small relationships between these pieces, and Litex builds those relationships in for you.
3. **Verification is based on matching and substitution.** Litex searches known facts and applies them mechanically. You often do not need to name every intermediate fact just so you can mention it later; the checker can remember and reuse facts in the background.

The result is a different style of formal proof: daily mathematical reasoning, written as code, made strict, and made scalable. Here is a small example:

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
    <code>forall x R:</code><br>
    <code>&nbsp;&nbsp;x = 2</code><br>
    <code>&nbsp;&nbsp;=>:</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;x + 1 = 3</code><br>
    <code>&nbsp;&nbsp;&nbsp;&nbsp;x^2 = 4</code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by</code><br>
      <code>&nbsp;&nbsp;have h_add : x + 1 = 3 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [h]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num</code><br>
      <code>&nbsp;&nbsp;have h_square : x ^ 2 = 4 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [h]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;norm_num</code><br>
      <code>&nbsp;&nbsp;exact ⟨h_add, h_square⟩</code>
    </td>
  </tr>
</table>

This small example shows the intended feel: Litex code looks close to the mathematical steps, while the checker handles routine rewriting, arithmetic, and reuse of known facts.

## How Litex Works

_Mathematics is nothing more than a game played according to certain simple rules with meaningless marks on a paper._

_— David Hilbert_

Litex achieves its simplicity by imitating how people reason and how mathematics works. Litex is based on set theory. It searches for known facts mechanically and effectively to prove new facts for you. The user no longer has to memorize and recall known facts and inference rules by hand. Each Litex statement has and only has some of the following 4 effects: define, verify, memorize and infer, which is printed out in the output, making the user easy to know how the proof process works.

Among the 4 effects, verification is the most important one. Litex uses `match and substitution` to use `forall` facts to verify the correctness of the statements. It's impossible to explain how it works in a few words. So we put an example here. When `forall x human => $intelligent(x)` is already stored in memory and `Jordan $in human` is also stored in memory, when the users type `$intelligent(Jordan)`, Litex will substitute `Jordan` with `x` in the statement `forall x human => $intelligent(x)` and check if the statement is true. If it is, the statement is verified.

Think of this: when the user inputs a fact with proposition name `intelligent`, Litex will search all known facts with proposition name `intelligent` (including `forall` facts like `forall x human => $intelligent(x)` and specific facts like `$intelligent(Jordan)`) and check if the given fact matches the known fact. If matched, then it is correct. It works like `ctrl+f` in your browser. The reason why Lean cannot do this is that Lean can pass prop as forall parameter, so its search space is the whole memory, instead of the memory of the current proposition.

Even for 10-year-old beginners, Litex is straightforward to learn and use.

## Resources And Community

_The best way to predict future is to create it._

_-- Alan Kay_

Litex is nothing without its community and technical ecosystem.

Resources for Litex users:

1. [Official site](https://litexlang.com)
2. Use [pylitex](https://github.com/litexlang/pylitex) to call Litex in Python
3. Our Community is on [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)!
4. Email us [here](mailto:litexlang@outlook.com).
5. [Congratulations! Litex achieves top 10 on Hacker News on 2025-09-27!!](https://news.ycombinator.com/item?id=45369629)
6. Our organization's Github is [here](https://github.com/litexlang/). The kernel is [here](https://github.com/litexlang/golitex).
7. [Hugging Face dataset](https://huggingface.co/litexlang).

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

_未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. It is so fortunate to receive tremendous help from friends and colleagues throughout this journey of designing, implementing, and growing Litex into a community. Without their support, Litex would not have had the chance to succeed.

I am deeply grateful to Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Siqi Guo, Haoyang Shi, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Lei Bai, Xiuyuan Lu, Yunwen Guo for their emotional support and insightful advice. I am certain this list of special thanks will only grow longer in the future.