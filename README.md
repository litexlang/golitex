<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: From Formal Language to Verifiable Discovery in AI Era

## A Simple Formal Language Learnable in 2 Hours

**version v0.1.10-beta (not yet ready for production use)**  
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

[Congratulations! Litex achieves top 10 on Hacker News on 2025-09-27!!](https://news.ycombinator.com/item?id=45369629)

**Warning: Litex is still in beta. The syntax and semantics are subject to change. There might be some bugs and inconsistencies. You should not use Litex in any production environments yet.**

Litex([website](https://litexlang.com)) is a simple open-source formal language, learnable in 2 hours by anyone. It expresses mathematics in the form of code, ensuring that every step of the reasoning process is rigorously correct. The closeness of Litex to natural language, or more profoundly how people think, can be really helpful for AI and human alike in mathematical exploration and problem-solving. I hope you will forget that you are using a formal language to write mathematics using Litex!([Star the repo!](https://github.com/litexlang/golitex)). 

Euclid showed us over 2000 years ago how 5 axioms could derive such a wonderful geometric world. Simple starting points often lead us into infinitely complex worlds. The same is true for mathematics. The foundation of modern mathematics is naive set theory, which doesn't have many axioms, and we even encountered the concept of sets in middle school. But it is precisely these simple and understandable rules that form the foundation of all mathematics. Before we move on, think about how powerful the idea is: with just very few absolutely accurate inference rules, plus a few axioms, we can derive a rich and diverse mathematical world! That is what math is all about.

By implementing those simple axioms and deduction rules in a software like Litex, we can write math in the form of code. The learning curve of Litex will not be higher than learning LaTeX. Let's explore the fascinating math world with Litex! The times are calling us, we cannot afford to delay!

## Why Litex?

_Our intent was to create a pleasant computing environment (Unix) for ourselves and our hope was that others liked it._

_- Dennis Ritchie_

Making Litex intuitive to both humans and AI is Litex's core mission. We want people feel happy using Litex. Just like how Python lowers the barrier of programming by 10x compared with C/C++, Litex lowers the barrier of formal reasoning by 10x compared with previous formal languages like Lean. Here is an example:

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

While Lean 4 is a powerful and rigorous proof assistant ideal, it requires months of training and years of experience to master. Litex takes a different approach: prioritizing accessibility and ease of use, enabling even beginners to formalize naive tasks like multivariate equations in minutes.

Since each Litex sentence corresponds directly to an expression in everyday mathematical language, and since it is supported by set theory (ZFC) and basic logic (not, forall, exist, or), Litex does not sacrifice any rigor. So please do not think about Litex using the mindset of traditional formal languages. Instead, imagine yourself as a college student or even a high school student who has a basic understanding of set theory — regardless of whether you like Litex or are skeptical of it.

*In summary, Litex is a piece of software that imitates the way people think when they verify mathematics in everyday reasoning, using a small number of straightforward rules.* For example, if it sees “24 * 25 = 600,” it knows that a calculation needs to be performed. If it sees statements like “Every person will die” and “Socrates is a person,” it uses pattern matching and substitution: it substitutes Socrates into the statement “Every person will die” and checks whether Socrates satisfies the condition “is a person.” If so, it concludes that Socrates will also die. Along with other extremely common rules, Litex can verify complex mathematical statements with ease.

## Our Mission

_The value of an idea lies in the using of it._

_- Thomas Edison_

Physics boils down to a few fundamental laws, and chemistry to the logic behind the periodic table. Biology, too, is structured around core principles like evolution, heredity, and molecular mechanisms. Mathematics is no different — beneath all the complexity lie just a handful of basic rules of reasoning. Once you truly grasp those few principles, everything else follows naturally. The key is seeing the underlying structure, and then one insight unlocks many. Litex is such a language that helps you see the underlying structure of mathematics.

Our mission is to make Litex the most intuitive and simple formal language for coding reasoning. We aim to solve the most challenging problems faced by the AI community, i.e. the challenge of efficient, scalable, and reliable coding reasoning. Let's build the future together!

For mathematical research, a well-designed formal language can clarify the dependency structure among complex theorems and lay the foundation for large-scale collaborative “Big Mathematics.” For AI, such a formal language enables reasoning models to form a self-reinforcing cycle of automatic problem generation → automatic solving → automatic verification. Combined with the reinforcement-learning-based post-training approach demonstrated by DeepSeek-R1, this may lead to a breakthrough moment comparable to AlphaGo.

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

_Sometimes it is the very people who no one imagines anything of who do the things that no one can imagine._

_– Alan Turing_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. It is so fortunate to receive tremendous help from friends and colleagues throughout this journey of designing, implementing, and growing Litex into a community. Without their support, Litex would not have had the chance to succeed.

I am deeply grateful to Zhaoxuan Hong, Siqi Sun, Wei Lin, Peng Sun, Jie Fu, Zeyu Zheng, Huajian Xin, Zijie Qiu, Siqi Guo, Haoyang Shi, Chengyang Zhu, Chenxuan Huang, Yan Lu, Sheng Xu for their invaluable contributions. I am certain this list of special thanks will only grow longer in the future.