<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**Release v0.1.1-beta (not yet ready for production use)**  
*May 2025*  
*Created by Jiachen Shen*

</div>

## About Litex

_Simplicity is the ultimate sophistication._

_-- Leonardo da Vinci_

Litex is a simple yet powerful formal language for mathematical reasoning. A formal language is a language that allows you to express your reasoning in structured way so that a computer can verify them. Unlike traditionally over-complicated formal languages, Litex is intuitive and accessible to everyone. Learn more in [tutorial](./doc/tutorial/tutorial.md).

Litex aims to scale reasoning in three ways:

**Engineering:** Like software engineering, Litex turns individual math work into **mathematical engineering** through clear abstraction and composition. Writing math in Litex can be as simple as writing code in Python.

**Accessibility:** Being much simpler than other formal languages, Litex enables **more people** to participate in formal reasoning, from children to experts.

**AI Integration:** Litex provides the perfect **infrastructure for AI** to learn and perform formal reasoning at scale.

World-class researchers including Terrence Tao, Yoshua Bengio, and AI companies including DeepMind and DeepSeek, are showing great interest how formal languages can be used to scale reasoning AI, ensure AI safety, and many more tasks. Litex is the perfect tool to their challenge. Litex has already gained attention from leading institutions worldwide, including **CMU, Mila, Tsinghua, PKU, OpenMMLab, SJTU, Fudan**.  

## Learn Basics of Litex in One Minute

_Keep it simple, stupid._

_-- The Unix Philosophy_

There are two things in math: objects and factual statements. Objects are the things that we are talking about, and factual statements are the statements about objects. Sets, functions, numbers, etc. are all objects. And factual statements are statements like "Jordan is intelligent", "1 < 2", "x = 1", etc. In Litex, a factual statement has four potential outcomes: true, false, unknown(not enough information to determine the truth value), or error(the statement is not well-formed). A fact is a statement that is true.

Math is built on top of a small sets of reasoning rules and axioms. There are basically two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

Amazingly, with these two ways of deriving a new fact, and with a set of carefully chosen axioms, we can (nearly) build the entire world of mathematics. And you have ALREADY learned the basic mechanism of Litex in just one minute: **match and substitute**. Pretty simple, right?

All daily math is built around first-order-logic, naive set theory, natural numbers related axioms (mathematical induction, Peano axioms, extension to rational numbers and real numbers), and all of these are implemented in Litex. So it does not matter whether you are formalizing algebra or geometry or any other math, as long as you are clear about concepts and axioms of the math you are formalizing, you can use Litex to formalize it.

A major special case of match and substitute is about rational numbers, like 1, 3.5 or 4.123456789. These objects are different from user-defined objects because their literal representation directly encodes information. Rational numbers and their basic operations like addition, multiplication, inequalities are builtin in Litex, and Litex handles all the verification rules for them automatically.

## A Simple Example

_If you define the problem correctly, you almost have the solution._

_-- Steve Jobs_

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle, which formalizes deductive reasoning as follows:

<table style="border-collapse: collapse; width: 100%;">
  <tr>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 3px solid black; padding: 8px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 3px solid black; padding: 8px;">
      <code>set Human</code> <br><br>
      <code>prop self_aware(x Human)</code> <br><br>      <code>know forall x Human:</code> <br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$self_aware(x)</code> <br> <br>
      <code>obj Bob Human</code> <br> <br>
      <code>$self_aware(Bob)</code>
    </td>
    <td style="border: 3px solid black; padding: 8px;">
      <code>def Human := Type</code> <br><br>
      <code>def self_aware (x : Human) : Prop := true</code> <br><br>
      <code>axiom self_aware_all :</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;∀ (x : Human), self_aware x</code> <br><br>
      <code>def Bob : Human := Human</code> <br><br>
      <code>example : self_aware Bob := self_aware_all Bob</code>
    </td>
  </tr>
</table>

Consider `Human` as the set of all humans. Using `know`, we establish a simple fact: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is true. This simple example shows how Litex builds math from basic pieces, like building blocks. By `match and substitute`, Litex verifies the correctness of the reasoning just like how you verify the correctness of your daily reasoning. Each statement in Litex has four potential outcomes: true, false, unknown, or error.

Notice how Litex is much simpler than Lean4. Instead of writing complex axioms with special names, you just use familiar words like `know` and `forall`. Litex automatically finds the facts it needs, just like searching in a database. Moreover, there are less unfamiliar keywords, less twisted syntax in Litex. People can understand Litex at first glance and say "oh, I already get this." instead of trying to figure out what this keyword or that syntax means. Users can focus more on math itself instead of the formal language they use. Litex's syntax is similar to Python and Go, so if you've done any programming, you'll feel right at home. See more in [comparison with Lean](./doc/comparison_with_lean/comparison_with_lean.md), [tutorial](./doc/tutorial/tutorial.md).

## Unique Idea of Litex

_Common sense is not so common._

_-- Voltaire_

Everyone knows how to reason, including 5-year-old. We reason thousands of time every day without even noticing it. Yet, traditional formal languages, like Lean4, Coq, and Isebelle are so complex that even the smartest mathematicians find it hard to use. Why is that?

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system. These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. 

If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

On the other hand, Litex is a formal language that operates as a Read-Only Turing Machine. By deliberately sacrificing Turing completeness, Litex focuses solely on mathematical verification. Unlike programming languages, Litex eliminates variables, control flow, and execution semantics - concepts that are foreign to pure mathematics. 

This design choice, similar to how SQL specializes in database operations, allows Litex to specialize in everyday math as much as possible. The language adopts Python-like syntax for accessibility.

Another important design choice is that the user does not need to give names to facts, because Litex can automatically find the matched facts it needs. It saves a lot of time and effort for the user. Read [tutorial](./doc/tutorial/tutorial.md) for more details.

Throughout the years, natural languages are [considerably more expressive than their formal mathematical counterparts](https://terrytao.wordpress.com/advice-on-writing-papers/take-advantage-of-the-english-language/). With Litex, we can finally make the best of both worlds.

In a nutshell, Litex is for EVERYONE, from children to experts, to learn and use formal language at AI age. It scales up reasoning by making the process of writing formal reasoning as intuitive as writing in natural language.

## Resources

_If I have seen further, it is by standing on the shoulders of giants._

_-- Isaac Newton_

[Applications of Formal Reasoning in AI and Many Other Fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md)

[Tutorial](./doc/tutorial/tutorial.md)

[Formalization of Hilbert Geometry Axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix)

[Compare Litex with Lean](./doc/comparison_with_lean/comparison_with_lean.md)

[Website](https://litexlang.org)

[Github](https://github.com/litexlang/golitex)


## Answers to Common Questions

1. Why is Litex poised for success now?

Litex represents an intellectual breakthrough in formal language design. The rapidly expanding AI industry presents the perfect opportunity, as it needs tools for ensuring AI safety, enhancing reasoning, and accelerating scientific discovery.

2. What makes Litex different from other formal languages?

Litex's greatest strength is its remarkable simplicity. While other formal languages require years of expertise to master, Litex is intuitive enough for children to learn, striking the perfect balance between power and accessibility.

3. How do I formalize concepts like uniform distribution over (0,1) or anything like that?

Think of formalization like reading a book - you need to understand the previous pages before the last one. Similarly, formalizing advanced concepts requires building up from fundamentals. For example, formalizing uniform distribution over (0,1) requires many prerequisites. The good news is that translating mathematical concepts to Litex is straightforward once you have the prerequisites in place.

## Contribute to Litex

_The best way to predict the future is to invent it._

_-- Alan Kay_

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics and programming language enthusiast (a programming language geek, if you are one too, you are welcome to contact me). In 2023, I shockingly found that math is somehow equivalent to programming, after reading Professor Terence Tao's [blog](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/). This is the most amazing idea that I have ever seen in my life. In 2024, after thinking about it for a year, I started to implement Litex. After more than 2500 git commits, what it means to be a "formal language that is intuitive and as aligned with daily math expression as possible" is finally to make sense to me and my kernel sort of works now (in a very clumsy way, I am sorry I am too single-handed to do this big project all by myself). Litex is evolving from implementation to community-driven development. The interpreter is 90% complete and covers most daily math.

You can contribute by:
1. Contributing to the interpreter or standard library
2. Creating datasets for AI training
3. Improving documentation
4. Exploring Litex's mathematical capabilities
5. Spreading the word about Litex
6. Building standard library of Litex
7. Creating the LitexDojo, similar to how LeanDojo is for Lean.

See more in [contribute to Litex](./doc/contribute_to_Litex/contribute_to_Litex.md).

Since 90% of the functionality delivered now is better than 100% of it delivered never[^1], the inventor of Litex put it open-source to welcome everyone, including you, to learn, try, use, and contribute to Litex, even though Litex is not fully ready. Feel free to contact us and join this exciting journey!

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
- **Discord:** [discord](https://discord.gg/uvrHM7eS)

[^1]: Kernighan & Plauger, The Elements of Programming Style, 1978.