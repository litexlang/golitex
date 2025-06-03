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

**Engineering:** Like software engineering, Litex turns individual math work into **mathematical engineering** through clear abstraction and composition.

**Accessibility:** Being much simpler than other formal languages, Litex enables **more people** to participate in formal reasoning, from children to experts.

**AI Integration:** Litex provides the perfect **infrastructure for AI** to learn and perform formal reasoning at scale.

World-class researchers including Terrence Tao, Yoshua Bengio, and AI companies including DeepMind and DeepSeek, are showing great interest how formal languages can be used to scale reasoning AI, ensure AI safety, and many more tasks. Litex is the perfect tool to their challenge. Litex has already gained attention from leading institutions worldwide, including **CMU, Mila, Tsinghua, PKU, OpenMMLab, SJTU, Fudan**.  

## Learn Basics of Litex in One Minute

_Keep it simple, stupid._

_-- The Unix Philosophy_

Math is built on top of a small sets of reasoning rules and axioms. There are basically two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

Amazingly, with these two ways of deriving a new fact, and with a set of carefully chosen axioms, we can (nearly) build the entire world of mathematics. And you have ALREADY learned the basic mechanism of Litex in just one minute: **match and substitute**. Pretty simple, right?

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

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

Technically, Litex is a declarative formal language that operates as a Read-Only Turing Machine. By deliberately sacrificing Turing completeness, Litex focuses solely on mathematical verification. This design choice, similar to how SQL specializes in database operations, allows Litex to specialize in everyday math as much as possible. The language combines Python-like syntax for accessibility with LaTeX-like mathematical notation for precision. Unlike programming languages, Litex eliminates variables, control flow, and execution semantics - concepts that are foreign to pure mathematics. 

Another important design choice is that the user does not need to give names to facts, because Litex can automatically find the matched facts it needs. Read [tutorial](./doc/tutorial/tutorial.md) for more details.

All daily math is built around first-order-logic, naive set theory, natural numbers related axioms (mathematical induction, Peano axioms, extension to rational numbers and real numbers), and all of these are implemented in Litex. So it does not matter whether you are formalizing algebra or geometry or any other math, as long as you are clear about concepts and axioms of the math you are formalizing, you can use Litex to formalize it.

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

1. Why now could Litex be a big hit?

Litex itself is a piece of art intellectually. However, it must target the right group of users so that it can be a big hit in real world. The ever-growing AI industry now is the right group of users, for safety, for better reasoning, for scientific discovery.

2. Why Litex?

Litex is a simple language, really really simple. Even a child can learn it with ease. It is just the right tool tailored for formalizing math compared with other formal languages which takes an expert an enormous amount of time to learn.


## Contribute to Litex

_The best way to predict the future is to invent it._

_-- Alan Kay_

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics and programming language enthusiast. Litex is evolving from implementation to community-driven development. The interpreter is 90% complete and covers most daily math.

You can contribute by:
1. Contributing to the interpreter or standard library
2. Creating datasets for AI training
3. Improving documentation
4. Exploring Litex's mathematical capabilities
5. Spreading the word about Litex
6. Building standard library of Litex
7. Creating the LitexDojo, similar to how LeanDojo is for Lean.

90% of the functionality delivered now is better than 100% of it delivered never. That is why despite Litex is not fully ready, I put it open-source to welcome everyone, including you, to learn, try, use, and contribute to Litex. Feel free to contact us and join this exciting journey!

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
