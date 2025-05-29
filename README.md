<div align="center">
<img src="assets/logo.png" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: Scale Formal Reasoning in AI Age

**Release v0.1.1-beta**  
*May 2025*  
*Created by Jiachen Shen*

</div>

Litex is a simple yet powerful formal language (proof assistant) for mathematical reasoning. It uses `match and substitute` to automatically verify the correctness of your reasoning, making it perfect for validating mathematical proofs. Unlike complex formal languages that require years of training, Litex is designed to be intuitive - even a 5-year-old can understand its basic concepts. Our mission is to make formal reasoning accessible to everyone. Tutorial is [here](./doc/tutorial/tutorial.md).

Litex aims to scale reasoning in three ways:

**Engineering:** Like software engineering, Litex turns individual math work into mathematical engineering through clear abstraction and composition.

**Accessibility:** Being much simpler than other formal languages, Litex enables more people to participate in formal reasoning, from children to experts.

**AI Integration:** Litex provides the perfect foundation for AI to learn and perform formal reasoning at scale.

World-class researchers including Terrence Tao, Yoshua Bengio, and AI companies including DeepMind and DeepSeek, are showing great interest in the combination of formal languages and AI. Litex is my answer to this challenge. Litex has already garnered attention from leading institutions worldwide, including **CMU, Tsinghua, Peking University, Pujiang Lab, Shanghai Jiao Tong University, Fudan University**.  

## Learn Basics of Litex in One Minute

Math is built on top of a small sets of reasoning rules and axioms. There are basicly two types of deriving a new fact from existing facts:

1. derive from a specific fact: e.g. If I know x = 1, then x = 1
2. derive from a general fact: e.g. If I know forall human, he is intelligent, and Jordan is a human, then Jordan is intelligent. Litex calls this way of deriving a new fact "match and substitute", because it is like matching a pattern and substituting the pattern with a specific value.

Amazingly, with these two ways of deriving a new fact, and with a set of carefully chosen axioms, we can (nearly) build the entire world of mathematics. And you have ALREADY learned the basic mechanism of Litex in just one minute: match and substitute. Pretty simple, right?

A major special case of match and substitute is about real numbers, like 1, 3.5 or 4.123456789. These objects are different from user-defined objects in two key ways:

1. Their literal representation directly encodes their value - for example, "3.5" immediately tells us this is three and a half
2. They are built-in primitive types that cannot be declared by users - you can't create new real numbers, only use the ones that exist

Litex handles all the verification rules for real numbers automatically. This means you can use familiar properties of real numbers (like addition, multiplication, inequalities) without having to prove them yourself.

## A Simple Example

Mathematics is the art of deriving new facts from established ones. To illustrate, consider a classical syllogism proposed by Aristotle in his Prior Analytics, which formalizes deductive reasoning as follows:

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

Consider `Human` as the set of all humans. Using `know`, we establish a simple fact: all humans are self-aware. Since Bob is in the set of `Human`, "Bob is self-aware" is true.

Notice how Litex is much simpler than Lean4. Instead of writing complex axioms with special names, you just use familiar words like `know` and `forall`. Litex automatically finds the facts it needs, just like searching in a database. Moreover, there are less unfamiliar keywords, less twisted syntax in Litex.

This simple example shows how Litex builds math from basic pieces, like building blocks. By `match and substitute`, Litex verfies the correctness of the reasoning just like how you verify the correctness of your daily reasoning.

Litex's syntax is similar to Python and Go, so if you've done any programming, you'll feel right at home. See more in [comparison with Lean](./doc/comparison_with_lean/comparison_with_lean.md).

## Idea Behind Litex: Why Is Litex Unique?

Everyone knows how to reason, including 5-year-old. We reason thousands of time every day without even noticing it. Yet, traditional formal languages, like Lean4, Coq, and Isebelle are so complex that even the smartest mathematicians find it hard to use. Why is that?

It turns out that these languages attempt to serve two distinct purposes simultaneously: they want to be both programming languages and reasoning verifiers. This dual nature makes it technically challenging to create a simple and intuitive system.

These languages heavily rely on type theory and functional programming concepts, which even mathematics PhD students need years to master. If Newton had to learn those theories before inventing calculus, he would never succeed, because those theories would be invented 3 centuries later.

Technically, Litex is a Read-Only Turing Machine, instead of a Turing Machine. Litex sacrifices Turing completeness to focus exclusively on mathematical verification, adopting a Python-like syntax for ease of use and LaTeX-like elegance for mathematical expression (similar to how SQL sacrifices completeness to specialize in database logic). That is why Litex is so simple and intuitive.

With a small set of reasoning rules and axioms, we human beings are able to build the entire world of mathematics and apply them in everyday life. That is why in Litex, there are not that many keywords and language rules. Keeping Litex small and intuitive helps it keep  aligned with how reasoning actually works. The more you understand how Litex relates to your daily reasoning, the better you'll learn it.

More importantly, Litex's clean syntax and structured representation make it an ideal training dataset for AI reasoning, helping AI models develop more reliable mathematical reasoning capabilities.

For those who are curious about whether Litex can truly express all logic in math, the answer is: Yes, almost. All daily math is built around first-order-logic, naive set theory, and mathematical induction, and all of these are already implemented in Litex. And Litex will implement higher-order-logic in the future.

In a nutshell, Litex is for EVERYONE, from children to experts, to learn and use formal language at AI age. It scales up reasoning by making the process of writing formal reasoning as intuitive as writing in natural language.

## Resources

[Applications of Formal Reasoning in AI and Many Other Fields](./doc/applications_of_formal_reasoning/applications_of_formal_reasoning.md)

[Tutorial](./doc/tutorial/tutorial.md)

[Formalization of Hilbert Geometry Axioms](./examples/comprehensive_examples/Hilbert_geometry_axioms_formalization.lix)

[Compare Litex with Lean](./doc/comparison_with_lean/comparison_with_lean.md)

[Website](https://litexlang.org)

[Github](https://github.com/litexlang/golitex)


## Contribute to Litex

Hi, I am Jiachen Shen, the creator of Litex. I am a PhD student in mathematics, and I am also a programming language geek. I have been working on Litex since 2024 and received many valuable feedbacks from Litex enthusiasts. I hope you enjoy using Litex, too. 

For the time being (2025-05), Litex is evovling from the stage of figuring out and implementing the idea of a simple formal language, to the stage of community-driven development and user-adoption. It will be long and interesting journey, feel free to contact us.

For the time being, the Litex interpreter itself is 90% complete. Most daily usage is covered. You can contribute to Litex by:

1. Contributing to the Litex interpreter.
2. Contributing by telling your friends about Litex.
3. Contributing to standard library of Litex, which covers daily math.
4. Contributing writing dataset of Litex for AI to learn. Just 1000 pairs of natural language and Litex code is also helpful.
5. Contributing to the LitexDojo, similar to how LeanDojo is for Lean.
6. Contributing to the Litex README, tutorial, reference, and other documentation. If you are confused about something, please let me know.

Litex is still under active development. Contribution and early adoption is welcome!

---  
**Contact:**  
- **Website:** [litexlang.org](https://litexlang.org)  
- **GitHub:** [github.com/litexlang/golitex](https://github.com/litexlang/golitex)
- **Project Email:** litexlang@outlook.com
- **Litex Creator:** Jiachen Shen
- **Litex Creator's Email:** malloc_realloc_free@outlook.com
