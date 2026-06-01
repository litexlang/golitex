<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Formal Language Where Code Verifies Itself

*by Jiachen Shen and The Litex Team, version 0.9.88-beta*

[![Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![litexpy](https://img.shields.io/badge/Litexpy-green?logo=python)](https://github.com/litexlang/litexpy)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Zulip](https://img.shields.io/badge/Zulip-blue?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)
[![Textbook](https://img.shields.io/badge/Textbook-orange?logo=book)](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof)

**Beta notice:** Litex is experimental and not ready for production or mission-critical proof work. **We welcome you to try it.**

</div>

## What is Litex?

_Truth is ever to be found in simplicity, and not in the multiplicity and confusion of things._

_– Isaac Newton_

Litex is an open-source language for writing checked mathematical proof code.
The basic loop is small:

1. Write the next mathematical fact.
2. Let Litex check it against the facts already in context.
3. Reuse the verified fact on later lines.

Here is a first proof:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

Read it as ordinary mathematics: for every real number `x`, if `x = 2`, then
`x + 1 = 3` and `x^2 = 4`. Litex checks the two conclusions by using the
assumption `x = 2`, routine rewriting, and arithmetic.

This is the central idea of Litex: **users write facts; Litex grows a verified
context**. A Litex file introduces objects, states facts about them, checks
which facts follow, stores the accepted ones, and makes them available to the
lines that come after.

The goal is not to make proof scripts look clever. The goal is to make ordinary
mathematical reasoning precise enough that it can be checked while still
looking like mathematical reasoning.

## The First Mental Model

Think of a Litex proof as checked mathematical notes.

```litex
forall a, b Q:
    a - b = 4
    a * b = 1
    =>:
        (a + b)^2 = (a - b)^2 + 4 * (a * b) = 4^2 + 4 * 1 = 20
```

The last line is a calculation chain. Litex checks each link:

1. the algebraic identity,
2. the substitutions from `a - b = 4` and `a * b = 1`,
3. the final arithmetic.

You do not have to name a special command for each small move. The line exposes
the mathematical shape, and the checker tries to justify that shape from the
current context.

As proofs grow, the same loop continues:

```litex
forall r, s R:
    r + 2 * s = -1
    s = 3
    =>:
        r = (r + 2 * s) - 2 * s = -7
```

The assumptions create a small mathematical world. Inside that world, the final
fact becomes checkable.

## What You Can Create

Litex is designed to help you build mathematical worlds one verified fact at a
time.

1. Start with calculations over numbers.
2. Reuse facts you proved earlier.
3. Define your own mathematical vocabulary.
4. Prove properties of functions, sets, relations, and finite structures.
5. Use the verifier output to see why a line succeeded or where more context is
   needed.

The online textbook, [The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof),
is the best starting point. It begins with calculation and gradually moves to
structured proofs, logic, induction, functions, sets, relations, and
cardinality.

## What the Checker Reports

When Litex accepts a factual line, it can also report why. For example, a line
may be accepted because it follows from arithmetic, from a previously verified
fact, or from a matching universal fact.

A simplified output record names the accepted statement and the kind of reason
Litex found. The exact JSON may include line numbers and more detailed trace
fields, but the important shape is:

```text
{
  "result": "success",
  "type": "AtomicFact",
  "stmt": "x + 1 = 3",
  "verified_by": {
    "type": "known equality and arithmetic"
  }
}
```

The useful part is not only that a line succeeds. The output explains the proof
route Litex found: a builtin rule, a known fact, a matching `forall`, or an
inferred consequence. That makes Litex useful as a feedback loop: write the
next fact, run the checker, read what happened, and add the next piece of
context.

Every factual statement has exactly one of three outcomes: **true**,
**unknown**, or **error**. `true` means Litex found a proof path, such as a
builtin rule, a known fact, or a known `forall` fact. `unknown` means the
statement is meaningful, but Litex did not find enough verified information to
prove it. `error` means the line cannot be checked as a valid fact, often
because the syntax is wrong or some object is not well-defined, such as an
undeclared name, a function argument outside its domain, or `1 / 0`.

## How Litex Is Different

Litex is not trying to be a faster Lean. Lean is a powerful formal mathematics
ecosystem with a broad library and mature tooling. Litex explores a different
interface: for textbook-style mathematics and AI repair loops, the user writes
a sequence of checkable facts, and the checker uses context plus builtin
relationships to keep the feedback loop short.

The important difference is the default task. Instead of asking the user to
construct proof terms through a general proof-programming environment, Litex
asks whether the next mathematical fact follows from the current verified
context. *In one local run, more than 240 runnable examples from The Mechanics
of Litex Proof checked in about 13 seconds.*

A tiny example makes the interface difference concrete. In Litex, the user
writes the facts they want checked:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

One Lean proof of the same elementary facts names the hypothesis, proves the
two conclusions, and then packages them together:

```lean
import Mathlib.Tactic

example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩
```

The point is not that Lean cannot prove this. It can, and Lean's proof engine
is much more general. The point is where the default attention goes: Lean asks
the user to work through a proof language, while Litex lets the user put the
mathematical facts on the surface and asks the checker to justify them from
context.

For readers who want the detailed comparison with Lean-style proof writing, see
[Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean) and
[Research Positioning](https://litexlang.com/doc/Research_Positioning).

## Goals of Litex

Litex is experimental, but it is aiming at three simple things:

1. **Verify AI-generated mathematics.** As generation gets cheaper, checking becomes the bottleneck.
2. **Support scientific discovery.** Turn verification into a fast loop of trying ideas, repairing arguments, and reusing patterns.
3. **A formal mathematical language that inspires everyone.** Formal math should not only be backend code for proof-assistant experts; it should also become a medium for ordinary mathematical learning, communication, and research. To make that possible, the language has to be usable, understandable, and close to everyday mathematical expression, so mathematicians, students, AI agents, and curious readers can benefit from formal rigor while still seeing ideas in a form that can inspire their own work.

## Starting Points

If this is your first formal proof language, start with the textbook path:

1. [The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof):
   learn the proof style gradually, beginning with calculations.
2. [Setup: Download Litex](https://litexlang.com/doc/Setup): run snippets
   locally.
3. [Manual](https://litexlang.com/doc/Manual): look up syntax once you have
   written a few examples.

A useful first ten minutes is to run the first Chapter 1 calculation, change
one assumption, and see which later fact becomes `unknown`. Then add the missing
intermediate line. That is the Litex learning loop in miniature: create a small
world, state the next fact, and let the checker show what is still missing.

For different readers:

1. [Benchmarks and Case Studies](https://litexlang.com/doc/Benchmarks_and_Case_Studies): for reproducible examples and evaluation.
2. [AI for Science](https://litexlang.com/doc/AI_for_Science): for local verification of scientific and applied mathematical derivations.
3. [Hilbert Axioms of Euclidean Geometry](https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry): for a complete abstract-mathematics example.
4. [Soundness and Limitations](https://litexlang.com/doc/Soundness_and_Limitations): for readers who care about the trusted base, explicit assumptions, builtin rules, and current limitations.
5. [Research Positioning](https://litexlang.com/doc/Research_Positioning): for proof assistant researchers and formal mathematics readers.
6. [Litex 中文战略一页纸](https://litexlang.com/doc/Strategic_One_Page_CN): for Chinese strategic and project discussions.
7. [Outreach Guide](https://litexlang.com/doc/Outreach_Guide): for contributors writing emails, posts, and audience-specific pitches.

Resources on the official website:

1. [Official site](https://litexlang.com)
2. [Textbook: The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof)
3. [Setup: Download Litex](https://litexlang.com/doc/Setup)
4. [Manual](https://litexlang.com/doc/Manual)

Resources:

1. [Litex Kernel and Documents](https://github.com/litexlang/golitex)
2. [litexpy: Use Litex in Python](https://github.com/litexlang/litexpy)
3. [litex-lang on crates.io: Use Litex in Rust](https://crates.io/crates/litex-lang)
4. [Hugging Face: Litex code examples and datasets](https://huggingface.co/litexlang)

Contact us:

1. [Email](mailto:litexlang@outlook.com)
2. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

## Special Thanks

_未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Siqi Guo, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Xiuyuan Lu, and Yunwen Guo for their support and advice. I am sure this list will keep growing.
