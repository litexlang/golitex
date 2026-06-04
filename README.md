<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: A Fact-Oriented Language for Checked Mathematics

*by Jiachen Shen and The Litex Team, version 0.9.96-beta*

[![Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![litexpy](https://img.shields.io/badge/Litexpy-green?logo=python)](https://github.com/litexlang/litexpy)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Zulip](https://img.shields.io/badge/Zulip-blue?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)
[![Manual](https://img.shields.io/badge/Manual-orange?logo=book)](https://litexlang.com/doc/Manual)

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

Litex is not intended to replace any other proof assistant. It explores a
different path in formal mathematics: whether a readable, fact-oriented
interface can make it easier for AI systems and humans to translate
natural-language problems and textbook theorems into checkable formal proof
attempts. The goal is to make ordinary mathematical reasoning precise enough
for machine feedback while preserving the structure and appearance of
mathematical reasoning itself.

## The First Mental Model

Think of a Litex file as a small mathematical world that grows one checked fact
at a time. You introduce the objects in the world, give yourself vocabulary,
store general rules, and then ask Litex whether a new fact follows.

A classical syllogism shows the shape:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

This says: Socrates is human; every human is mortal; therefore Socrates is
mortal.

The four moves are the basic Litex loop:

1. `have human nonempty_set, Socrates human` builds a tiny world.
2. `abstract_prop mortal(x)` adds a new word that can be used in facts.
3. `know forall x human: ...` stores the general rule.
4. `$mortal(Socrates)` asks Litex to verify the particular conclusion.

The example is intentionally small, but it uses two assumption-facing tools:
`abstract_prop` declares the vocabulary word `mortal`, and `know` assumes the
general rule. Litex checks that the conclusion follows from that context; it
does not prove the assumed rule from nothing.

When Litex accepts that final line, the verifier output can explain the route
it found. The exact JSON may include line numbers and more trace fields, but
the important shape is:

```text
{
  "result": "success",
  "type": "AtomicFact",
  "stmt": "$mortal(Socrates)",
  "verified_by": {
    "type": "cite forall fact",
    "cited_stmt": "forall x human: $mortal(x)"
  }
}
```

The useful part is not only that a line succeeds. The output tells you whether
the route was arithmetic, a known fact, a matching `forall`, or an inferred
consequence. That makes Litex a feedback loop: write the next fact, run the
checker, read what happened, and add the next piece of context.

Every factual statement has exactly one of three outcomes: **true**,
**unknown**, or **error**. `true` means Litex found a proof path, such as a
builtin rule, a known fact, or a known `forall` fact. `unknown` means the
statement is meaningful, but Litex did not find enough verified information to
prove it. `error` means the line cannot be checked as a valid fact, often
because the syntax is wrong or some object is not well-defined, such as an
undeclared name, a function argument outside its domain, or `1 / 0`.

## How is Litex Different

Litex supports two complementary ways to verify a fact.

The explicit route is `by thm`: give a theorem a name, remember that name, and
cite it with the required arguments. This is closer to the named-theorem style
used by Lean and other formal proof systems.

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

thm all_humans_are_mortal:
    prove:
        forall x human:
            $mortal(x)
    know $mortal(x)

by thm all_humans_are_mortal(Socrates)
$mortal(Socrates)
```

The Lean shape is similar: keep the universal fact under a name, then apply
that name to the object you need.

```lean
variable (Human : Type)
variable (Socrates : Human)
variable (mortal : Human -> Prop)
variable (all_humans_are_mortal : forall x : Human, mortal x)

example : mortal Socrates := by
  exact all_humans_are_mortal Socrates
```

The Litex-native route is pattern matching against the verified context. Instead
of naming and citing the theorem, you can leave the universal fact in context
and write the conclusion directly:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

Here Litex matches `$mortal(Socrates)` against the known `forall`, checks that
`Socrates human` is already in context, substitutes `x` with `Socrates`, and
verifies the conclusion. This is the core difference in proof style: Litex can
use named theorem calls when names make the proof clearer, but it also lets
ordinary factual lines drive verification by their mathematical shape.

>  This example uses two assumption-facing tools. `abstract_prop` declares an uninterpreted predicate name, and `know` assumes a fact about it, similar in role to Lean's `by sorry`. They are useful for axioms and proof skeletons, but final artifacts should replace, justify, or explicitly record them as proof debt.

## Goals of Litex

Litex is experimental, but it is aiming at three simple things:

1. **Audit AI-generated mathematical derivations.** As generation gets cheaper,
checking assumptions, malformed facts, missing steps, and remaining proof debt
becomes the bottleneck.
2. **Support scientific discovery.** Turn verification into a fast loop of
trying ideas, repairing arguments, and reusing patterns.
3. **A formal mathematical language that inspires everyone.** Formal math should
be a usable, readable medium for learning, communication, and research, close
enough to everyday math that students, mathematicians, AI agents, and curious
readers can benefit from rigor without losing sight of the ideas.

This route comes with a clear audit obligation. A Litex result should be read
relative to its trusted background: builtin rules, inference rules,
standard-library facts, and any explicit `know` assumptions. The project goal
is not to hide that boundary; it is to make the boundary visible while keeping
the user-facing proof script close to ordinary mathematical writing.

Here is the whole landscape of Litex kernel:

<div align="center">
  <img src="assets/verifier_flow.png" alt="Litex kernel" width="1000">
  <p><em>Litex kernel: the core components and their relationships.</em></p>
</div>

## Starting Points

Litex keeps the public documentation small:

1. [Setup: Download Litex](https://litexlang.com/doc/Setup): install Litex,
   run files, and understand CLI output.
2. [Manual](https://litexlang.com/doc/Manual): the source of truth for syntax,
   statements, proof flow, builtin rules, and inference.
3. [FAQ](https://litexlang.com/doc/FAQ): design rationale, trust boundaries,
   comparison notes, and old overview material in condensed form.
4. [Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean): dedicated
   comparison with Lean's interface and ecosystem.
5. [Litex 中文介绍](https://litexlang.com/doc/%E4%B8%AD%E6%96%87%E7%AE%80%E8%A6%81%E4%BB%8B%E7%BB%8D): Chinese introduction and project framing.

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

The path of Litex is a deliberate trade-off. Litex accepts a larger trusted
implementation than small-kernel systems in order to make the proof surface
lighter. The system tries to do more routine checking in the verifier so users
can spend more of their attention on the mathematical sequence of facts. This uniqueness is the core value of Litex as a proof assistant, but it also makes contribution to Litex more difficult and demanding. We welcome young talents to try Litex and contribute to it.

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Siqi Guo, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Xiuyuan Lu, and Yunwen Guo for their support and advice. I am sure this list will keep growing.
