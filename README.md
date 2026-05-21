<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Formal Way to Write Math as It Looks

*by Jiachen Shen and The Litex Team, version 0.9.81-beta*

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

Litex is an open-source formal language for writing mathematical proofs that *look like ordinary mathematical writing*. Users write math almost exactly as they would in notes or textbooks; Litex checks them, stores verified results, and lets the proof grow from the context.

The central idea is: **users write facts; Litex grows a verified context**. Litex code introduces objects, states facts, checks them, stores successful ones, and reuses them later.

Litex is designed around ordinary mathematical writing: objects such as numbers, sets, and functions; facts such as `x = 2` or `x $in R`; and statements that grow a proof step by step. 

It emphasizes a set-theoretic surface, proof scripts as verifiable facts, a growing context, and proof output that explains why each fact was accepted.

Here is the intended feel:

<table style="border-collapse: collapse; width: 100%; table-layout: fixed; font-size: 12px">
  <tr>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 1px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4</code></pre>
    </td>
    <td style="border: 1px solid black; padding: 4px; vertical-align: top; overflow-wrap: anywhere; word-break: break-word">
<pre style="margin: 0; white-space: pre-wrap"><code>import Mathlib.Tactic
example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩</code></pre>
    </td>
  </tr>
</table>

This shows the intended feel: Litex states the desired facts directly, while the checker handles routine rewriting, arithmetic, and reuse of known facts. *Reading Litex code is a pleasant experience, because you can understand it without any prior study.*

## Why It Feels Simple

_To understand is to see connections._

_– Ludwig Wittgenstein_

_One must be able to say at all times instead of points, straight lines, and planes—tables, chairs, and beer mugs._

_– David Hilbert_

Litex feels simple because routine mathematical structure lives in the checker, not in user proof scripts.

1. **Facts are proof steps.** A script mostly states mathematical facts in reading order.
2. **The context grows.** Once verified, a fact is stored and can produce routine consequences.
3. **Basic mathematics is built in.** Litex knows small links between equality, order, membership, functions, sets, tuples, and arithmetic.
4. **Statement shapes guide matching.** Litex matches known facts and `forall` facts by shape, then substitutes the matching objects.

> As Hardy said, "A mathematician, like a painter or poet, is a maker of patterns.", Litex expects you to recognize familiar proof patterns (equality chains, membership, subsets, witnesses, contradiction, finite case splits). The checker matches those shapes to facts and routine consequences—more like following a textbook argument than memorizing tactic or library names for each line.

In this sense, Litex aims to be **the language where mathematics verifies itself**.

For example, a syllogism is ordinary mathematical information:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

Litex matches `$mortal(Socrates)` with the known `forall`, sees that `Socrates` belongs to `human`, and verifies the conclusion.

This is why `forall` is central: a known `forall` theorem acts like infinitely many concrete facts, ready to use when arguments and assumptions match.

The output looks like

```text
{
  "result": "success",
  "type": "AtomicFact",
  "line": 7,
  "stmt": "$mortal(Socrates)",
  "verified_by": {
    "type": "cite forall fact",
    "cite_source": {
      "line": 4,
      "source": "entry"
    },
    "cited_stmt": "forall x human:\n    $mortal(~1x)"
  },
  "infer_facts": [],
  "inside_results": []
}
```

The useful part is not only that the line succeeds. The output says
`$mortal(Socrates)` was proved by reusing the known `forall`: Litex matched
`x` with `Socrates`, checked the required membership fact, substituted into
`$mortal(x)`, and closed the goal. This is the explanatory surface Litex tries
to provide: you can see whether a fact closed by a builtin rule, a known fact,
a known `forall`, or an inferred consequence.

> Another special design of Litex is that much of its surface vocabulary is primitive. Forms such as `R`, `N`, `$in`, `fn`, `{}`, and finite sets are not first unfolded into user-visible foundations; their meaning comes from the web of builtin rules, known facts, and inference rules connected to them.

## AI Agents Can Work With Litex

_The only way to get artificial intelligence to work is to do the computation in a way similar to the human brain._

_– Jeff Hinton_

Litex is designed so that modern coding agents can formalize textbook-style mathematics by iterating against verifier feedback. An agent can sketch a proof in ordinary mathematical language, translate it into Litex step by step, run the checker, read why each fact failed or succeeded, and refine the argument until every step is local and concrete.

A concrete example is the final example in [Here](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Chapter_8_Functions), which proves that there is a bijection from `N^2` to `N` using Cauchy pairs. Codex formalized this example in Litex by reading the Manual and project documentation, running Litex, inspecting the verifier output, and iterating on the proof about three times. It does not rely on external mathematical facts, and was produced from Litex's own feedback loop rather than from hand-written hints about the proof.

This is the point Litex is trying to make especially strong: Litex gives agents a very direct debugging surface. The agent states the next mathematical fact, runs the checker, reads the local success or failure, and continues in the same language as the proof. Litex is still early, but this feedback loop suggests that filling in basic standard libraries and theorem collections may be fast: agents can add missing facts exactly where proofs ask for them.

## Starting Points

_Learn the rules like a pro, so you can break them like an artist._

_– Pablo Picasso_

Litex is aiming at a specific target: not making formal proof look clever, but making ordinary mathematical reasoning precise enough to check without changing its shape. Welcome to explore Litex by yourself.

Resources on the official website:

1. [Official site](https://litexlang.com)
2. [Manual](https://litexlang.com/doc/Manual)
3. [Setup: Download Litex](https://litexlang.com/doc/Setup)
4. [Textbook: The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof)

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

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Zeyu Zheng, Siqi Guo, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Xiuyuan Lu, and Yunwen Guo for their support and advice. I am sure this list will keep growing.
