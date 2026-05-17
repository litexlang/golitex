<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Formal Way to Write Math as It Looks

*by Jiachen Shen and The Litex Team, version 0.9.73-beta*

[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Manual](https://img.shields.io/badge/Manual-teal)](https://litexlang.com/doc/Manual#manual-introduction)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Setup](https://img.shields.io/badge/Setup-Download%20Locally-green)](https://litexlang.com/doc/Setup)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)

**Beta notice:** Litex is experimental and not ready for production or mission-critical proof work. **We welcome you to try it.**

</div>

## What is Litex?

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex is an open-source formal language for writing mathematical proofs that *look like ordinary mathematical writing*. Users write facts almost exactly as they would in notes or textbooks; Litex checks them, stores verified results, and lets the proof grow from the context.

The central idea is: **users write facts; Litex grows a verified context**. A file introduces objects, states facts, checks them, stores successful ones, and reuses them later.

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

This shows the intended feel: Litex states the desired facts directly, while the checker handles routine rewriting, arithmetic, and reuse of known facts.

## Why It Feels Simple

_A mathematician, like a painter or a poet, is a maker of patterns._

_– G. H. Hardy, *A Mathematician's Apology*_

Litex feels simple because routine mathematical structure lives in the checker, not in user proof scripts.

1. **Facts are proof steps.** A script mostly states mathematical facts in reading order.
2. **The context grows.** Once verified, a fact is stored and can produce routine consequences.
3. **Basic mathematics is built in.** Litex knows small links between equality, order, membership, functions, sets, tuples, and arithmetic.
4. **Statement shapes guide matching.** Litex matches known facts and `forall` facts by shape, then substitutes the matching objects.

> Litex expects you to recognize familiar proof patterns (equality chains, membership, subsets, witnesses, contradiction, finite case splits). The checker matches those shapes to facts and routine consequences—more like following a textbook argument than memorizing tactic or library names for each line.

In this sense, Litex aims to be **the language where mathematics verifies itself**.

For example, a syllogism is ordinary mathematical information:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

The user does not say "apply the theorem with `x = Socrates`." Litex matches `$mortal(Socrates)` with the known `forall`, sees that `Socrates` belongs to `human`, and verifies the conclusion.

This is why `forall` is central: a known `forall` theorem acts like infinitely many concrete facts, ready to use when arguments and assumptions match.

Think in three blocks: **objects**, **facts**, and **statements**.

- **Objects** are mathematical things: `2`, `R`, `'R(z){z}`, `{1, 2, 3}`, or `1 + 2`.
- **Facts** are claims about objects: `x = 2`, `x $in R`, `0 <= x`, `forall! x set => {x = x}`, or `exist x R st {x ^ 2 = 4}`.
- **Statements** are proof-script actions: define an object, introduce a fact, prove a fact, or store known information.

For more, read the [Manual](https://litexlang.com/doc/Manual#manual-introduction), especially [Proof Process](https://litexlang.com/doc/Manual#proof-process).

## Proofs Explain Themselves

_Make things as simple as possible, but no simpler._

_– Albert Einstein_

Not only does Litex aim to be **the language where mathematics verifies itself**, but it also tells you how it was proved.

```litex
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
```

The output looks like:

```json
{
  "result": "success",
  "type": "Fact",
  "line": 4,
  "stmt": "$p(2)",
  "verified_by":   {
    "type": "known_fact",
    "line": 2,
    "source": "entry",
    "cited_fact": "forall x R:\n    $p(x)"
  },
  "infer_facts": [],
  "inside_results": []
}
```

This says `$p(2)` was proved by reusing the known `forall`: Litex matched `x` with `2`, substituted into `$p(x)`, and closed the goal. You can see whether a fact closed by a builtin rule, a known fact, a known `forall`, or an inferred consequence.

## Start Here

1. [Official site](https://litexlang.com)
2. [Manual](https://litexlang.com/doc/Manual#manual-introduction)
3. [Tutorial](https://litexlang.com/doc/Tutorial/Introduction)
4. [Open Source Language Implementation](https://github.com/litexlang/golitex)
5. [Related Textbooks, Examples, Implementation Notes, and Experimental Materials](https://github.com/litexlang/golitex)
6. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
7. [Email](mailto:litexlang@outlook.com)
8. [Privacy Policy and Terms of Use](Privacy_Policy.md)

## Special Thanks

_未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Zeyu Zheng, Siqi Guo, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Xiuyuan Lu, and Yunwen Guo for their support and advice. I am sure this list will keep growing.
