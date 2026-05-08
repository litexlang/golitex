<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: A Fact-Oriented Formal Language for Everyone

*by Jiachen Shen and The Litex Team, version 0.9.73-beta*

[![Official Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Manual](https://img.shields.io/badge/Manual-teal)](https://litexlang.com/doc/Manual#manual-introduction)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![Zulip Community](https://img.shields.io/badge/Zulip%20Community-purple?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/litexlang/golitex)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)

**Beta notice:** Litex is still an experimental project for testing ideas about formalizing everyday mathematics. It is not ready for production or mission-critical proof work yet. **We hope more people will look at Litex, try it and discuss the mathematical philosophy behind it.**

</div>

## What is Litex?

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex is an open-source language for writing mathematical proofs as a flow of checkable facts. *It is a different philosophy for looking at mathematics as a growing body of checkable facts written in a computer-checkable form.*

The central idea is this: **users write facts; Litex grows a verified context**. A Litex file introduces mathematical objects, states facts about them, checks those facts, stores the successful ones, and uses them to justify later steps.

This is why Litex feels like a strict mathematical notebook. You write objects such as numbers, sets, and functions. You state facts such as `x = 2` or `x $in R`. Litex checks whether those facts follow from the current context, builtin mathematics, definitions, and previously verified facts. 

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

This small example shows the intended feel: Litex code states the desired facts directly, while the checker handles routine rewriting, arithmetic, and reuse of known facts.

## Why It Feels Simple

Litex is designed to feel simple because much of the routine mathematical structure lives in the checker instead of in user proof scripts.

1. **Facts are first-class proof steps.** A proof script mostly says mathematical facts in the order the reader should understand them.
2. **The context grows as the script runs.** Once a fact is verified, Litex stores it and may infer routine consequences for later use.
3. **Basic mathematics is built in.** Litex knows many small links between equality, order, membership, functions, sets, tuples, and arithmetic.
4. **Matching and substitution reduce naming.** Litex finds known facts and known `forall` facts by shape, then substitutes the matching objects.

For example, in Litex:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

The assumption `x = 2` becomes known inside the local proof context. Litex can find it by matching the goal, substitute `2` for `x`, and let builtin arithmetic close `x + 1 = 3`.

This is also why `forall` is central in Litex. A known `forall` theorem is like knowing infinitely many concrete facts at once: whenever the arguments match and the assumptions hold, Litex can substitute concrete objects and use the result.

When thinking in Litex, start with three blocks: **objects**, **facts**, and **statements**.

- **Objects** are the mathematical things being discussed, such as number `2`, real number set`R`,anonymous function `'R(z){z}`, list set `{1, 2, 3}`, or a function object `1 + 2`.
- **Facts** are claims about objects, such as `x = 2`, `x $in R`, `0 <= x`, `forall! x set => {x = x}`, `exist x R st {x ^ 2 = 4}`.
- **Statements** are actions in the proof script: define an object, introduce a fact, prove a fact, or store known information.

For a deeper explanation, read the [Manual](https://litexlang.com/doc/Manual#manual-introduction), especially the [Proof Process](https://litexlang.com/doc/Manual#proof-process).

## Proofs Explain Themselves

Litex does not only say whether a fact passed. Its output tells you how the fact was proved.

```litex
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
```

The output message is like this:

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

This output says that `$p(2)` was proved by reusing the known `forall` fact. Litex matched `x` with `2`, substituted it into `$p(x)`, and closed the goal. This makes the proof process learnable: you can see whether a fact closed by a builtin rule, a known fact, a known `forall`, or an inferred consequence.

## Start Here

1. [Official site](https://litexlang.com)
2. [Manual](https://litexlang.com/doc/Manual#manual-introduction)
3. [Tutorial](https://litexlang.com/doc/Tutorial/Introduction)
4. [Open Source Language Implementation](https://github.com/litexlang/golitex)
5. [Related Textbooks, Examples, Implementation Notes, and Experimental Materials](https://github.com/litexlang/golitex)
6. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
7. [Email](mailto:litexlang@outlook.com)

## Special Thanks

_未来没有计划，但一定更好。_

_- 樊振东在巴黎奥运会后接受采访时说_

<div align="center">
  <img src="https://publisher.litexlang.org/Little_Little_O.PNG" alt="The Litex Logo" width="200">
  <p><em>Litex Mascot: Little Little O, a curious baby bird full of wonder</em></p>
</div>

Hi, I’m Jiachen Shen, creator of Litex. I am deeply grateful to Wei Lin, Siqi Sun, Peng Sun, Zeyu Zheng, Siqi Guo, Chenxuan Huang, Yan Lu, Sheng Xu, Zhaoxuan Hong, Xiuyuan Lu, Yunwen Guo for their emotional support and insightful advice. I am certain this list of special thanks will only grow longer in the future.
