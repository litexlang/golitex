<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### Write mathematics. See why it holds.

Created and maintained by Jiachen Shen.

_“Language is an instrument of human reason, and not merely a medium for the expression of thought.”_

_— George Boole, The Laws of Thought (1854), Chapter II (excerpt)_

[Official Website (官网)](https://litexlang.com) ·
[Read the Blueprint](docs/Litex_Blueprint.md) ·
[阅读中文蓝图](docs/Litex中文蓝图.md)
</div>

## Write a fact and see what it leaves behind

Litex is designed as an everyday formal language for everyone who wants to
write and understand checkable mathematics.

**Research and release boundary.** Litex is currently an evolving
formal-language research project and experimental system. It cannot replace
natural language in carrying all of mathematics' intuition, motivation, and
explanation, nor does it have the mature trusted foundation, domain coverage,
or ecosystem scale that Lean and Mathlib have accumulated. Litex investigates
a different, narrower, and independent question: can a language design
organized around facts, statement-by-statement checking, and retained
knowledge records lower the cost for people and AI to construct, understand,
review, repair, and reuse checkable knowledge?

This project is released in its current state. Public source code, examples,
and experimental results do not guarantee completeness, fitness for any
particular purpose, or superiority to other systems. Judge its capabilities by
dated verification results, trust boundaries, known limitations, and concrete
use cases; do not extrapolate results within an experimental scope into
untested guarantees.

Write the next mathematical fact directly; Litex checks it and shows the
grounds it found or where checking stopped.

```litex
1 + 1 = 2
have a R = 2
a + 1 = 3
```

The first line is checked by calculation. The second introduces `a` as a real
number: Litex records `a $in R` and `a = 2`. It then checks `a + 1 = 3` using
the available facts and stores that equality for later steps. The author
chooses what to establish; Litex searches for supported local grounds and
reports the method it found.

Definitions join the same flow:

```litex
prop is_odd(x Z):
    x % 2 = 1

$is_odd(3)
```

Litex checks the concrete claim through the definition and keeps
`$is_odd(3)` in the current context. These are small examples of the
fact-oriented interface, not a claim that the verifier can invent an entire
proof from its final statement.

**How Litex works.** See the [Litex Verification Pipeline](https://litexlang.com/assets/diagrams/litex-verification-pipeline-v1.png)
for a visual overview of checking a fact, finding local grounds, and making
accepted knowledge available to later steps.

**Multilingual feedback.** The CLI can present JSON verification feedback in
several languages. The same source can be checked with `-lang zh` for Chinese
explanations or `-lang fr` for French ones. Thanks in part to AI-assisted
translation, this multilingual explanatory copy became feasible; the language
setting changes the feedback, not the mathematical statement being checked.
See the [CLI language options](docs/cli.md#basic-shape).

**Mathematical content for your tools.** `litex -lang en -f example.lit`
emits JSON with statement text, stored facts, inferred facts and proof summaries.
Use it to build your own indexes or visualizations. Normal JSON summarizes
verification and does not expose every dependency; see the
[JSON output contract](docs/cli.md#json-output-contract).

**LaTeX export (preview).** `litex -latex -document -lang zh -f example.lit`
compiles parsed source into mathematical LaTeX with prose in any of the ten
CLI languages. It preserves definitions and explicit proof steps without
executing or verifying them. See the [LaTeX compiler guide](src/compile_to_latex/README.md).

## Start from familiar mathematical objects

Litex aims for a Python-like entry into formal mathematics, where more people
can learn to build checkable knowledge.

Litex takes set theory (ZFC) as its mathematical foundation and presents sets,
elements, functions, and relations as the working vocabulary. In
`have a R = 2`, membership and equality are facts the language can use again;
the author does not first choose an abstract carrier type for `a`. Function
domains, set membership, and other well-definedness conditions still have to
be checked before a statement is accepted.

```litex
have S set = {x R: x > 0}
have fn square(x R) R = x^2
square(2) = 4

prop is_less(x, y R):
    x < y

$is_less(2, 4)
```

**Symbolic input.** Litex also accepts familiar mathematical symbols as input:
`s ∩ u ⊆ t ∩ u` is the symbolic spelling of
`intersect(s, u) $subset intersect(t, u)`.
Most examples use the letter-based spelling because it is easier to type on
an ordinary keyboard. See the [supported Unicode aliases](docs/Manual.md#unicode-mathematical-input-aliases-preview).

Lean elaborates proofs into a core dependent type theory; its compiler IR for
executable programs is a separate path. Litex makes set membership and facts
the default authoring layer. Lean can express set theory too; this compares
their default interfaces, not their current coverage.

The concision of Litex source comes from the coordination among objects,
facts, statements, and verification procedures developed through sustained
iteration. It makes the mechanical work connecting common proof steps part of
the language's default checking, letting authors state mathematical steps
directly and build on existing knowledge. The Blueprint's
[systems engineering perspective](docs/Litex_Blueprint.md#systems-engineering)
follows a small reciprocal function through this design.

## Let checked knowledge grow

_“If I have seen further it is by standing on the shoulders of Giants.”_

_— Isaac Newton, letter to Robert Hooke (1676)_

Every accepted statement extends the mathematical context for the statements
that follow.

```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

The [checked Cantor example](docs/Litex_Blueprint.md#overview-spine) in the
Blueprint goes further: it defines a diagonal subset, proves a general theorem
without `trust`, then applies it to a `singleton` function to obtain
`missing != singleton(0)`.

## Work with people and AI through feedback

A person chooses the question, constructions, and mathematical meaning. AI can
propose or revise a small source fragment. Litex checks that fragment and
returns structured grounds or a stopping point; accepted steps become the
background for the next attempt. Failed statements do not enter the accepted
context. An external writing tool can save attempts and feedback for later
review—the language does not automatically archive the full collaboration.

[![Litex Agent Pipeline: AI proposes Litex steps, the verifier returns JSON feedback, and accepted facts accumulate into checked source.](assets/litex-agent-pipeline.png)](assets/litex-agent-pipeline.png)

*AI proposes, Litex checks, and accepted knowledge accumulates. The output
previews illustrate possible uses of the checked source.*

First attempt (rejected):

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(0) = 0
```

Revised attempt (accepted):

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

## Independent Lean rechecking is a goal

Litex checks supported source with its own verifier. The preview
`litex -lean -f <standalone-file>` replays supported typed results into Lean
source. [`lean/Litex.lean`](lean/Litex.lean) owns the semantic interface and
[`lean/examples/`](lean/examples/) contains problem-specific source/generated
pairs. Generation and Lean kernel checking are separate gates; this numeric
slice does not cover the complete Litex system. Development material and the
earlier compiler are local-only under ignored `scripts/`. See the
[Blueprint's Lean section](docs/Litex_Blueprint.md#compatibility).

<table>
<thead><tr><th>Litex</th><th>Lean (handwritten)</th></tr></thead>
<tbody>
<tr>
<td valign="top"><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td valign="top"><pre><code>import Mathlib
example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩</code></pre></td>
</tr>
</tbody>
</table>

Litex is an experimental beta project. Its builtin and inference rules, and
any user-written `trust` or `axiom`, are part of the present trust boundary. A successful
Litex check should be read with that scope in mind; the
[Manual's trust and strict-mode section](docs/Manual.md#trust-and-strict-mode)
explains how assumptions are handled. `-strict` rejects executed user `trust`,
`trust have`, and `axiom`, including imported dependencies; abstract predicate
signatures and named foundation releases remain allowed.

## Try Litex

Run it in the [online playground](https://litexlang.com), or install it on
macOS or Linux with Homebrew:

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
litex -lang zh -e '1 + 1 = 2'
litex -e '∅ ∩ ℕ ⊆ ℕ'
```

For other platforms and checkout builds, use the [setup guide](docs/setup.md).
The [CLI reference](docs/cli.md) explains commands and verification output;
the [Manual](docs/Manual.md) and [examples](examples/README.md) are starting
points for writing more Litex. [Analysis with Litex](showcases/analysis_notes/README.md) introduces limits and
infinite sums through a short mathematical lecture, citing the longer
[Tao Analysis chapter development](showcases/analysis/README.md). The latter
contains selected Chapters 1–8, with retained axioms and omitted branches
stated explicitly.
[Mathematics in Litex](showcases/Mathematics-in-Litex/README.md) adapts selected
material from *Mathematics in Lean*, following witnesses, sets and functions
through recursive constructions and algebraic structures. The full argument and further
source examples
are in the [Blueprint](docs/Litex_Blueprint.md) and
[中文蓝图](docs/Litex中文蓝图.md).

To understand the implementation, follow the [source reading guide](src/README.md):
start with the central data structures, then trace the component algorithms
that check statements and grow the mathematical context.

## About

_“The best way to predict the future is to invent it.”_

_— Alan Kay, “The Early History of Smalltalk” (1993)_

Jiachen Shen (沈嘉辰), creator of Litex, is a mathematics PhD student at Fudan University. Lean
showed him that mathematics and programming can meet in a real language;
Litex explores whether formal source can follow more closely the way people
construct mathematical arguments.

The Blueprint describes Litex's [mathematical values](docs/Litex_Blueprint.md#mathematical-values) ([中文](docs/Litex中文蓝图.md#mathematical-values)).

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu,
Sheng Xu, Keyao Zhu, and Zhaoxuan Hong for their support and advice.

Litex is released under the [Apache License 2.0](LICENSE).
