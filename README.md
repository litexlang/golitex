<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Language Where Mathematics Verifies Itself

*by Jiachen Shen and The Litex Team, version 0.9.103-beta*

[![Website](https://img.shields.io/badge/Official%20Website-blue?logo=website)](https://litexlang.com)
[![Github](https://img.shields.io/badge/Github-grey?logo=github)](https://github.com/litexlang/golitex)
[![litexpy](https://img.shields.io/badge/Litexpy-green?logo=python)](https://github.com/litexlang/litexpy)
[![Email](https://img.shields.io/badge/Email-red?logo=email)](mailto:litexlang@outlook.com)
[![Zulip](https://img.shields.io/badge/Zulip-blue?logo=zulip)](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)
[![Hugging Face](https://img.shields.io/badge/Hugging%20Face-black?logo=huggingface)](https://huggingface.co/litexlang)
[![Manual](https://img.shields.io/badge/Manual-orange?logo=book)](https://litexlang.com/doc/Manual)

**Beta notice:** Litex is experimental and not ready for mission-critical work.

</div>

## What is Litex?

Litex is a readable, fact-oriented formal language for checked mathematics.

The basic loop is small:

1. Write the next mathematical fact.
2. Litex checks whether it follows from the current context.
3. If it succeeds, the fact enters the context and can be reused later.
4. The output explains what was checked, how it was verified, and what changed.

A first Litex file can be this small:

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

The first line introduces a real number `x` and stores the fact `x = 2`.
The next two lines are not tactic commands. They are mathematical facts. Litex
checks them using the stored value of `x`, equality substitution, and arithmetic.

That is the central interface: **users write facts; Litex grows a verified
context**.

## A Small Mathematical Workflow

Litex is a bet on compressing the writing of mathematical reasoning without
making its verification opaque. A C compiler lets a programmer describe
structured operations instead of manually managing assembly instructions.
Litex lets a mathematical writer state objects, facts, and small derivations
instead of repeatedly exposing every formal encoding, proof goal, and tactic
step.

The details are not discarded: Litex checks each statement against the current
context, records the facts it accepted, and explains the rule or earlier fact
that justified the result.

Litex is also developing a Litex-to-Lean compiler (not yet released). For the supported verified
subset, it translates this fact-oriented surface into Lean declarations that
Lean's kernel can check, with Mathlib as the formal library. The bridge makes
the compression inspectable: readers can see how a concise Litex fact expands
into lower-level formal mathematics. The compiler is ongoing work and does not
yet cover every Litex feature. See
[Litex and Lean](https://litexlang.com/doc/Litex_and_Lean) for the current
mapping and limits.

Litex tries to reduce formal verification to a small mathematical state:

| Idea | Meaning | Litex shape |
| --- | --- | --- |
| **object** | a thing being discussed: a number, set, function, or expression | `have x R = 2` |
| **prop** | a predicate or relation | `prop positive(x R): x > 0` |
| **statement** | a fact asserted about objects | `x + 1 = 3` |
| **fact** | an accepted statement that later lines can reuse | after `x = 2` is accepted, later lines may use `x = 2` |

The proof side is meant to be just as small:

| Proof route | Meaning | Litex shape |
| --- | --- | --- |
| builtin reasoning | close routine arithmetic, equality, order, membership, set, or function facts | `2 + 3 = 5` |
| known fact matching | reuse a fact already in the context | write the target fact again |
| known `forall` matching | instantiate a universal fact whose premises match the context | `forall x R: ...` then write its conclusion |
| definition unfolding | use the meaning of a `prop` or definition | `$positive(1)` from `prop positive(x R): x > 0` |
| theorem call | cite a named theorem explicitly | `by thm self_eq(1)` |
| local claim | prove an intermediate fact and store it | `claim: ...` |
| witness | prove an existential or nonempty fact by giving objects | `witness exist x R st {x = 1} from 1` |
| contradiction | assume the opposite and derive an impossible fact | `by contra: ...` |
| cases | split into exhaustive cases | `by cases: ...` |
| induction | prove a base case and an induction step | `by induc n from 0: ...` |

*For ordinary fact-oriented proof work, that is it!* The rest of the language
mostly names, packages, imports, or structures these same moves. The user's
attention stays on ordinary mathematical objects and facts, and the verifier
explains which small proof route accepted each step.

Litex is not trying to replace Lean, Coq, Rocq, Isabelle, or any mature proof
assistant. It tests a different hypothesis: that a smaller, readable,
fact-oriented formal language can make checked mathematics cheap enough for
students, domain scientists, and AI agents to produce useful formal data at
scale.

The same fact-and-rule workflow also points to an AI-facing use case:
lightweight **proof-carrying policy**. Instead of hard-coding a fixed list of
`if`/`else` rules, a system can write policies as facts, definitions, and
`forall` rules; as new context enters, Litex can derive checked consequences
such as whether an agent action is allowed, forbidden, or needs human review,
and the output can expose the proof trace behind that decision.

## Output Explains Every Line

Litex does not only say whether a proof passed. It can print what every line
did, why it was accepted, and what later lines can reuse.

In ordinary mathematical prose, a reader may see a sentence and wonder: why is
this true, which earlier facts does it use, and what can I use it for later?
Litex output is designed to answer those questions line by line.

For each checked statement, the output tries to show three things:

1. **What the statement did.** It may introduce an object, assert a fact, open
   a local proof, split cases, or give a witness of an existential fact.
2. **How the fact was verified.** The route might be arithmetic, equality
   substitution, a known fact, a matching `forall`, a theorem call, or a
   builtin mathematical rule.
3. **What later lines can reuse.** Accepted facts, definitions, theorem names,
   and inferred consequences become part of the context for later statements.

For the tiny file above, the human reading is:

```text
Line 1 succeeded: introduced x as a real number and stored x = 2.
Line 3 succeeded: verified x + 1 = 3 from x = 2 and arithmetic.
Line 4 succeeded: verified x^2 = 4 from x = 2 and arithmetic.
```

Litex executes once and then projects the same trace into three views:

- `-compact` prints only `result`, `type`, `line`, and `statement`.
- Ordinary output is the default reading view. It keeps `inside_results`,
  assumptions, conclusions, and direct `why_verified` reasons, without audit
  duplication.
- `-detail` adds full recursive verification data, execution phases, effects,
  and raw source paths for auditing.

In `-detail` mode, the important execution phases have this shape:

```json
{
  "result": "success",
  "statement": "x + 1 = 3",
  "verification": {
    "type": "builtin verification",
    "rule": "known value substitution and arithmetic"
  },
  "phases": {
    "affect_environment": {
      "status": "success",
      "effects": [
        {
          "kind": "store_fact",
          "fact": "x + 1 = 3",
          "reason": "proved statement"
        }
      ]
    }
  }
}
```

*Litex output also supports multiple languages, including English, 中文,
日本語, 한국어, Español, Français, Deutsch, Português, Русский, العربية,
हिन्दी, Tiếng Việt, and Bahasa Indonesia. The source code stays the same; the
explanation can be localized.*

<sub>
This structured output can support dependency graphs, flow charts, knowledge
graphs, interactive textbooks, AI proof-repair loops, and proof audits. Each
accepted line can point to the definitions, previous facts, theorem calls,
builtin rules, imports, or assumptions it used. Natural-language explanations
are useful, but they do not normally preserve this kind of structured,
checkable proof trail.
</sub>

## A Few Litex Examples

### Facts Grow the Context

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

### The Same Context in Lean

<table>
  <tr>
    <th>Litex</th>
    <th>Lean</th>
  </tr>
  <tr>
    <td valign="top">
<pre><code>forall x R:
    x = 2
    =&gt;:
        x + 1 = 3
        x^2 = 4</code></pre>
    </td>
    <td valign="top">
<pre><code>import Mathlib

example (x : ℝ) (h : x = 2) :
    x + 1 = 3 ∧ x ^ 2 = 4 := by
  constructor
  · rw [h]
    norm_num
  · rw [h]
    norm_num</code></pre>
    </td>
  </tr>
</table>

Both snippets express the same arithmetic. Litex presents each consequence as
the next fact in a context; Lean makes the theorem boundary and proof
construction explicit.

### Finite Sets Look Like Finite Sets

```litex
1 $in {1, 2, 3}

forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

### A Universal Fact Can Be Proved from Witnesses

```litex
prop can_be_divided_by_8(x Z):
    exist d Z st {x = 8 * d}

prop can_be_divided_by_2(x Z):
    exist d Z st {x = 2 * d}

claim:
    ? forall x Z:
        $can_be_divided_by_8(x)
        =>:
            $can_be_divided_by_2(x)
    obtain d from exist d Z st {x = 8 * d}
    witness exist e Z st {x = 2 * e} from 4 * d:
        x = 8 * d
        8 * d = 2 * (4 * d)

witness exist d Z st {8 = 1 * d} from 8
$can_be_divided_by_8(8)
$can_be_divided_by_2(8)
```

The claim unfolds both divisibility predicates. From a witness `d` with
`x = 8 * d`, it constructs the new witness `4 * d` with `x = 2 * (4 * d)`.
The final three lines give the concrete witness for `8` and check that instance.

### Functions Look Like Functions

```litex
have fn f(x R) R = x^2 + 1

f(3) = 10
```

For numeric formulas and update rules with a direct programming-language shape,
Litex also has a narrow `litex -python` path: checked `have fn as algo`
definitions can be emitted as ordinary Python for scientific-computing-style
kernels. See [Litex To Python](https://litexlang.com/doc/Litex_To_Python) for
the current supported subset.

### Existential Witnesses Are Direct

```litex
witness exist x R st {x^2 = 4} from 2
```

### Users Can Define Vocabulary

```litex
prop is_one(x R):
    x = 1

$is_one(1)
```

### Proof by Contradiction Reads Like Proof by Contradiction

```litex
by contra not 2 < 1:
    2 < 1
    impossible 2 < 1
```

These examples are small on purpose. They show the surface rule: write the next
mathematical fact, and let the checker explain whether the current context
justifies it.


### Abstract Mathematical Concepts

Litex is not limited to small arithmetic examples. It can also express abstract
mathematical concepts directly. For example, a group can be described by a
carrier set, an inverse operation, a binary operation, an identity element, and
the usual axioms. After defining that abstract interface, Litex can check that
the integers with negation, addition, and `0` form a group:

```litex
prop GroupProperty(s nonempty_set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
    forall x s:
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s nonempty_set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $GroupProperty(s, inv, op, e)

$GroupProperty(Z, fn(x Z) Z {-x}, fn(x, y Z) Z {x + y}, 0)

(fn(x Z) Z {-x}, fn(x, y Z) Z {x + y}, 0) $in &Group<Z>
```

The last line says that `(Z, x -> -x, (x, y) -> x + y, 0)` is an instance of
the `Group` structure. Litex verifies it by checking the tuple fields have the
right types and that the displayed group axioms hold for integer addition.


## Trust Boundary

Litex is beta software. A Litex result should be read relative to the trusted
background used in that run:

- builtin objects and builtin mathematical facts;
- builtin verification and inference rules;
- facts imported from declared project modules or source-local cite packages;
- explicit `axiom`, or `trust` assumptions;
- the current implementation of the parser, runtime, and verifier.

`trust` is assumption injection. It is useful for marking unfinished
background work, but it is not a proof. When auditing a Litex file, inspect the
remaining `trust` facts before treating the development as complete.

This trust boundary is part of the project design. Litex deliberately places
many routine mathematical relationships into the checker so ordinary proofs can
be written as readable fact sequences. That makes the interface lightweight,
but it also means the trusted background is larger than a minimal proof kernel.

Litex does not ship or auto-load a mathematical `std`; supporting facts belong
first in source-local cite packages. The promotion rule for any future reusable
package is recorded in [Reusable Mathematics Policy](docs/Reusable_Mathematics_Policy.md).

## Goals

Litex is aiming at three practical goals:

1. **Readable formalization.** Make formal mathematical code close enough to
   ordinary mathematical writing that students, scientists, and curious readers
   can follow the proof.
2. **AI repair loops.** Give AI-generated mathematical reasoning a strict,
   inspectable feedback loop: accepted facts, unknown facts, errors, and
   explicit proof debt.
3. **Translation as pressure test.** Use real mathematical sources to discover
   language, library, verifier, and diagnostic gaps.

By the end of 2026, our goal is to make textbook-first formalization the main
benchmark for Litex: a public, auditable body of undergraduate mathematics
translations across calculus, linear algebra, geometry, probability, analysis,
algebra, and number theory. We think this is more meaningful than simply
accumulating many isolated definitions, theorem names, or lines of formal code,
because a textbook translation tests whether the language can preserve the
actual mathematical development: definitions in order, local lemmas,
intermediate facts, proof routes, verifier output, and explicit blockers when
the current system falls short.

Litex is not a shortcut around mathematics. It is an experiment in making the
proof trail readable enough that more people and AI systems can participate in
formal checking without losing sight of the argument.

## Starting Points

1. [Setup: Download Litex](https://litexlang.com/doc/Setup): install Litex and
   run files from the command line.
2. [Examples learning path](docs/Examples.md): the first place to look after
   setup, from tiny checked facts to small mathematical worlds.
3. [Manual](https://litexlang.com/doc/Manual): syntax, proof flow, builtin
   verification rules, inference, and trust boundaries.
4. [Litex Output Is Your Friend](https://litexlang.com/doc/Tutorial/Litex_Output_Is_Your_Friend):
   how to read verifier output as a proof trace.
5. [Litex and Lean](https://litexlang.com/doc/Litex_and_Lean): how the two
   interfaces can work together, including the ongoing compilation bridge.
6. [The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction):
   a textbook-style introduction to Litex proof writing.
7. [Hugging Face: Litex examples and datasets](https://huggingface.co/litexlang)

Contact:

1. [Email](mailto:litexlang@outlook.com)
2. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

## Special Thanks

Litex is built by Jiachen Shen and the Litex team, with support and advice from
many friends and collaborators. Thanks especially to Wei Lin, Siqi Sun, Peng
Sun, Chenxuan Huang, Yan Lu, Sheng Xu, and Zhaoxuan Hong. This list will keep
growing.
