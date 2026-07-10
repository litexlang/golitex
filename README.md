<div align="center">
<img src="https://publisher.litexlang.org/logo.PNG" alt="The Litex Logo" width="300">
</div>

<div align="center">

# Litex: The Language Where Mathematics Verifies Itself

*by Jiachen Shen and The Litex Team, version 0.9.100-beta*

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

Litex is a bet on compression: not compressing mathematics into opaque
automation, but compressing the user-facing verification workflow into a few
inspectable mathematical moves.

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

The JSON output contains more structure, but the important fields have this
shape:

```json
{
  "result": "success",
  "statement": "x + 1 = 3",
  "verification": {
    "type": "builtin verification",
    "rule": "known value substitution and arithmetic"
  },
  "store_facts": [
    {
      "fact": "x + 1 = 3",
      "reason": "proved statement"
    }
  ]
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

### Finite Sets Look Like Finite Sets

```litex
1 $in {1, 2, 3}

forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3
```

### A Universal Fact Can Be Used by Shape

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

forall:
    forall x human:
        $mortal(x)
    =>:
        $mortal(Socrates)
```

The conclusion `$mortal(Socrates)` is checked by matching it against the local
`forall x human: $mortal(x)` and the known fact `Socrates human`.

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


## Litex & Lean: Shared Aim, Different First Principles

Lean is a mature theorem prover with a powerful dependent type theory, Mathlib,
expert tooling, and a large community. Litex is a younger research system with
a larger trusted mathematical background and a narrower interface goal. Litex and Lean share the broad aim of making mathematics machine-checkable.

We are also developing a partial Litex-to-Lean compiler. The longer-term
experiment is not to make Litex a Lean-based language, but to let it serve as a
fact-oriented, set-theory-based, intuitive, and simple-to-write interface for
Lean. Litex remains an independent formal language, designed around a
set-theoretic mathematical surface and explicit fact growth. Lean is not its
foundation; it is an important backend: Litex can compile verified
developments into independently checkable Lean code and reuse the Mathlib
ecosystem. This is ongoing work; see
[Litex and Lean](https://litexlang.com/doc/Litex_and_Lean).

The point of the comparison below is not that Lean cannot prove these examples.
Lean proves them easily. The point is that the default user interface is
different.

### Context Reuse

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

Litex writes the desired facts directly. Lean exposes a theorem goal and asks
the user to construct a proof, here by rewriting with `h` and running
arithmetic simplification.

### Finite Set Membership

<table>
  <tr>
    <th>Litex</th>
    <th>Lean</th>
  </tr>
  <tr>
    <td valign="top">
<pre><code>forall a {1, 2, 3}:
    a = 1 or a = 2 or a = 3</code></pre>
    </td>
    <td valign="top">
<pre><code>import Mathlib

example (a : ℕ)
    (ha : a ∈ ({1, 2, 3} : Finset ℕ)) :
    a = 1 ∨ a = 2 ∨ a = 3 := by
  simpa using ha</code></pre>
    </td>
  </tr>
</table>

Litex treats membership in a displayed finite set as an ordinary mathematical
fact. Lean can express the same fact precisely, but the user chooses a concrete
encoding such as `Finset ℕ` and uses library simplification.

### Domain-Constrained Functions

<table>
  <tr>
    <th>Litex</th>
    <th>Lean</th>
  </tr>
  <tr>
    <td valign="top">
<pre><code>have fn g(x R: x &gt; 0) R = x + 1

g(1) = 2</code></pre>
    </td>
    <td valign="top">
<pre><code>import Mathlib

def g (x : {x : ℝ // x &gt; 0}) : ℝ :=
  x.val + 1

example : g ⟨1, by norm_num⟩ = 2 := by
  norm_num [g]</code></pre>
    </td>
  </tr>
</table>

Lean is more general and more mature. Litex chooses a surface closer to the
way the same domain restriction often appears in ordinary mathematical writing.

For a much longer and more careful comparison, see
[Litex and Lean](https://litexlang.com/doc/Litex_and_Lean).

## Trust Boundary

Litex is beta software. A Litex result should be read relative to the trusted
background used in that run:

- builtin objects and builtin mathematical facts;
- builtin verification and inference rules;
- imported standard-library facts;
- explicit `axiom`, or `proof_debt` assumptions;
- the current implementation of the parser, runtime, and verifier.

`proof_debt` is assumption injection. It is useful for marking unfinished
background work, but it is not a proof. When auditing a Litex file, inspect the
remaining `proof_debt` facts before treating the development as complete.

This trust boundary is part of the project design. Litex deliberately places
many routine mathematical relationships into the checker so ordinary proofs can
be written as readable fact sequences. That makes the interface lightweight,
but it also means the trusted background is larger than a minimal proof kernel.

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
