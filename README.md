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

Litex is not trying to replace Lean, Coq, Rocq, Isabelle, or any mature proof
assistant. It tests a different hypothesis: that a smaller, readable,
fact-oriented formal language can make checked mathematics cheap enough for
students, domain scientists, and AI agents to produce useful formal data at
scale.

## Output Is a Proof Interface

Litex does not only answer "accepted" or "rejected". Output is one of the main
interfaces of the language. The source file is the proof as the user writes it;
the output is the proof as the checker reads it back.

This is a core design choice. In ordinary mathematical prose, a reader may see
a sentence and wonder: why is this true, which earlier facts does it use, and
what can I use it for later? Litex output is designed to answer those questions
line by line.

For each checked statement, the output tries to show three things:

1. **What the statement did.** It may introduce an object, assert a fact, open
   a local proof, split cases, or give a witness of an existential fact.
2. **How the fact was verified.** The route might be arithmetic, equality
   substitution, a known fact, a matching `forall`, a theorem call, or a
   builtin mathematical rule.
3. **How the environment changed.** Accepted facts, definitions, theorem
   interfaces, and inferred consequences become part of the context for later
   statements.

This makes the output more than a success message. It turns a proof script into
inspectable mathematical data:

- A dependency graph can point from each accepted line to the definitions,
  previous facts, theorem calls, builtin rules, and assumptions it used.
- An interactive textbook can let a reader click a sentence and ask "why is
  this true?" without relying only on informal prose.
- An AI repair loop can see whether a line failed because a domain condition,
  equality, membership fact, or lemma is missing.
- A proof audit can expose which steps were checked, which came from imports,
  and which were accepted as explicit `proof_debt`.

Natural language explanations are useful, but they do not usually carry
machine-checkable provenance. Traditional theorem-prover interfaces often
center on proof states, tactics, elaboration messages, or kernel terms. Litex
puts statement-by-statement proof reading into the main user experience: an
ordinary-looking mathematical line can be printed back with its verification
route and its effect on the growing context.

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

The JSON shape is intentional: it is structured enough for dependency tables,
flow charts, knowledge graphs, interactive textbooks, and AI tools, while still
being readable as an explanation of what happened in the proof.

*Litex output also supports multiple languages, including English, Chinese,
Japanese, Korean, Spanish, French, German, Portuguese, Russian, Arabic, Hindi,
Vietnamese, and Indonesian. The source code stays the same; the explanation can
be localized.*

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

### Domain Conditions Stay Near the Function

```litex
have fn g(x R: x > 0) R = x + 1

g(1) = 2
```

The call `g(1)` is meaningful because Litex can check the domain condition
`1 > 0`.

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
prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

have fn square(x R) R = x^2
forall x R:
    square(x) = x^2

by contra not $surjective_fn(R, R, square):
    have by exist x R st {-1 = square(x)}: x
    0 <= x^2
    square(x) = x^2
    -1 = square(x) = x^2
    0 <= -1
    impossible 0 <= -1
```

These examples are small on purpose. They show the surface rule: write the next
mathematical fact, and let the checker explain whether the current context
justifies it.

## Litex vs Lean: Same Idea, Different Interface

Lean is a mature theorem prover with a powerful dependent type theory, Mathlib,
expert tooling, and a large community. Litex is a younger research system with
a larger trusted mathematical background and a narrower interface goal.

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
[Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean).

## A Larger Mathematical Surface

Litex can define reusable mathematical vocabulary. For example, a group
interface can keep the carrier set, operation, inverse, identity, and axioms in
one visible place:

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
```

Litex is also being pressure-tested on real mathematical translation work:
textbook chapters, MATH-style problems, high-school mathematics, miniF2F-style
items, and Tao Analysis material. The goal is not only to collect successful
proofs. Failed translations are useful too, because they expose concrete gaps
in syntax, standard-library interfaces, verifier rules, diagnostics, or proof
automation.

## Trust Boundary

Litex is beta software. A Litex result should be read relative to the trusted
background used in that run:

- builtin objects and builtin mathematical facts;
- builtin verification and inference rules;
- imported standard-library facts;
- explicit `know`, `let`, `axiom`, or `proof_debt` assumptions;
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

Litex is not a shortcut around mathematics. It is an experiment in making the
proof trail readable enough that more people and AI systems can participate in
formal checking without losing sight of the argument.

## Starting Points

1. [Setup: Download Litex](https://litexlang.com/doc/Setup): install Litex and
   run files from the command line.
2. [Manual](https://litexlang.com/doc/Manual): syntax, proof flow, builtin
   verification rules, inference, and trust boundaries.
3. [Litex Output Is Your Friend](https://litexlang.com/doc/Tutorial/Litex_Output_Is_Your_Friend):
   how to read verifier output as a proof trace.
4. [Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean): a dedicated
   comparison of proof interface and ecosystem tradeoffs.
5. [The Mechanics of Litex Proof](https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction):
   a textbook-style introduction to Litex proof writing.
6. [Hugging Face: Litex examples and datasets](https://huggingface.co/litexlang)

Contact:

1. [Email](mailto:litexlang@outlook.com)
2. [Zulip community](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

## Special Thanks

Litex is built by Jiachen Shen and the Litex team, with support and advice from
many friends and collaborators. Thanks especially to Wei Lin, Siqi Sun, Peng
Sun, Chenxuan Huang, Yan Lu, Sheng Xu, and Zhaoxuan Hong. This list will keep
growing.
