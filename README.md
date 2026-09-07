<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### Write math as it is. See why it holds.

Created and maintained by Jiachen Shen.


**Litex is a small, readable, fact-oriented formal language for turning**
**mathematical reasoning into checkable, traceable data; it also keeps the**
**runtime process readable, traceable, and repairable, so humans, AI, and Litex**
**can work in the same loop.**

It is a set-theoretic, fact-oriented formal language that builds proof flows
from the bottom up. It puts humans, AI, and the verifier in the same loop:
humans provide mathematical intent, AI proposes or repairs the next fact, and
Litex checks it and returns either its supporting evidence or the point where
verification stops. Through this cycle, checkable mathematical knowledge
accumulates. In principle, any Litex code can be compiled to Lean and connected
to the Lean/Mathlib ecosystem. 

> **Litex is an experimental hobby project in beta; expect rough edges.**

This README is a five-minute introduction. For the complete design argument,
detailed comparisons, examples, and trust boundaries, read the
[Litex Blueprint](docs/Litex_Blueprint.md)
([中文蓝图](docs/Litex中文蓝图.md)).
</div>

## Beyond the Search for One Best Language

The question is not only which formal language is the most powerful, mature, or
widely adopted. We should also ask what other forms of mathematical thought
could become possible if the interface were different. As AI produces more
mathematical reasoning, solving more problems, producing shorter proofs, and
increasing benchmark scores are useful goals—but they are not the whole
purpose of mathematics. Different formal paths can preserve the attention
needed for deep understanding and discovery.

Litex begins from this possibility. It treats formalization as a way of
shaping mathematical attention, not only as a way of satisfying a kernel. Its
fact-oriented and bottom-up design is an invitation to explore another relation
between human intuition, machine verification, and mathematical knowledge.

Litex may not become the only path, and it does not need to. Its contribution
may be to show that formal mathematics has more than one possible future. A
second rigorous route can make different structures visible, support new ideas,
and give different readers a way into the same mathematics. Read the
[Litex Blueprint](docs/Litex_Blueprint.md) for the fuller argument.

Litex's longer-term vision is that its implementation may grow large while its
core execution model remains easy to understand. It can externalize the
dependencies readers silently track in mathematics as Checkable Knowledge
Records for interactive textbooks.

<!-- README spine: plural formalization paths → write one fact → accepted facts become context → build a mathematical language with Group → readable execution and Checkable Knowledge Records → human–AI verification loop → formal language → AI for Math → toward safe and efficient reasoning → ToLean and Lean rechecking → ecosystem fit and boundaries → action -->

<!--
Litex positioning layers:
- Scientific object: how checkable knowledge is represented and constructed step by step.
- Scientific hypothesis: whether fact-oriented representation and transactional interaction form a useful formal-language design paradigm.
- Result variables: how that paradigm changes the cost of constructing, understanding, reviewing, repairing, and reusing checked knowledge.
- Potential impact: broader participation in verification and, over time, safer and more efficient AI reasoning.
The first three are the scientific core. The fourth is a possible downstream impact, not a result already established.
-->

## Start with the mathematics

Litex begins from the next mathematical fact you want to establish:

```litex
1 + 1 = 2
```

This is a complete statement, not a proof hole. Litex checks that the
expression is well-defined, establishes the equality through a calculation
rule, and records that route. When the current context and supported rules
cannot establish a requested fact, Litex stops there instead of silently
accepting it.

The aim is simple: conditions remain explicit and verification remains strict,
while the source stays close to the mathematics a reader wants to inspect.

## Verified facts become the next context

The first accepted conclusion is not merely output; it becomes context for
what comes next.

Here is a complete divisibility development. The definition says that
<code>d</code> divides <code>n</code> when an integer witness
<code>k</code> satisfies <code>n = d * k</code>. The theorem composes two
such witnesses. The final statements construct <code>3 | 12</code> and
<code>12 | 60</code>, then reuse the theorem to establish
<code>3 | 60</code>.

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divisibility_is_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(3, 12) from 4:
    12 = 3 * 4
witness $divides_by(12, 60) from 5:
    60 = 12 * 5
by thm divisibility_is_transitive(3, 12, 60) => $divides_by(3, 60)
```

The author supplies the mathematical move: expose the witnesses, multiply
them, and package the result. Litex checks each connection and stores accepted
facts for later use. This bottom-up proof flow is close to an ordinary
mathematical draft: establish something useful, keep it, and continue.

## Build a language for your mathematics

Litex is not only a way to check isolated answers. Definitions and structures
let a project create its own reusable mathematical language.

This example defines a group over a nonempty set, including multiplication,
identity, inverse, and the group laws. It then uses that interface to establish
that any element acting as a two-sided identity must equal the group's
declared identity.

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

The structure is more than a bundle of fields. It establishes a vocabulary
and a body of laws that later mathematics can use. A small team can begin from
sets, functions, and facts, then grow a domain interface without pretending
that mature libraries no longer matter.

For a larger, runnable example of this process, see
[Example of Building a Math System With Litex](showcases/Example_of_Building_A_Math_System_With_Litex/README.md).
Formal geometry itself is not new—projects such as
[LeanGeo](https://github.com/project-numina/LeanGeo) already build substantial
systems in Lean. This showcase asks a different question: can building a
checked mathematical system become direct enough for learners to participate,
so that formalization is part of learning mathematics rather than its final
translation? It grows a coordinate model of the Euclidean plane into geometric
predicates, bridge lemmas, and reusable theorems, then uses that system to
solve a concrete geometry problem. It also points toward interactive
textbooks in which explanation, experimentation, exercises, and verification
share one environment, while stating the example's remaining axiom boundary
explicitly.

## The human–AI verification loop

Fact growth becomes especially useful when a human or AI is exploring a proof:

```text
write a fact
    → inspect its verification route
    → retain valid progress
    → stop at an unknown or invalid step
    → repair that local step
    → continue from the checked context
```

An <code>unknown</code> result does not mean the proposition is false. It
means the current context and verifier have not established it. The next move
might be to add a missing condition, expose a witness, split a case, cite a
known theorem, or correct the formal statement.

Litex also supports transactional attempts: a failed attempt can roll back
without contaminating the context that was already checked. This gives humans
and agents a concrete repair boundary rather than an all-or-nothing answer.

The structured result of a definition or verification can be treated as a
**Checkable Knowledge Record**. It keeps the statement, relevant dependencies,
evidence, identifiers, and execution status available to people and tools;
JSON is a machine-readable representation, while Litex's graph command can
display relationships extracted from those records.

Four connected design choices support this loop:

| Design choice | What it changes for the author |
| --- | --- |
| **Set-theoretic surface** | Begin with sets, membership, functions on sets, and familiar mathematical structures. |
| **Fact-oriented** | Write the next fact that should hold; let the verifier look for supported local grounds. |
| **Bottom-up** | Let each accepted fact extend the context from which later facts can grow. |
| **Lean-compatible** | Compile supported recorded verification routes into Lean proof terms for independent checking. |

These are interface choices, not claims of universal superiority. Lean's type
theory, abstraction mechanisms, kernel, and Mathlib ecosystem remain much
stronger for many large formal developments.

## From formal language to AI for Math—and toward safe, efficient reasoning

These are three stages of one research direction, not three capabilities that
Litex already possesses at the same maturity.

### 1. Formal language

Litex's direct scientific object is the representation and step-by-step
construction of checkable knowledge. It tests whether mathematical facts,
immediate checking, growing context, and transactional repair can form a
useful formal-language interface for humans and AI.

The hypothesis must be measured: how long does formalization take, how much
breaks after a definition changes, can readers recover the intended
mathematics, can failed attempts be repaired locally, and can results be
reused?

### 2. AI for Math

Mathematics is the first rigorous testbed. Statements can be made precise,
proof attempts can receive machine-checkable feedback, and both successful
translations and failures can become evidence. Textbooks, datasets, and small
domain libraries therefore pressure-test Litex's language, standard library,
verifier, diagnostics, and proof organization.

Litex can expose local failures that an agent may repair and can produce
checked facts, provenance, and repair traces. This does not mean that Litex
has solved autoformalization or automated mathematical discovery.

### 3. Toward safe and efficient reasoning

Explicit facts, local grounds, transactional rollback, provenance, and
fail-closed compilation are also relevant beyond mathematics. If these
mechanisms prove useful under rigorous mathematical pressure tests, they may
inform AI systems whose reasoning is easier to inspect, repair, reuse, and
independently check.

That is a longer-term research direction. Litex currently checks a growing
body of mathematics; it does not claim to make general AI reasoning safe.

## Write in Litex. Recheck in Lean.

Litex aims to combine a readable front end with an increasingly rigorous
compatibility path:

```text
Litex source
    → Litex verifier and recorded evidence
    → ToLean
    → Lean proof terms
    → Lean kernel rechecking
    → optional handwritten Adapter / Mathlib interface
```

For **supported verification paths**, ToLean compiles source-owned Litex
declarations and recorded evidence into Lean proof terms. Lean can then check
those terms independently. Unsupported or trusted routes must fail closed
rather than silently becoming <code>sorry</code> or hidden project axioms.

The optional adapter is separate from generated proofs: a human or AI may use
it to expose ordinary Lean/Mathlib concepts without allowing the compiler to
invent mathematics that was absent from the Litex source.

Coverage is still partial. A statement accepted by the Litex verifier has not
automatically passed the Lean kernel; only a route that is fully compiled and
actually accepted by Lean gains that additional check. See the
[ToLean implementation and coverage](lean/README.md) and the
[Litex → Lean → Mathlib showcase](showcases/Litex_to_Lean_Mathlib_Pipeline/README.md).

## Where Litex can be useful

The following are potential areas of strength to test through real work:

- **Mathematical notebook:** turn everyday derivations into checked mathematics quickly.
- **Formalization middle layer:** connect natural-language mathematics with mature systems such as Lean.
- **New-domain incubator:** experiment with definitions, interfaces, and small domain libraries at low initial cost.
- **AI proof training ground:** produce local feedback, repair trajectories, and classified failures.
- **Checkable knowledge record:** preserve definitions, facts, dependencies, and verification status for interactive textbooks and knowledge bases.

Current areas where mature systems such as Lean/Mathlib are stronger:

- **Mature-library reuse:** large developments that depend heavily on existing formal mathematics.
- **Deep abstraction engineering:** complex type structures and large, highly abstract theory hierarchies.
- **Long-lived trusted assets:** public-library maintenance, auditing, compatibility, and final trusted delivery.

These boundaries are part of the project, not disclaimers to hide. Successful
translations provide evidence about cost and reuse; failed translations reveal
language, library, verifier, diagnostic, kernel, or compiler gaps.

## Try Litex

[Try Litex](https://litexlang.com) ·
[Website](https://litexlang.com) ·
[Blueprint](docs/Litex_Blueprint.md) ·
[Learner Cheatsheet](docs/Litex_Learner_Cheatsheet.md) ·
[Manual](docs/Manual.md) ·
[GitHub](https://github.com/litexlang/golitex)

For a local installation, see the short [setup guide](docs/setup.md). On macOS
and Linux with Homebrew:

```bash
brew install litexlang/tap/litex
litex -version
litex -e '1 = 1'
```

Continue with the [examples](examples/README.md), the
[Litex Learner Cheatsheet](docs/Litex_Learner_Cheatsheet.md), the full
[manual](docs/Manual.md), or the [CLI reference](docs/cli.md).

## About

I am Jiachen Shen (沈嘉辰), a mathematics PhD student at Fudan University who
loves both mathematics and programming. Lean showed me that these worlds can
meet in a real language. It also made me wonder whether formal source could
follow more closely the mental flow I use when solving mathematical problems.
Litex is the result of that exploration.

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Yi Wang, Chenxuan Huang, Yan Lu,
Sheng Xu, Keyao Zhu, Xingjian Ma, and Zhaoxuan Hong for their support and advice.

Mathematics is the unseen skeleton deep within the edifice of science. We
believe that any mathematics can be formalized, and that formalized mathematics
will ultimately become the future of mathematics. Litex hopes to become one of
the building blocks of that future.

Natural language is easy to understand but often ambiguous; existing
formalization tools such as Lean are rigorous and reliable, but typically have
a high technical barrier. Litex starts from the premise that mathematical
expression can be both understandable and rigorous. Between comprehensibility
and verifiability, we do not have to choose.

Litex is released under the [Apache License 2.0](LICENSE).
