<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### Write math, get formalized code: because the math already is.

**Pronunciation:** /ˈliːtɛk/ (“LEE-tek”, Chinese “里泰克”), not “LYE-tek” (“赖泰克”).

Created and maintained by Jiachen Shen.

[中文 README](docs/中文README.md) ·
[Official Website (官网)](https://litexlang.com) ·
[Why I built Litex](docs/Motivation_and_Construction_Thinking_Behind_Litex.md)
[Github](https://github.com/litexlang/golitex)
</div>

<a id="the-goal-of-litex"></a>

## Could mathematics itself be the formal language?

Mathematics is already a rigorous language. We introduce objects, give
definitions, state facts, and justify each step from what we know. I started
Litex with a question: **could we make that writing directly checkable by a
machine, adding just enough structure to make its meaning precise?**

In Litex, this is a complete piece of formal source:

```litex
1 + 1 = 2
```

The checker reads the mathematical statement itself. More involved arguments
need definitions, conditions, and proof steps, but the goal stays the same:
write the mathematics you mean, and let the language check the reasoning.

That idea determines how Litex is built: its mathematical objects and their
meanings, its syntax, its verification engine, and the explanations it returns.
Here is how those choices follow from one another.

<a id="familiar-mathematics"></a>
<a id="mathematical-objects"></a>

## Start with the mathematics

The first question is what mathematics the language should express. I chose
a set-theoretic foundation: sets, elements, functions, and relations are already
part of how many of us learn and use mathematics. Membership is a mathematical
fact: `1 $in N` and `1 $in R` say different things about the same number.

Familiar symbols also need familiar meanings. Consider three expressions:

| Expression | Usual textbook convention | Lean / Mathlib | Litex |
| --- | --- | --- | --- |
| Division by zero | `1 / 0` is undefined. | `(1 : ℝ) / 0 = 0` | Rejects `1 / 0 = 0`: the denominator must be nonzero. |
| Subtracting a larger natural number | In integer arithmetic, `1 - 2 = -1`. | `(1 : Nat) - 2 = 0` | `1 - 2 = -1`; the result belongs to `Z`. |
| Real square root of a negative number | `-1` has no real square root. | `Real.sqrt (-1) = 0` | Rejects `sqrt(-1) = 0`: the input must be nonnegative. |

Lean/Mathlib deliberately uses these conventions for
[division](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/Basic.html#div_zero),
[natural-number subtraction](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/#Nat.sub),
and [real square roots](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Real/Sqrt.html#Real.sqrt_eq_zero_of_nonpos).
Choosing `Int` instead gives `(1 : Int) - 2 = -1` in Lean. A formal checker
checks the definitions it is given; the author still needs to know whether
those definitions express the intended mathematics.

I want Litex to make ordinary mathematical meanings and their conditions of
use part of the default writing experience. For example, the nonzero condition
belongs in the definition of a reciprocal:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

The condition `x != 0` is checked whenever the function is used. Keeping the
usual meaning of division requires the language to check its domain.

<a id="direct-facts"></a>

## Let mathematical statements be the syntax

With that vocabulary in place, the next question is how to write it. Litex
uses Python-like indentation to organize mathematical sentences. “For any two
nonnegative real numbers, their sum is nonnegative” becomes:

```litex
forall x, y R:
    x >= 0
    y >= 0
    =>:
        x + y >= 0
```

Introduce the objects, state the assumptions, then state the conclusion.
The assumptions come before `=>:`; what follows must be checked.

Definitions use the same mathematical vocabulary. Collect the positive real
numbers into a set, then check that two belongs to it:

```litex
have positive_reals set = {x R: x > 0}
2 $in positive_reals
```

Define distance from zero, establish its nonnegativity, and calculate with it:

```litex
have fn distance_from_zero(x R) R = |x|

forall x R:
    distance_from_zero(x) = |x| >= 0

distance_from_zero(-3) = distance_from_zero(3) = 3
```

The same approach extends to statements about sets. Here are two ways to
write that intersection preserves an inclusion:

<table>
<thead><tr><th>Litex</th><th>Lean / Mathlib (handwritten)</th></tr></thead>
<tbody><tr>
<td valign="top"><pre><code>forall s, t, u set:
    s $subset t
    =&gt;:
        intersect(s, u) $subset intersect(t, u)</code></pre></td>
<td valign="top"><pre><code>import Mathlib
example {α : Type*} (s t u : Set α) (h : s ⊆ t) :
    s ∩ u ⊆ t ∩ u := by
  intro x hx
  exact ⟨h hx.1, hx.2⟩</code></pre></td>
</tr></tbody>
</table>

Litex checks this implication directly using its set rules. It also accepts
`s ∩ u ⊆ t ∩ u` as the symbolic spelling of the conclusion. The source uses
a controlled formal syntax, with a close correspondence to mathematical
sentences; see the [notation guide](docs/Manual.md#unicode-mathematical-input-aliases-preview).

This choice puts the next mathematical fact at the center of writing a proof.
The Lean example shows a common tactic style; Lean also offers other proof
styles and automation. In longer Litex arguments, authors still supply the
mathematical route: intermediate facts, witnesses, or case splits. The verifier
checks the local connections it supports.

<a id="knowledge-workflow"></a>

## Build a verifier around the next fact

For that syntax to work, the verifier has to answer a particular question:
**given the current mathematical context, what justifies this statement?**

```litex
have a R = 2
a + 1 = 3
```

The first line introduces `a` and records `a $in R` and `a = 2`. The second
line can use that knowledge. Once checked, `a + 1 = 3` becomes available to
later steps too. A source file builds a mathematical context as it proceeds.

My first implementation idea was matching and substitution: find a relevant
known fact, match it against the statement, and check the required conditions.
That developed into structured fact lookup, bounded recursive verification,
built-in mathematical rules, and explicit proof steps.

**Turning familiar mathematical expressions, step by step, into mathematical
knowledge a machine can recognize, store, and use is the core of the Litex
project.** The difficulty is preserving mathematical meaning throughout that
chain: identifying the objects and facts in a statement, checking domains and
premises, retaining scope and justification, and enabling later reasoning to
find and correctly apply that knowledge under the right conditions.

I think of the storage and lookup as a database specialized for mathematical
reasoning. Its design must work together with parsing, representation, and
verification so that a fact established in one step can become usable knowledge
in the next. The experience of writing mathematics directly rests on getting
all these parts to work together. The [source reading guide](src/README.md)
follows `a + 1 = 3` through the actual implementation.

## Make the reasoning inspectable

I also want to see why a statement was accepted, what it established, and
where a failed step stopped. Return to `1 + 1 = 2`. Running
`litex -lang en -e '1 + 1 = 2'` returns JSON; its statement result is:

```json
{
  "statement_result": "accepted",
  "statement": "(1 + 1) = 2",
  "proof_method": {
    "type": "by_closed_calculation",
    "rule_name": "Closed calculation",
    "message": "Exact evaluation of closed expressions without proof search"
  },
  "stores": [
    "(1 + 1) = 2"
  ],
  "infers": []
}
```

The source states the mathematics. The output reports the checking method,
the fact stored, and any inferred facts. Here the justification is an exact
closed calculation. For `1 / 0 = 0`, the rejection instead identifies
well-definedness and the unmet obligation `0 != 0`.

Syntax, semantics, and output belong together: what did I say, what does it
mean, and on what grounds can it be accepted? Normal JSON summarizes the
verification; it does not expose every dependency. The
[CLI reference](docs/cli.md#json-output-contract) documents that contract,
including feedback languages such as Chinese via `-lang zh`.

<a id="human-ai-feedback"></a>
<a id="work-with-people-and-ai-through-feedback"></a>
<a id="independent-lean-rechecking-is-a-goal"></a>
<a id="lean-rechecking"></a>

## What follows from that record

Once the source and its checking results are available together, they give us
something to build on.

A person or AI agent can propose a step, inspect the feedback, and revise it.
In one persistent `-session`, an ordinary rejection preserves earlier accepted
knowledge: after `have a R = 2`, rejecting `a = 3` still leaves `a + 1 = 3`
checkable. Keep that Session open while writing; the
[Agent Guide](docs/AgentGuide.md) explains the workflow and restart boundaries.
I want to build a capable mathematical agent around this interaction.

The verification results also provide a bridge to Lean. The experimental
`litex -lean -f <standalone-file>` compiler uses the source and typed results
to generate Lean statements and proofs along supported routes. Lean can then
independently check those generated proofs. Explore the
[source/generated pairs](lean/examples/) and a
[complete Mathlib adapter example](showcases/litex_to_lean_adapter/README.md).
Coverage and faithful translation need to be established route by route;
generation and Lean checking are separate steps. The
[compiler guide](docs/Litex_To_Lean_Compiler_Guide.md) describes current support.

I also see possibilities for knowledge graphs and interactive mathematical
textbooks built around definitions, facts, and their explanations. These are
directions I want to explore. Existing tools already expose
[JSON](docs/cli.md#json-output-contract) and
[LaTeX export](src/compile_to_latex/README.md); LaTeX export renders parsed
source without verifying it.

## Try Litex

Use the [online playground](https://litexlang.com), or install with Homebrew
on macOS or Linux:

```bash
brew install litexlang/tap/litex
litex -e '1 + 1 = 2'
```

Other platforms and checkout builds are covered in the [setup guide](docs/setup.md).
Start writing with the [Manual](docs/Manual.md) and
[small examples](examples/README.md), or read a mathematical development in
the [showcase collection](showcases/README.md).

Litex is an experimental beta project. Its verifier, builtin and inference
rules, and mathematical foundations are part of the trusted basis. User-written
`trust` and `axiom` add assumptions; `-strict` rejects executed user assumptions,
including imported ones, while retaining the fixed foundations. See the
[trust and strict-mode guide](docs/Manual.md#trust-and-strict-mode).

## About

I am Jiachen Shen (沈嘉辰), a mathematics PhD student at Fudan University and
the creator of Litex. Lean showed me that mathematics and programming could
meet in a real language. Litex grew from wanting to explore how closely that
language could follow the way we write and understand mathematics.

I explore these questions by building something I can use, inspecting what it
does, and letting each answer expose the next question. My hope is that more
people who use mathematics can also write, understand, and contribute to
machine-checkable mathematics.

The longer [motivation essay](docs/Motivation_and_Construction_Thinking_Behind_Litex.md)
([中文](docs/Litex的缘起与构建思路.md)) develops this design path. The
[Blueprint](docs/Litex_Blueprint.md) ([中文](docs/Litex中文蓝图.md)) explores the
broader project and its evidence. Hard examples, edge cases, and constructive
feedback are welcome.

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu,
Sheng Xu, Keyao Zhu, and Zhaoxuan Hong for their support and advice.

Litex is released under the [Apache License 2.0](LICENSE).
