<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### A formal language where mathematics verifies itself

Created and maintained by Jiachen Shen.

[Website](https://litexlang.com) · [Blueprint](docs/Litex_Blueprint.md) · [中文蓝图](docs/Litex中文蓝图.md) · [Manual](docs/Manual.md) · [Cheat Sheet](docs/cheatsheet.md) · [Install](docs/Setup.md) · [Examples](examples/README.md) · [Zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)

**Litex is an experimental hobby project in beta. Expect rough edges.**
</div>

Litex is a **set-theory-based, fact-oriented, bottom-up, Lean-compatible**
formal language. It is designed for writing readable mathematics that a machine
can check while keeping the source close to the objects, facts, and proof flow a
mathematician has in mind.

Litex is not trying to replace Lean. It tests a different hypothesis: that a
smaller, readable, fact-oriented language can make checked mathematics cheap
enough for students, domain scientists, and AI agents to produce useful formal
data at scale.

## See the design in one fact

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

This is a complete statement submitted to the verifier, not a proof hole. It
says that intersecting both sides with the same set preserves inclusion. Litex
checks that the expressions are well-defined, unfolds the relevant membership
facts, transports membership through `s $subset t`, and records why the result
was accepted.

The example already shows three design choices: sets and membership are visible
at the surface; the user writes the mathematical fact that should hold; and the
verifier reconstructs the routine local justification. The fourth choice is to
record enough evidence for supported verification paths to be checked again by
Lean.

## The blueprint in four design choices

These choices are meant to reinforce one another:

| Design choice | What it changes for the author |
| --- | --- |
| **Based on set theory** | Start from sets, membership, functions on sets, and familiar mathematical structures. |
| **Fact-oriented** | Write the next fact that should hold; let the verifier search for an acceptable local justification. |
| **Bottom-up** | Let every accepted fact extend the context from which later facts can grow. |
| **Lean-compatible** | Compile the verification paths currently supported by the backend into Lean proof terms for independent checking. |

### 1. Let set-theoretic mathematics look like set theory

Litex organizes its user-facing language around sets, membership, and relations
between sets. A function can be written as a function from one set to another;
a structure can be written as operations and laws on a carrier set. Users do
not first have to organize the same mathematics through type universes.

That is a choice of interface, not a claim that type theory is unnecessary.
Lean's type-theoretic design provides powerful abstraction, composition, and a
mature ecosystem. Litex chooses a narrower, membership-centered surface because
it is often closer to the way set-theoretic mathematics is already written.

### 2. Make facts the executable unit of source

```litex
have a R = 1
have b R = 2

a + b >= 0
```

The last line has no theorem name and invokes no tactic. The verifier sees the
shape of the requested fact, finds a relevant nonnegativity rule, checks its
premises from the current context, and accepts or rejects the fact. Successful
facts are then available to later lines.

Litex can justify a submitted fact from builtin rules, user-provided universal
facts, concrete facts and known equalities, definitions, or an explicit proof
process. Its central division of labor is:

> The author writes **what mathematical fact should hold**. Litex searches for
> **how that fact can be verified**, then exposes the route it used.

This does not mean that names are forbidden or that every fact is automatic.
Stable interfaces can be named as theorems, and proofs can explicitly use
witnesses, contradiction, cases, induction, definitions, or named theorems
when the mathematics calls for them.

### 3. Grow proofs from known facts

Consider membership transported through two inclusions. A common Lean tactic
proof starts from the final goal and works backward:

```lean
example {α : Type} {A B c : Set α}
    (hAB : A ⊆ B) (hBc : B ⊆ c)
    {x : α} (hx : x ∈ A) :
    x ∈ c := by
  apply hBc
  apply hAB
  exact hx
```

The corresponding Litex proof grows forward from the known membership:

```litex
forall A, B, c set, x A:
    A $subset B
    B $subset c
    =>:
        x $in B
        x $in c
```

After `x $in B` is checked, it becomes part of the context used to check
`x $in c`. This is Litex's default bottom-up flow: derive a useful fact, keep
it, and continue. Goal-directed blocks still exist when working backward is the
clearer mathematical move.

The distinction is about the default interface, not an exclusive capability
boundary. Lean supports forward and declarative styles; Litex supports goals
and explicit proof structure. Litex simply makes a verified fact that extends
the context its ordinary unit of execution.

### 4. Use Lean as an independent checking path

Litex has its own parser, runtime, verifier, builtin rules, and inference rules.
That makes it independently usable, but it also gives Litex a larger trusted
implementation than a small proof-assistant kernel.

The Litex-to-Lean compiler addresses this boundary by translating recorded
Litex verification evidence into Lean proof terms over native Lean and Mathlib
representations. The current compiler covers only part of the language. Covered
routes are checked by Lean; unsupported or trusted routes fail instead of
becoming `sorry` or hidden axioms. See the [compiler README](lean/README.md) for
the implemented surface and current limits.

“Every Litex file compiles to Lean” is a direction of work, not a capability of
the current beta.

## Why build this now?

AI makes it increasingly cheap to generate candidate mathematics. The harder
problem is to check, repair, review, reuse, and accumulate that mathematics.
Formal languages can provide this infrastructure, but their first-contact
experience is still usually designed for specialists.

Litex explores whether a language specialized for mathematics can offer a
different entry point:

- a learner can express familiar mathematics before learning proof-assistant
  internals;
- a mathematician or domain scientist can keep the formal source close to the
  argument they want to communicate;
- an AI agent can propose the next small mathematical fact and repair it from
  a local verification failure; and
- a reviewer can inspect the written statement, its dependencies, and its
  trust boundary separately.

Real mathematical work is the pressure test. Textbooks and datasets are used
to find concrete gaps in the language, standard library, verifier, inference
rules, diagnostics, and proof organization. Successful translations become
examples or benchmarks; failed translations become explicit blocker evidence
rather than being hidden.

## Try Litex

The fastest route is the [online playground](https://litexlang.com). For a
local installation, see the [setup guide](docs/Setup.md). On macOS and Linux
with Homebrew:

```bash
brew install litexlang/tap/litex
litex -version
litex -e '1 = 1'
```

Useful next steps:

- [Examples](examples/README.md) — small proof patterns, builtin mathematics,
  language features, and case studies;
- [Cheat Sheet](docs/cheatsheet.md) — a compact choose-the-next-authoring-action
  reference;
- [Manual](docs/Manual.md) — the language and verifier reference;
- [Blueprint](docs/Litex_Blueprint.md) / [中文蓝图](docs/Litex中文蓝图.md) — the
  full design argument and comparisons;
- [System map](docs/Litex_System_Map.md) — how parsing, verification, evidence,
  and output fit together; and
- [Contributing](docs/How_To_Contribute.md) — how to report gaps and contribute.

## What a successful result means

A successful run means that the current Litex parser, runtime, verifier,
accepted rules, imported libraries, and declared context accepted the
statement. It does **not** mean that the implementation is bug-free or has the
audit history of a mature proof assistant.

Read every result relative to its trusted background:

- builtin objects, verification rules, and inference rules;
- imported packages and source-local interfaces;
- explicit `trust` and `axiom` assumptions; and
- the current implementation and test coverage.

`trust` and `axiom` introduce assumptions; they are not checked derivations.
Tests reduce risk but do not eliminate it. When a verification path can also be
compiled and accepted by Lean, that provides an additional, independent check
for that covered path.

## About

I am Jiachen Shen, a mathematics PhD student at Fudan University who loves both
mathematics and programming. Lean showed me that these worlds can meet in a
real language. It also made me wonder whether formal source could follow more
closely the mental flow I use when solving mathematical problems. Litex is the
result of that exploration.

The project has received support and advice from many friends and
collaborators. Special thanks to Wei Lin, Siqi Sun, Peng Sun, Yi Wang, Chenxuan
Huang, Yan Lu, Sheng Xu, and Zhaoxuan Hong.

Litex is released under the [Apache License 2.0](LICENSE).
