# Manual Introduction

Try all snippets in browser: https://litexlang.com/doc/Manual/Manual_Introduction

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Manual_Introduction.md

This manual explains how Litex reads and checks mathematical proof scripts. The main idea is simple: a piece of Litex code introduces mathematical objects, states facts about them, checks those facts, and stores the successful facts for later use.

Litex has many builtin concepts because ordinary mathematics has many small background steps. Numbers, sets, membership, equality, functions, tuples, products, order, finite displays, and positivity facts constantly interact. Litex puts this shared background into the language so user proofs can focus on the mathematical idea instead of repeating basic bookkeeping.

This is the main usability advantage of Litex: proof code can stay close to the way a person would write the argument on paper. For example, using a known value can be written as direct algebraic steps:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

The corresponding Lean 4 proof has to expose more proof-engine details:

```lean
import Mathlib.Tactic

example (x : ℝ) (h : x = 2) : x + 1 = 3 ∧ x ^ 2 = 4 := by
  have h_add : x + 1 = 3 := by
    rw [h]
    norm_num
  have h_square : x ^ 2 = 4 := by
    rw [h]
    norm_num
  exact ⟨h_add, h_square⟩
```

Litex's checker is designed to remember known facts, use builtin arithmetic and substitution, and infer routine consequences automatically. The result is usually shorter code, fewer proof-engine details, and a lower learning burden for everyday mathematical proofs.

> Litex is different from Lean in design goals and surface style, but its author deeply respects Lean. If you are interested in how the two languages differ in foundations, examples, strengths, and tradeoffs, see [Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean/Typical_Examples).

---

## Mental model

When learning Litex, it is enough to keep the following mental model in mind. Try to connect each Litex idea with its everyday mathematical counterpart: the objects you write, the facts you claim, the statements that organize the proof, and the checker steps that justify and store those facts.

- **Objects** are the mathematical things a proof talks about: numbers, sets, tuples, functions, products, sequences, matrices, and names introduced earlier.
- **Facts** are judgments about objects: `x = 2`, `x $in N`, `0 <= x`, `$is_set(A)`, or a user-defined predicate such as `$prime(n)`.
- **Statements** are the user-facing forms that introduce objects, define concepts, organize local proofs, and assert facts.
- **Verification** proves the current goal from the context, definitions, evaluation, normalization, and builtin verification rules.
- **Execution** is what a statement does to the current context. A statement may define a name, open a proof block, verify a fact, store accepted facts, or run inference. Inference is one part of execution for factual statements: after a fact is accepted, Litex may add standard consequences or side information to the context.

The key distinction is that an expression such as `x + 1` is only an object. It becomes a fact only when a relation or predicate makes a claim about it, such as `x + 1 = 3`.

Many uncommon forms can be skipped at first. Read them when a proof needs them; the common core above is enough for most early examples.

---

## First reading path

If you are reading the manual to understand how Litex works, start with the things Litex handles, then read how it verifies and executes them.

**What Litex works with**

1. [Objects](https://litexlang.com/doc/Manual/Objects): the mathematical terms and data-like structures Litex can talk about.
2. [Builtin Predicates](https://litexlang.com/doc/Manual/Builtin_Predicates): the common builtin predicates used to make atomic facts, such as `=`, `<`, `$in`, `$subset`, and `$is_set`.
3. [Factual Statements](https://litexlang.com/doc/Manual/Factual_Statements): how atomic facts combine into chains, conjunctions, disjunctions, `exist`, and `forall`.
4. [Statements](https://litexlang.com/doc/Manual/Statements): the statement forms used to introduce definitions, context, and proof blocks.

**How Litex verifies facts**

1. [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules): the builtin steps that can close goals while checking a fact.
2. [Proof Process](https://litexlang.com/doc/Manual/Proof_Process): the end-to-end flow from writing statements to checked facts.

**How Litex executes code**

1. [Statements](https://litexlang.com/doc/Manual/Statements): what each statement does when it is executed.
2. [Inference](https://litexlang.com/doc/Manual/Inference): the extra execution step for accepted facts, adding consequences so later statements can use a richer context.

