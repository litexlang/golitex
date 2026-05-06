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

---

## The proof model

A typical Litex check follows this path:

```text
statement
factual statement
atomic facts
verification
stored facts
inference
later statements
```

The pieces mean:

- **Objects** are the mathematical things a proof talks about: numbers, sets, tuples, functions, products, sequences, matrices, and names introduced earlier.
- **Facts** are judgments about objects: `x = 2`, `x $in N`, `0 <= x`, `$is_set(A)`, or a user-defined predicate such as `$prime(n)`.
- **Verification** proves the current goal from the context, definitions, evaluation, normalization, and builtin verification rules.
- **Inference** runs after a fact is accepted, adding standard consequences or side information to the context.
- **Statements** are the user-facing forms that introduce objects, define concepts, organize local proofs, and assert facts.

The key distinction is that an expression such as `x + 1` is only an object. It becomes a fact only when a relation or predicate makes a claim about it, such as `x + 1 = 3`.

---

## First reading path

If you are reading the manual to understand how Litex works, use this order:

1. [Proof Process](Proof_Process.md): the end-to-end flow from a statement to checked facts, storage, and inference.
2. [Objects](Objects.md): the mathematical terms and data-like structures Litex can talk about.
3. [Builtin Props](Builtin_Props.md): the common atomic proposition forms, such as `=`, `<`, `$in`, `$subset`, and `$is_set`.
4. [Factual Statements](Factual_Statements.md): how atomic facts combine into chains, conjunctions, disjunctions, `exist`, and `forall`.
5. [Builtin Verification Rules](Builtin_Verification_Rules.md): the builtin steps that can close goals while checking a fact.
6. [Builtin Inference](Builtin_Inference.md): the consequences added after a fact is accepted.
7. [Builtin statements](Statements.md): the statement forms used to introduce definitions, context, and proof blocks.

This path starts with the proof flow, then fills in the vocabulary used by that flow.

---

## Reference path

If you already know what you want to write, jump directly to the relevant page:

- Use [Statements](Statements.md) when you want to know how to write `have`, `prop`, `claim`, `prove`, `know`, `witness`, imports, and similar top-level forms.
- Use [Factual Statements](Factual_Statements.md) when you want to know what shapes of facts Litex can check.
- Use [Objects](Objects.md) when you want to know how to write sets, functions, tuples, products, sequences, matrices, and other terms.
- Use [Builtin Props](Builtin_Props.md) when you want to know the common atomic fact forms.
- Use [Builtin Verification Rules](Builtin_Verification_Rules.md) when you want to know which goals the checker can close automatically.
- Use [Builtin Inference](Builtin_Inference.md) when you want to know what extra facts become available after a fact is stored.

For how this builtin world fits into user definitions, `forall` proofs, and execution traces, see [Mechanics of Litex](../Mechanics_of_Litex.md).
