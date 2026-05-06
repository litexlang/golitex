# Introduction to Litex Builtin Features

Try all snippets in browser: https://litexlang.com/doc/Manual/Introduction_of_Builtin_Rules

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Introduction_of_Builtin_Rules.md


**Builtin features** are the shared mathematical background that comes with Litex. They tell the checker what mathematical objects exist, what atomic facts can be written about them, which goals can be proved automatically, and what consequences are added after a fact is stored.

The core loop is:

```text
write a statement
check the factual statement inside it
reduce complex facts to atomic goals
prove atomic goals from context, definitions, and builtin verification rules
store accepted facts
run builtin inference so later statements see standard consequences
```

The important distinction is not syntax versus magic. It is the separation between **objects**, **facts**, **verification**, **inference**, and **statements**:

- **Objects** are the mathematical things a proof talks about, such as numbers, sets, functions, tuples, products, and sequences.
- **Facts** are judgments about objects, such as `x = 2`, `x $in N`, `0 <= x`, or `$is_set(A)`.
- **Verification** is the process of proving the current goal.
- **Inference** runs after a fact is accepted and adds standard consequences to the context.
- **Statements** are the surface forms users write to introduce objects, define predicates, organize proof blocks, and assert facts.

Each builtin rule is usually easy to read in isolation. The real size comes from combinations: equality, membership, products, `fn`, ranges, positivity, finite sets, tuples, and order facts constantly meet in ordinary proofs. Builtin features exist so that this basic mathematical bookkeeping stays in the language instead of being repeated in every user proof.

For the full proof-flow explanation, start with [Proof Process](Proof_Process.md). The best way to understand a concrete proof is also to read the message printed after a statement is executed, because it shows how the statement affects the context.

---

## How this folder is organized

Read the pages in this order if you want the design story:

1. [Proof Process](Proof_Process.md): the full loop from statement to fact checking, storage, and inference.
2. [Builtin Objects](Builtin_Objects.md): what mathematical terms and data-like structures Litex can talk about.
3. [Builtin Props](Builtin_Props.md): the atomic proposition forms built into the surface language.
4. [Factual Statements](Factual_Statements.md): how atomic facts combine into chains, conjunctions, disjunctions, `exist`, and `forall`.
5. [Builtin Verification Rules](Builtin_Verification_Rules.md): goals the checker can close during verification.
6. [Builtin Inference](Builtin_Inference.md): facts and side information added after storage.
7. [Builtin statements](Statements.md): the statement forms that organize definitions, declarations, proof blocks, and context changes.

Together, these describe **what Litex already knows** before your own `prop`s and `forall` theorems enlarge the theory. For how that builtin world fits into the bigger proof story with user definitions, `forall`, and traces, see [Mechanics of Litex](../Mechanics_of_Litex.md).

