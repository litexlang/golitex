# Litex FAQ

Jiachen Shen and The Litex Team, 2026-06-03. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/FAQ.md

This page collects common questions about Litex's design, performance model,
and intended proof style. It is written as a living note: answers should stay
concrete, modest, and close to the current verifier behavior.

## If there are ten thousand `forall` facts, will proving one proposition become slow?

It can become slow if all ten thousand universal facts are active automatic
matching candidates in the same context. Litex's proof model uses known facts,
builtin rules, substitution, and known `forall` facts to justify later facts.
That is useful because users can write the mathematical fact they want, but it
also means the active context should not be treated as an unbounded global
search space.

There are two main design answers.

First, use `thm` for named theorems that should be called explicitly. A
`thm` proves and stores a named theorem, but it does not add its `forall` body
as an ordinary automatic `forall` matching fact. To use it, the proof says
`by thm name(args...)`. That makes large, classic, expensive, or
parameter-sensitive results explicit proof dependencies instead of background
noise.

Second, organize broad mathematical background into packages. A theorem about
groups should live in a group-related package; a theorem about real analysis
should live in a real-analysis package. The user imports the package when that
background is actually needed. This keeps the active known-fact and known-`forall`
space closer to the topic of the current proof.

A practical rule of thumb is:

- use automatic `forall` matching for short, local, common facts whose intended
  instantiation is obvious from the goal shape;
- use `claim forall` or direct `forall` facts when you want a helper to behave
  like local reusable context;
- use `thm` plus `by thm` when the theorem name and arguments should be visible
  in the proof;
- split standard-library facts by subject and import only the subjects needed
  for the current file.

This is not only a performance issue. It is also proof readability. If a fact
is mathematically important, the proof is often clearer when it names that fact
directly.

## What is fundamentally different about Litex?

Litex's core difference is its matching-and-substitution verification
interface.

The user writes mathematical facts: equalities, memberships, implications,
existential witnesses, `forall` statements, function facts, set facts, and
predicate facts. The verifier then asks whether the new fact follows from the
current verified context by builtin rules, known facts, known `forall` facts,
definitions, matching, and substitution.

So the central interaction is not "choose a tactic that transforms the proof
state." It is closer to:

1. write the next mathematical fact;
2. let Litex match it against the verified context and trusted mathematical
   background;
3. if it succeeds, store the fact and continue growing the context;
4. if it fails, inspect whether the missing step is a missing fact, missing
   theorem call, missing library support, or a real gap in the argument.

This is why Litex proofs often look like ordinary mathematical prose or
calculation chains. The proof script exposes the facts that should be true, and
the checker performs routine matching and replacement steps that a human reader
would usually do silently.

This does not mean Litex proves arbitrary goals by magic. It means Litex places
more ordinary mathematical structure inside the verifier and standard library,
then gives the user a fact-oriented interface to that structure. The trade-off
is explicit: Litex has a larger trusted implementation than a small-kernel proof
assistant, so builtin rules, infer rules, `know`, and standard-library facts
need clear boundaries, tests, and audit-friendly output.

Litex should therefore be described as complementary to Lean, Coq, and Isabelle,
not a replacement for them. Those systems expose deeper foundations and much
larger mature libraries. Litex tests a narrower hypothesis: many ordinary
mathematical arguments may become cheaper to check if the main proof interface
is verified context growth through matching and substitution.
