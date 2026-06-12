# Litex Architecture

Jiachen Shen and The Litex Team, 2026-06-10. Email: litexlang@outlook.com

Try the examples in browser: https://litexlang.com/doc/Architecture

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Architecture.md

This page explains the main architecture of Litex for users and contributors
who want to understand what happens after a `.lit` file is run. It is not a
soundness proof and not a claim that Litex already has the small-kernel trust
model of mature proof assistants. The current system is better understood as a
larger trusted implementation with clear layers around fact-oriented checking.

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [CLI](https://litexlang.com/doc/cli) for the supported language codes.

## Big Picture

Litex is built around one loop:

1. The user writes a mathematical statement.
2. Litex parses it into internal objects, facts, and statements.
3. Execution updates the current mathematical context.
4. Factual statements are verified against builtin rules, known facts, known
   `forall` facts, definitions, and local assumptions.
5. Accepted facts are stored, routine consequences may be inferred, and later
   statements can reuse the updated context.
6. Output explains the result, including why a fact was accepted or where it
   became unknown.

In short: users write facts; Litex grows a checked context and reports the
reasoning route it used.

## Core Flow

The core call flow can be read as:

```text
source text
  -> tokenizer / TokenBlock
  -> parse_stmt / parse_obj / parse_fact
  -> Stmt / Obj / Fact AST
  -> exec_stmt
  -> Runtime + Environment mutation
  -> verify_fact / verify_atomic_fact / builtin rules / known facts / known forall
  -> infer facts after storing checked facts
  -> StmtResult + display / LaTeX / CLI output
```

The important point is that parsing, execution, verification, inference, and
output are different responsibilities. They are connected by the runtime, but
they are not the same layer.

## Main Layers

### Parsing

`src/parse/` turns source text into token blocks and then into parsed Litex
statements, objects, and facts. This layer is about surface syntax: indentation,
headers, object syntax, fact syntax, and statement forms.

The parser should not be treated as the proof engine. It decides what the user
wrote, not whether the mathematics follows.

### Statement And Object Data

`src/stmt/`, `src/obj/`, and `src/fact/` hold the internal data structures that
represent Litex statements, mathematical objects, and facts. Keeping these
separate from the parser is useful because many surface forms can map into a
smaller set of internal concepts.

This boundary is also where Litex keeps a useful distinction:

- objects are mathematical terms, such as `x + 1`, `{1, 2}`, `sqrt(x)`, or
  function applications;
- facts are judgments about objects, such as `x + 1 = 3`, `x $in R`, or
  `$is_set(A)`;
- statements are actions in a file, such as introducing objects, defining
  vocabulary, asserting facts, opening proof blocks, or importing modules.

### Execution

`src/execute/` runs one statement at a time. Execution is broader than proof:
a statement may introduce a name, define a predicate, run a proof block, store
a verified fact, import a module, or call theorem machinery.

This is why `exec_stmt` and `verify_fact` are separate. Executing a statement
is about changing or inspecting the runtime state. Verifying a fact is one
specific operation that execution may need.

### Runtime And Environment

`src/runtime/` stores the active proof context. The `Runtime` tracks the
current environment, module state, name scope, output mode, and source labels.
The `Environment` is intentionally broad: it is the physical container for the
mathematical context.

The environment keeps information such as:

- defined objects and predicates;
- known atomic facts;
- known `forall` facts that can be matched against future goals;
- theorem and claim information;
- object-property caches;
- strategy registrations and other proof-context data.

This makes `Environment` a large structure, but it has a clear role: it is the
place where the growing mathematical world lives.

Imports have their own important state boundary. Imported-module runtimes are
created from the parent runtime with `Runtime::new_for_import_from_parent`, so
nested imports, cycle checks, stopped-module state, source labels, and module
manager state stay consistent across the whole top-level run.

### Verification

`src/verify/` is the fact-checking layer. It receives a fact and asks whether
that fact follows from the current context and trusted background.

Verification may use:

- builtin verification rules for common mathematics, such as calculation,
  equality, order, membership, sets, tuples, functions, and well-definedness;
- known facts already stored in the environment;
- known `forall` facts by matching the shape of the goal and checking the
  required instantiations;
- definitions and predicate expansion;
- local assumptions from a proof block or `forall` statement.

`VerifyState` records control information for recursive verification. It helps
avoid unbounded loops and records whether particular checks, such as
well-definedness or certain equality routes, are already in progress or allowed
in the current recursive call.

Verification is the layer that decides whether a factual statement is `true`,
`unknown`, or an `error`.

### Inference

After a fact is accepted, Litex may infer routine consequences and store them
in the context. This is different from verification. Verification closes the
current goal. Inference records useful side information for future goals.

For example, after accepting a membership or equality fact, Litex may record
related facts that make later expressions easier to check. This is one reason
the context grows as a file runs.

### Output

Successful and failed statement results are collected as `StmtResult` values.
The output layer turns those results into user-facing JSON, display text,
LaTeX, and CLI output.

For most successful factual statements, the proof route is reported under
`verification`. A successful `forall` fact reports
`conclusions`, where each conclusion carries its own `verification` object.
Detail output additionally expands the local parameters and assumptions.

This output is part of the intended feedback loop. Users and agents should be
able to inspect whether a step was accepted by calculation, a known fact, a
known `forall`, local assumptions, or a composite chain of smaller checks.

## Why These Boundaries Matter

Several design boundaries are especially important:

- `src/parse/` and AST data structures are separate, so surface syntax does not
  become the proof model.
- `src/execute/` and `src/verify/` are separate, so changing the runtime state
  and proving a fact remain different responsibilities.
- `Runtime` owns the active run state, while `Environment` carries the
  mathematical context.
- imported runtimes share the same module manager, so imports have consistent
  cycle checks and source-state behavior.
- `VerifyState` makes recursive verification explicit instead of letting every
  rule call every other rule without control.

These boundaries do not make Litex a mature small-kernel proof assistant. They
do make it more than an unstructured script collection. The architecture is a
layered implementation of a specific interface idea: fact-oriented checking
with explainable context growth.

## Trust Boundary

Litex's current trust boundary is intentionally larger than a small proof
kernel. A checked result should be read relative to:

- the parser and AST interpretation;
- the execution model;
- builtin verification rules;
- builtin inference rules;
- standard-library facts and imports;
- any explicit `know` assumptions in the file;
- output rendering of the result trace.

This is a deliberate prototype-stage trade-off. Litex puts more ordinary
mathematical background into the checker so that user proofs can stay close to
paper mathematics. The cost is that builtin rules, inference rules, and
standard-library assumptions need careful review, tests, documentation, and
eventual audit.

So the accurate public description is:

> Litex is not a mature small-kernel system, but it is not an unstructured
> script collection either. It is a larger trusted implementation with clear
> layers around fact-oriented checking.

## Current Engineering Direction

The next architectural work is not to replace the whole design. The useful
work is to keep tightening the existing boundaries:

1. Reduce repeated interfaces between execution, verification, output, and
   runtime helpers.
2. Clean up naming drift in user-facing output and internal result structures.
3. Keep large files from becoming ownership bottlenecks by moving shared helper
   logic into focused modules.
4. Make builtin and infer rule behavior easier to audit with examples,
   regression tests, and compact documentation.
5. Use real translation work, such as MATH500, miniF2F, Mechanics, and
   textbook slices, to discover which architecture gaps matter in practice.

This is the same philosophy as the language itself: write the next concrete
mathematical or engineering fact, run the checker or tests, inspect the result,
and make the next smallest correction.
