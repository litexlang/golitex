# Litex Tutorial: Introduction

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Try the examples in browser: https://litexlang.com/doc/Tutorial/Introduction

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Tutorial/Introduction.md

## What Litex Is

Litex is a language for writing math in a way that still looks like math, but can be checked line by line.

The fastest correct mental model is:

> In Litex, you write facts.  
> If a fact is checked successfully, it becomes part of the current context.  
> Later lines can use that context.

So Litex is not mainly about writing tactics. It is mainly about writing mathematical facts in a good order.

## The Three Things You Need First

You can understand a lot of Litex with only these three ideas.

### 1. Objects

Objects are the things you talk about: numbers, sets, functions, tuples, and named variables.

Examples:

- `2`
- `x`
- `{1, 2, 3}`
- `f(2)`

By themselves, these are just objects, not claims.

### 2. Facts

Facts are claims about objects.

Examples:

- `1 + 1 = 2`
- `x $in R`
- `A $subset B`
- `f(2) = 3`

These are the lines Litex tries to verify.

### 3. Context

When a fact succeeds, Litex remembers it.

That means later lines do not start from nothing. They start from the verified facts already stored in the context.

This is why the order of lines matters.

## The Smallest Useful Example

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

Read it like this:

1. Introduce a real number `x` and fix it to `2`.
2. Since Litex now knows `x = 2`, it can verify `x + 1 = 3`.
3. It can also verify `x^2 = 4`.

That is already a large part of the user experience.

## `have`, `know`, and bare facts

These are the first three surface forms most people need.

### `have`

Use `have` to introduce an object or definition into the context.

Example:

```litex
have a R = 5
```

Now Litex knows `a` is a real number and `a = 5`.

### `know`

Use `know` to store a fact directly in the context.

Example:

```litex
know 2 < 3
```

Now later lines can reuse `2 < 3`.

### Bare fact line

If you just write a fact by itself, Litex tries to prove it from the current context.

Example:

```litex
have a R = 5
a + 1 = 6
```

The second line is not a definition. It is a claim Litex must verify.

## `forall` Means a Reusable General Fact

One of the most important ideas in Litex is that a known `forall` fact can be reused later by instantiating it.

Example:

```litex
know forall x R:
    x = 2
    =>:
        x + 1 = 3

have a R = 2
a + 1 = 3
```

What happens:

1. Litex stores the general statement.
2. Later it sees `a = 2`.
3. It matches the general fact with `a`.
4. It verifies `a + 1 = 3`.

This is one of the main reasons Litex works well for textbook-style proofs.

## Starting From An Abstract Structure

Litex can also start from an abstract mathematical interface. A file can name
the domains and relations it wants to study, store axioms about them, and then
check later facts against that context.

The complete example to read first is
[Hilbert Axioms of Euclidean Geometry](https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry).
It introduces points, lines, planes, incidence, betweenness, and congruence
relations directly, in the style of Hilbert-style geometry, instead of starting
from coordinates.

## Blocks Mean “Assume This, Then Prove That”

This is the most common proof shape:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
        x^2 = 4
```

Read it as:

- for every real `x`,
- if `x = 2`,
- then prove the following lines.

The important point is that the lines under `=>:` are checked inside the local context created by the assumption `x = 2`.

## Why Litex Often Feels Short

Litex is short because it tries to do routine math automatically.

For example, if Litex already knows:

- `x = 2`

then it may be able to verify:

- `x + 1 = 3`
- `x^2 = 4`
- `x - 2 = 0`

without asking you to manually describe every algebra step.

This is not “magic”; it is the checker using builtin rules, known facts, and normalization.

## What Success, Unknown, and Error Mean

When a line is processed, you should think in three possible outcomes.

### Success

Litex found a proof path.

Typical reasons:

- builtin arithmetic
- a previously known fact
- a previously known `forall`

### Unknown

The line is meaningful, but Litex does not know enough to prove it yet.

This usually means:

- you need one more lemma,
- one more assumption,
- or a better proof structure.

### Error

The line is not well-defined or not valid syntax.

Typical reasons:

- undeclared identifier
- division by zero
- malformed statement
- wrong object shape for the statement

This distinction is important: `unknown` is a proof gap, while `error` is a malformed step.

## How To Start Writing Litex

A good beginner workflow is:

1. Introduce objects with `have`.
2. State known assumptions with `know`.
3. Write the next fact you want.
4. If it fails, make the missing step explicit.
5. Turn repeated patterns into a `forall`.

If you do only that, you can already write a surprising amount of Litex.

## What To Read Next

After this file, go to:

- Mechanics of Litex Proof: https://litexlang.com/doc/The_Mechanics_of_Litex_Proof/Introduction
- Manual: https://litexlang.com/doc/Manual

If you remember only one sentence from this page, remember this:

> Litex is a language where you write mathematical facts in a good order, and the checker grows a verified context for you.
