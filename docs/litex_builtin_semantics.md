# Litex Builtin Semantics

Litex builtins are not a loose collection of shortcuts. They form the language's built-in semantic layer.

This layer has three responsibilities:

1. It decides which mathematical objects are basic enough to be part of the language.
2. It records the default relationships between those basic objects.
3. It gives the verifier a small set of automatic proof mechanisms.

Each concept is usually simple, and each relationship between concepts is also usually simple. The complexity comes from scale: sets, functions, equality, membership, sequences, matrices, order, and integer ranges interact in many combinations. Litex builds these common relationships into the language so users can focus on the mathematical statement they actually want to prove.

This document is the high-level map. Detailed builtin verification rules should live in separate rule-oriented documents.

## 1. Builtin Concepts

Builtin concepts are objects, facts, statements, or keywords that Litex treats as primitive enough to be understood by the parser, runtime, and verifier.

They are not user-defined `prop`s. They are part of the core mathematical vocabulary of the language.

### 1.1 Sets and Standard Sets

| name | category | meaning |
|---|---|---|
| `set` | parameter type | an arbitrary set |
| `nonempty_set` | parameter type | a nonempty set |
| `finite_set` | parameter type | a finite set |
| `N` | standard set | natural numbers, including `0` |
| `N_pos` | standard set | positive natural numbers |
| `Z` | standard set | integers |
| `Q` | standard set | rational numbers |
| `R` | standard set | real numbers |
| `R_pos` / `R_neg` / `R_nz` | standard set | positive, negative, and nonzero real numbers |

These sets are not only names. They carry basic semantic information. For example, `n N` means `n` is a natural number, and `x R_pos` means `x` is a positive real number.

### 1.2 Function Spaces

`fn` is the builtin object constructor for function spaces.

```text
fn(x S: P(x)) T
```

This describes functions whose input `x` belongs to `S`, whose optional domain condition `P(x)` holds, and whose output belongs to `T`.

This concept connects:

1. parameter sets
2. domain conditions
3. return sets
4. function-object membership
5. well-definedness of function application

Example:

```text
f $in fn(x R: x > 0) R
```

This means that `f` is a function object that accepts positive real inputs and returns real outputs.

### 1.3 Sequence and Matrix Concepts

`seq`, `finite_seq`, and `matrix` are common mathematical objects. In Litex, they are connected to function spaces.

```text
seq(s) = fn(x N_pos) s

finite_seq(s, n) = fn(x N_pos: x <= n) s

matrix(s, m, n) = fn(x, y N_pos: x <= m, y <= n) s
```

These relationships say:

1. A sequence is a function from positive natural numbers to `s`.
2. A finite sequence of length `n` is a function whose domain is restricted by `x <= n`.
3. An `m` by `n` matrix is a function from two positive-natural coordinates to `s`.

Because of this bridge, these objects do not need separate `by seq`, `by finite_seq`, or `by matrix` proof statements.

### 1.4 Logical Concepts

| name | category | meaning |
|---|---|---|
| `forall` | logical fact constructor | relates parameters, domain facts, and conclusion facts |
| `forall!` | inline forall | compact form of `forall` for local or shorthand syntax |
| `exist` | logical fact constructor | introduces witnesses that make body facts true |
| `exist!` | logical fact constructor | unique existence |
| `prop` | user-defined concept | defines a new predicate from existing concepts |
| `abstract_prop` | abstract concept | declares only the predicate name and parameters |

`forall` and `prop` are the main ways users extend the language. Builtin concepts are provided by Litex; user-defined concepts are connected back into the same proof system through `prop` and `forall`.

## 2. Builtin Semantic Bridges

Builtin semantic bridges are built-in relationships between basic concepts. They answer: how does one concept constrain, translate to, or imply another?

This section should describe the role of each bridge, not enumerate every verification rule that currently implements it.

### 2.1 Membership: Object and Set

```text
x $in S
```

`$in` connects an object with a set.

Many pieces of mathematical type information are memberships. For example:

```text
x R
```

can be read as:

```text
x $in R
```

Different set shapes carry different semantic information, such as standard-number membership, interval bounds, finite-set alternatives, and function-space typing.

### 2.2 Equality: Object and Object

```text
a = b
```

`=` connects two objects and states that they are the same.

In Litex, equality plays several roles:

1. ordinary mathematical equality
2. the target of calculation
3. known-fact matching
4. algebraic rewriting and structural comparison
5. object and function definition results

### 2.3 Function Equality

`$fn_eq` and `$fn_eq_in` are semantic bridges for function equality.

```text
$fn_eq_in(f, g, S)
```

This states that `f` and `g` are pointwise equal on `S`.

```text
$fn_eq(f, g)
```

This states that two functions are equal on their shared domain, while the verifier also checks their function-space information.

These bridges exist so users do not need to write the full pointwise `forall` every time.

### 2.4 Implication and Equivalence

```text
A => B
```

This connects assumptions to conclusions.

```text
A <=> B
```

This gives a relationship that can be used in both directions.

Inside a `forall`, `=>` separates domain facts from conclusion facts:

```text
forall x R:
    x > 0
    =>:
        x * x > 0
```

This says: for every real `x`, if `x > 0`, then `x * x > 0`.

## 3. Builtin Verification Mechanisms

Builtin verification mechanisms are automatic proof procedures used by the verifier. They are not new mathematical objects. They are ways to prove facts about the existing objects and relations.

### 3.1 Calculation

Calculation handles equalities between computable expressions.

```text
1 + 2 = 3
```

The user does not need to provide a proof script for this kind of fact. Litex can evaluate both sides and compare the results.

### 3.2 Known Fact Matching

If a fact has already been stored, a later identical fact can be verified from it.

```text
know a = b

a = b
```

The second line can be verified by the known fact.

### 3.3 Forall Instantiation

A known `forall` can prove an instance.

```text
know forall x R:
    x = x

1 = 1
```

The core mechanism is matching and substitution:

1. Match the target fact against the conclusion facts of the `forall`.
2. Solve which objects should replace the forall parameters.
3. Check parameter sets and domain facts.
4. Produce the target fact.

### 3.4 Algebraic and Order Verification

The verifier has builtin procedures for common algebraic and order reasoning over arithmetic expressions.

This category connects arithmetic symbols with equality and order symbols:

```text
+ - * / % abs max min < <= > >= =
```

The detailed list of rules in this category should be maintained outside this overview document.

### 3.5 Number and Set Membership

Litex can directly verify membership facts for literal numbers, standard sets, intervals, finite sets, and other built-in set shapes.

Example:

```text
1 $in N_pos
0 $in N
-1 $in Z
```

This category also includes closure behavior for standard number sets. The rule inventory belongs in a dedicated rule document.

### 3.6 Function Membership

When Litex knows:

```text
f $in fn(x S: P(x)) T
```

it records function-space information. Later, function application can use this information to check:

1. whether the input belongs to `S`
2. whether the domain condition `P(x)` holds
3. whether the returned object belongs to `T`

### 3.7 Set Membership Expansion

Some membership facts expand into simpler facts.

For example, membership in a finite listed set can produce alternatives, and membership in an integer range can produce integer membership plus bounds.

### 3.8 Structural Evaluation

Litex has builtin evaluation rules for structural objects such as lists, tuples, finite sequences, and matrices.

These rules connect structural syntax with elementwise computation.

## 4. Documentation Structure

This file should remain a conceptual map. It should answer:

1. What kinds of things are builtin?
2. Why are they builtin?
3. Which broad semantic category do they belong to?

Detailed rule catalogs should live in separate files. A useful split is:

1. `docs/litex_builtin_rule_notes.md` for current builtin verification rules.
2. `docs/builtin_verify_rules.md` for a future complete verifier-rule reference.
3. `docs/builtin_inference_rules.md` for inference rules.

## 5. First Batch To Document

The first batch should focus on the core semantic vocabulary:

1. `set`, `nonempty_set`, `finite_set`
2. `N`, `N_pos`, `Z`, `Q`, `R`, `R_pos`, `R_nz`
3. `$in`
4. `=`
5. `<`, `<=`, `>`, `>=`
6. `fn`
7. `$fn_eq`, `$fn_eq_in`
8. `seq`, `finite_seq`, `matrix`
9. `range`, `closed_range`
10. `forall`, `exist`, `prop`

After this structure is stable, detailed verification and inference rules can be moved into their own dedicated references.
