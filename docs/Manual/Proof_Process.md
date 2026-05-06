# Proof Process

Try all snippets in browser: https://litexlang.com/doc/Manual/Proof_Process

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Proof_Process.md

A Litex proof is built from facts you claim one after another. After a fact is proved, it becomes known information for proving the next facts.

This page explains how one fact gets proved. The process is designed to stay close to ordinary mathematical thinking: first check that expressions make sense, then try direct mathematical rules, reuse known facts, and instantiate known universal facts when their shape matches the goal.

---

## The Core Loop

Most verification in Litex follows the same loop:

1. Check that the fact is well-defined.
2. Try builtin mathematical rules.
3. Try matching known facts.
4. Try matching known `forall` facts.

The exact details depend on the shape of the fact, but this loop is the main mental model.

### A builtin rule proves it

Some facts are closed directly by builtin mathematical rules.

```litex
2 + 3 = 5
```

Here Litex does not need a previous lemma. It evaluates the arithmetic expression and closes the equality by calculation. Other builtin rules handle ordinary mathematical background such as order, membership, set predicates, tuples, functions, and standard equality patterns. See [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules) for the detailed list.

### The same fact is already known

Some facts are true because the current context already contains the same fact.

```litex
abstract_prop ok(x)
know $ok(0)
$ok(0)
```

The last line is accepted because `$ok(0)` is already known in the proof context. This is the simplest form of reuse: a fact proved or introduced earlier can be used later.

### A known `forall` proves it

Known universal facts are also reusable. Litex can match the current goal against a known `forall` statement and substitute the right argument.

```litex
abstract_prop p(x)
know forall x R:
    $p(x)
$p(2)
```

The known fact says that every real number satisfies `$p`. When the goal is `$p(2)`, Litex matches `x` with `2` and checks the instantiated conclusion.

This match-and-substitution behavior is one of the main reasons Litex proofs can be written without manually naming every small intermediate fact.

---

## Atomic Fact Verification

An **atomic fact** is one indivisible mathematical claim, such as:

```text
2 + 3 = 5
2 < 3
1 $in {1, 2}
$is_set(R)
$p(2)
```

Atomic fact verification is where most proof obligations finally close.

### 1. Check Well-Definedness

Litex first checks that the objects in the fact make sense. The most common question is whether each function is applied inside its declared domain: if `f` is a function on `R`, then a fact about `f(a)` needs `a` to be usable as a real-number argument.

The same idea appears for set domains, tuple projections, indexed objects, and other object forms.

### 2. Try Builtin Rules

The main idea is pattern matching. If the fact uses a builtin predicate together with builtin objects, and the whole fact matches a pattern Litex knows, then that kind of fact can be closed automatically.

Typical examples:

```litex
2 + 3 = 5
```

This matches a numeric equality pattern: both sides can be calculated and compared.

```litex
1 $in {1, 2}
```

This matches a membership pattern: an element is checked against an enumerated set.

```litex
$is_finite_set({1, 2})
```

This matches a set predicate pattern: an enumerated set is recognized as a set object.

Builtin rules are not one mysterious tactic. They are many small mathematical patterns for equality, order, membership, sets, tuples, functions, arithmetic, and related standard objects.

### 3. Try Known Facts

If builtin rules do not close the goal, Litex checks known atomic facts with the same predicate and the same truth value. The arguments do not have to be written with exactly the same text: they may match through known equalities.

For example, suppose these facts are already known:

```text
$p(a, b)
a = a2
b = b2
```

Then this goal can be accepted from the known fact:

```text
$p(a2, b2)
```

Internally, Litex looks up known facts with predicate `$p`, then checks whether each goal argument is equal to the corresponding known argument.

```litex
abstract_prop p(x, y)
forall a, b, a2, b2 set:
    a = a2
    b = b2
    $p(a, b)
    =>:
        $p(a2, b2)
```

### 4. Try Known `forall` Facts

If direct known facts do not close the goal, Litex searches applicable universal facts. The rough process is:

1. Find known `forall` facts whose conclusion has the same predicate shape as the current goal.
2. Match the current goal's arguments against the `forall` conclusion and build a substitution for the universal parameters.
3. Substitute those parameters into the `forall` assumptions.
4. Check that the substituted assumptions are already known or can be verified.

Object matching is structural. If the `forall` conclusion has a parameter such as `x`, that parameter may bind to the object in the goal. If the conclusion has a structured object such as `f(x)`, `x + 1`, or `(x, y)`, Litex matches the outer shape first, then recursively matches the inner objects.

```text
know forall x R:
    $p(x)

goal:
    $p(2)

match:
    x -> 2
```

```text
know forall x R:
    $p(x + 1)

goal:
    $p(2 + 1)

match:
    x -> 2
```

```text
know forall x, y R:
    $p((x, y))

goal:
    $p((2, 3))

match:
    x -> 2, y -> 3
```

The substitutions are merged as matching goes deeper. If the same universal parameter appears twice, both appearances must match the same object:

```text
know forall x R:
    $p(x, x)

goal:
    $p(2, 2)

match:
    x -> 2
```

```text
know forall x R:
    $p(x, x)

goal:
    $p(2, 3)

match:
    fail

reason:
    x cannot be both 2 and 3
```

Litex also simplifies many common matching steps for you. If the `forall` conclusion has a parameter plus, minus, times, or divided by a number, and the goal gives a single object instead of the same written shape, Litex can move that number to the other side of the match.

```text
know forall x R:
    $p(x + 1)

goal:
    $p(y)

match:
    x -> y - 1
```

```text
know forall x R:
    $p(x * 2)

goal:
    $p(y)

match:
    x -> y / 2
```

The practical lesson is simple: the more similar your goal looks to a known fact or a known `forall` conclusion, the easier it is for Litex to verify it automatically. If the shapes are too different, you usually need to write intermediate facts that gradually rewrite the goal into a familiar shape.

`forall` is the foundation for proving facts beyond builtin rules. A known `forall` fact is like knowing infinitely many facts at once: once Litex finds objects that satisfy the parameter conditions, it can substitute those objects into the `forall` conclusion and obtain the corresponding concrete fact. Builtin rules give Litex a fixed base of mathematical reasoning; `forall` lets users keep generating new facts from their own definitions and theorems.

> The result of a factual statement is either **true** or **unknown**. `unknown` does not mean the statement is false. It means these verification routes did not find enough information. Usually the proof needs a smaller intermediate fact: an equality, a membership fact, a domain condition, a nonzero denominator, or a lemma that should be stated before the current line.

---

## Larger Facts

Larger factual statements do not introduce a completely separate proof engine. They organize smaller checks and eventually reduce to atomic facts or other smaller factual statements.

For a reference list of fact shapes, see [Factual Statements](https://litexlang.com/doc/Manual/Factual_Statements).

### Conjunction

```litex
1 = 1 and 2 < 3
```

A conjunction succeeds when each part succeeds. Each part is checked as its own fact.

### Chain

```litex
0 < 1 < 2
```

A chain is shorthand for adjacent comparisons or equalities. Litex checks the pieces and may record useful transitive consequences.

### Disjunction

```litex
1 = 2 or 1 = 1
```

Litex first checks that every branch is well-defined. Then it tries builtin rules for common exhaustive splits. If no builtin split applies, Litex checks the branches one by one. If any branch can be verified by the usual fact-verification process, the whole `or` fact is true.

If no branch is directly verified, Litex tries to match the whole `or` fact against known `or` facts, using known equal objects when comparing the arguments. Finally, it can also use known `forall` facts whose conclusion is an `or` fact.

```text
goal:
    1 = 2 or 1 = 1

reason:
    the second branch can be verified
```

```text
goal:
    x < 0 or 0 <= x

reason:
    builtin rule
```

```text
known:
    a = 0 or a > 0
    x = a

goal:
    x = 0 or x > 0

reason:
    the whole or fact matches the known or fact using x = a
```

```text
know forall x R:
    x < 0 or 0 <= x

goal:
    a < 0 or 0 <= a

match:
    x -> a
```

### Existential Facts

```litex
exist x R st { x = 1 }
```

Existential fact verification follows the same general routes. First, Litex checks that the parameter domains and body facts are well-defined. Then it tries to verify the existential fact by matching known information.

Builtin rules usually appear when Litex checks instantiated body facts:

```text
goal:
    exist x R st { x = 1 }

witness:
    x -> 1

body after substitution:
    1 = 1

reason:
    builtin rule
```

Known existential facts can be reused. Parameter names do not matter because Litex normalizes the body by renaming existential parameters:

```text
known:
    exist y R st { y = 1 }

goal:
    exist x R st { x = 1 }

reason:
    same normalized existential body
```

Known `forall` facts can also prove existential facts when their conclusion is an existential fact:

```text
know forall A Set:
    exist x A st { x $in A }

goal:
    exist x N st { x $in N }

match:
    A -> N
```

There is also a common user-facing path: the user can give a witness explicitly. Litex verifies that by substitution. It temporarily treats the existential parameter as equal to the witness object, runs the proof block, substitutes the witness into the body facts, and verifies those instantiated facts. Those body facts then reduce to the usual atomic fact, conjunction, chain, disjunction, or nested existential verification.

### Universal Facts

```litex
forall x R:
    x = x
```

A universal fact is checked in a local temporary context. Litex introduces the parameters, stores their domain facts as known facts, assumes the premise facts in that local context, and then verifies the conclusion facts there. Those conclusion facts again reduce to atomic facts or smaller factual statements.

```text
forall x R, y Z:
    $p(x, y)
    =>:
        $q(x, y)
```

For this example, Litex opens a local environment, declares `x $in R` and `y $in Z`, stores `$p(x, y)` as a known fact in that environment, and then verifies `$q(x, y)` inside the same environment.

Litex also has universal facts with `<=>:`. They are checked by reducing the equivalence to two ordinary `forall` facts:

```text
forall x R:
    $t(x)
    =>:
        $p(x)
    <=>:
        $q(x)
```

Litex verifies both directions:

```text
forall x R:
    $t(x)
    $p(x)
    =>:
        $q(x)
```

```text
forall x R:
    $t(x)
    $q(x)
    =>:
        $p(x)
```

So `forall` with `<=>:` is still the same local-environment process. Litex opens a temporary context, assumes one side, verifies the other side, then checks the reverse direction in another temporary context.

> Complex facts explain how to break the proof into sub-goals. Atomic facts are where most verification actually closes.

---

## Why The Builtin Layer Is Large

Litex includes many basic mathematical objects and rules because ordinary proofs use many small background facts. Numbers, sets, membership, functions, tuples, products, order, equality, finite displays, and positivity conditions constantly interact.

Each individual builtin rule is meant to be simple:

```litex
1 $in {1, 2}
2 + 3 = 5
0 <= 2
$is_set(R)
```

The size comes from combinations. A proof about a function may need arithmetic on its output, membership in its domain, tuple projections, set inclusion, and equality substitution. If every one of those steps had to be rebuilt as a user theorem, proofs would be dominated by bookkeeping.

The builtin layer is Litex's shared mathematical background. User-defined `prop`s and `forall` theorems add domain-specific ideas on top of that background, while the language handles the common low-level facts of basic mathematics.

---

## Read The Output Message

When Litex verifies a file, read the output message. It tells you how each fact was proved.

For example, a successful fact result may show:

```litex
let a, x R:
    a = 0 or a > 0
    x = a

x = 0 or x > 0
```

```text

{
  "result": "success",
  "type": "DefLetStmt",
  "line": 1,
  "stmt": "let a, x R:\n    a = 0 or a > 0\n    x = a",
  "infer_facts": [
    "a $in R",
    "x $in R",
    "a = 0 or a > 0",
    "x = a"
  ],
  "inside_results": []
}

{
  "result": "success",
  "type": "Fact",
  "line": 5,
  "stmt": "x = 0 or x > 0",
  "verified_by":   {
    "type": "known_fact",
    "line": 2,
    "source": "entry",
    "cited_fact": "a = 0 or a > 0"
  },
  "infer_facts": [],
  "inside_results": []
}
```

This means the goal `x = 0 or x > 0` was not proved by a fresh builtin calculation. It was proved by matching a known fact, namely `a = 0 or a > 0`. These messages are useful for learning Litex's proof process: they show whether a fact closed by builtin rules, by a known fact, by a known `forall`, or by another recorded verification route.