# Factual Statements

Try all snippets in browser: https://litexlang.com/doc/Manual/Factual_Statements

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Factual_Statements.md

A **factual statement** is a Litex statement that claims a mathematical fact. It may be as small as `1 = 1`, or as structured as a `forall`, `exist`, `or`, or chain of inequalities.

The result of checking a factual statement is either **true** or **unknown**.

- **true** means Litex has verified the fact from the current context, definitions, and builtin rules.
- **unknown** means Litex does not have enough verified information to close the goal. The fact may be false, or it may simply need more intermediate facts.

Once a factual statement is verified, it becomes a **known fact** in the current context and can be reused by later statements.

> Hint: `unknown` is usually a request for a smaller step. Try stating the missing equality, membership, domain condition, or previous lemma explicitly.

This page is about **facts themselves**. For the larger list of Litex statement forms such as `prop`, `have`, `claim`, `prove`, `know`, and `witness`, see [Builtin statements](https://litexlang.com/doc/Manual/Statements).

---

## Quick mental model

Think of Litex as checking one sentence at a time:

```litex
1 + 1 = 2
```

Litex asks:

1. Are the terms well-defined?
2. What shape is this fact?
3. Can the fact be proved from what is already known?
4. If the fact is compound, can its smaller parts be checked?

For example:

```litex
have x R = 2
x + 1 = 3
```

The second line works because `x` is already known to be `2`, so the equality can be reduced to a numeric equality.

---

## Shapes of facts

Different fact shapes are verified in different ways, but they all reduce to the same idea: Litex must justify the claim from the current context.

| Shape | Meaning | Example |
|-------|---------|---------|
| **Atomic fact** | One basic claim: equality, order, membership, or one predicate call. | `1 = 1`, `2 < 3`, `1 $in {1, 2}`, `$is_set(R)` |
| **Atomic negation** | Negation of one atomic claim. | `2 != 3`, `not 1 < 0` |
| **Conjunction** | Several atomic facts all hold. | `1 = 1 and 2 < 3` |
| **Chain** | Shorthand for adjacent comparisons. | `0 < 1 < 2` |
| **Disjunction** | At least one branch holds. | `1 = 2 or 1 = 1` |
| **Existential fact** | **Inline witness form**: `exist`, `exist!`, or `not exist`, followed by `st { ... }`. | `exist x R st { x = 1 }` |
| **Universal fact** | For all typed variables, conclusions hold. | `forall! x R: x = x`, or block `forall x R:` |
| **Universal with equivalence** | A universal fact with an equivalent reformulation. | block `forall ...` with `<=>:` |
| **Negated universal** | A universal claim is false. | `not forall x R: x > 0` |

> Hint: If you are new to Litex, start by writing one simple fact per line. Use compound forms only when they make the proof easier to read.

Some fact shapes have both **inline** and **multiline** forms. Inline forms are convenient for short facts; multiline forms are easier when the body has several facts or when you need `=>:` / `<=>:`.

Existential facts are usually inline. The keyword tells you which kind of existence is being claimed:

```litex
exist x R st { x = 1 }
exist! x R st { x = 0 }
not exist x R st { x != x }
```

When the body has several requirements, keep them inside the braces:

```litex
exist x R st { x > 0, x < 1 }
```

Universal facts can be inline with `forall!`:

```litex
forall! x R: x = x
forall! x R: 0 < x => { x != 0 }
```

The multiline form uses ordinary `forall`:

```litex
forall x R:
    x = x

forall x R:
    0 < x
    =>:
        x != 0
```

Universal facts with equivalence are normally written in multiline form:

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

> Hint: Use inline syntax only when the whole fact is easy to read on one line. If the fact has multiple assumptions, multiple conclusions, or `<=>:`, use multiline syntax.

---

## Atomic facts

An **atomic fact** is one indivisible mathematical claim. It has one main relation or predicate, plus its arguments.

Common atomic facts:

```litex
1 = 1
2 != 3
0 < 1
not 1 < 0
1 $in {1, 2}
$is_set({1, 2})
```

Custom predicates defined by `prop` are also atomic when you call them:

```litex
prop is_one(x R):
    x = 1

$is_one(1)
```

The call `$is_one(1)` is atomic. Litex can unfold the `prop` definition and check that `1 = 1`.

> Hint: A predicate definition is written with `prop is_one(...)`, but a predicate fact is called with `$is_one(...)`.

Atomic facts are usually checked by:

- direct computation, such as `2 + 3 = 5`;
- known definitions, such as a `prop` body or a `have fn` equation;
- already known facts in the current context;
- builtin verification rules for equality, order, membership, sets, tuples, numbers, and similar standard objects.

> Hint: Before Litex proves an atomic fact, it must also know that the expressions make sense. For example, using a variable usually requires that the variable has already been introduced with a type such as `have x R`.

---

## Conjunctions

A **conjunction** says that several atomic facts all hold.

```litex
1 = 1 and 2 < 3
```

This means the same thing as writing the two facts separately:

```litex
1 = 1
2 < 3
```

Litex style usually prefers the second form. It is easier to read, and when something becomes `unknown`, the failing line is clearer.

> Hint: Use `and` inside compact bodies such as `exist x R st { ... }` only when it improves readability. In ordinary proof blocks, one fact per line is usually better.

---

## Chains

A **chain** is a compact way to write adjacent binary relations.

```litex
0 < 1 < 2
```

Logically, this means:

```litex
0 < 1 and 1 < 2
```

Chains are not a new kind of mathematical logic. They are shorthand for smaller atomic comparisons, and Litex may also use order facts to derive convenient consequences.

```litex
0 < 1 < 2
0 < 2
```

> Hint: If a chain is hard to debug, split it into its adjacent pieces first.

---

## Disjunctions

A **disjunction** says that at least one branch holds.

```litex
1 = 2 or 1 = 1
```

Litex can verify this because the second branch is true.

A branch is usually an atomic fact, a conjunction of atomic facts, or a chain.

> Hint: To prove `A or B`, it is enough for Litex to prove one side. If both sides are `unknown`, state more facts before the disjunction or prove one branch inside a `claim:`.

---

## Existential facts

An **existential fact** says that there is a witness satisfying some conditions.

```litex
exist x R st { x = 1 }
```

Read this as: there exists an `x` in `R` such that `x = 1`.

You can also state uniqueness:

```litex
exist! x R st { x = 0 }
```

And non-existence:

```litex
not exist x R st { x != x }
```

The body after `st` is the list of facts the witness must satisfy.

> Hint: To prove an `exist` goal, Litex usually needs a concrete witness. In proof code, use `witness` when you want to tell Litex which object should be used as the witness.

> Hint: To use an already known `exist` fact, use `have by exist` to give names to the witnesses and bring their body facts into the current context.

Example:

```litex
know exist u R st { u = 1 }

have by exist v R st { v = 1 }: h
v = 1
```

---

## Universal facts

A **universal fact** says that something holds for every object of a given type.

```litex
forall x R:
    x = x
```

Read this as: for every `x` in `R`, `x = x`.

A universal fact can also have assumptions before `=>:`:

```litex
forall x R:
    0 < x
    =>:
        x != 0
```

Read this as: for every `x` in `R`, if `0 < x`, then `x != 0`.

The lines before `=>:` are the **domain assumptions** or **hypotheses**. The lines under `=>:` are the **conclusions**.

> Hint: Without assumptions, put conclusions directly under `forall`. With assumptions, put the assumptions first, then `=>:`, then indent the conclusions one more level.

Compact `forall!` syntax is also available for short facts:

```litex
forall! x R: x = x
```

For beginners, block form is often clearer.

---

## Universal facts with equivalence

Sometimes a universal statement says that two descriptions are equivalent. Litex writes this with `<=>:`.

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

Read this as: under the same variables and assumptions, `x > y` is equivalent to `y < x`.

> Hint: Use `<=>:` when both directions are intended. If you only need one direction, use an ordinary `forall` with `=>:`.

---

## Negated universal facts

A **negated universal** says that a universal claim is not true.

```litex
not forall x R:
    x > 0
```

Read this as: it is not true that every real number is greater than `0`.

This usually corresponds to a counterexample.

```litex
not forall x R:
    x != x
```

> Hint: `not forall` is different from putting `not` inside the conclusion. If you want to say there is a counterexample to a universal claim, use `not forall`.

---

## How Litex verifies a fact

The exact builtin rules are listed in [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules), but the basic flow is simple:

1. **Check well-definedness.** Litex first checks that the names, terms, sets, function calls, and predicate calls make sense in the current context.
2. **Recognize the fact shape.** Atomic, `and`, chain, `or`, `exist`, `forall`, and `not forall` are handled differently.
3. **Break compound facts into smaller goals.** For example, `A and B` requires both `A` and `B`; a chain becomes adjacent atomic comparisons.
4. **Use the current context.** Litex uses facts already proved, facts introduced by `know`, function definitions, `prop` definitions, and facts inferred from earlier statements.
5. **Try builtin rules.** Arithmetic, equality normalization, order comparison, membership, set facts, tuple facts, and other standard rules may close the goal.
6. **Return true or unknown.** If all required pieces are verified, the whole fact is true. Otherwise it is unknown.

> Hint: Do not read `unknown` as a final mathematical judgment. Read it as: "Litex cannot see the proof from here."

---

## Writing proof-friendly facts

Prefer small, explicit steps:

```litex
have x R = 2
x = 2
x + 1 = 3
```

State domain facts before using rules that need them:

```litex
have x R
know x > 0
x != 0
```

Use `claim:` when you want to prove a fact in a small local block:

```litex
claim:
    1 + 1 = 2
```

Use `know` for facts you want to add as assumptions or already accepted background knowledge:

```litex
know forall x R:
    x = x
```

> Hint: A good Litex proof often looks more detailed than a paper proof. That is normal: you are writing down the steps that a human reader might silently fill in.

---

## Common beginner mistakes

Writing a fact before introducing its variables:

```litex
# x has not been introduced yet
x = x
```

Introduce the variable first:

```litex
have x R
x = x
```

Using `=>:` when there are no assumptions:

```litex
# Prefer the simpler form
forall x R:
    =>:
        x = x
```

Write:

```litex
forall x R:
    x = x
```

Expecting a disjunction to prove both branches:

```litex
1 = 1 or 1 = 2
```

This proves only that at least one branch holds. It does not make `1 = 2` known.

> Hint: When in doubt, ask: "What exact fact do I want to be available on the next line?" Then write that fact directly if possible.
