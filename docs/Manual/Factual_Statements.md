# Factual Statements

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Manual/Factual_Statements

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Factual_Statements.md

_I think, therefore I am._

_— René Descartes_

A **factual statement** is a Litex statement that claims a mathematical fact. It may be as small as `1 = 1`, or as structured as a `forall`, `exist`, `or`, or chain of inequalities.

The result of checking a factual statement is either **true** or **unknown**.

- **true** means Litex has verified the fact from the current context, definitions, and builtin rules.
- **unknown** means Litex does not have enough verified information to close the goal. The fact may be false, or it may simply need more intermediate facts.

Once a factual statement is verified, it becomes a **known fact** in the current context and can be reused by later statements.

> Hint: `unknown` is usually a request for a smaller step. Try stating the missing equality, membership, domain condition, or previous lemma explicitly.

This page is about **facts themselves**. For the larger list of Litex statement forms such as `prop`, `have`, `claim`, `prove`, `know`, and `witness`, see [Builtin statements](https://litexlang.com/doc/Manual/Statements).

This page mainly lists the **types of facts** Litex can read and how they are shaped. For how those facts are actually proved by the checker, read [Proof Process](https://litexlang.com/doc/Manual/Proof_Process) and [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules).

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

---

## Atomic facts

An **atomic fact** is one indivisible mathematical claim. It is made from a **predicate** and its **arguments**. The predicate is the judgment being made; the arguments are the objects being judged. Some predicates are built into Litex because they correspond to basic mathematical ideas, such as equality `=`, order `>`, membership `$in`, subset `$subset`, and set predicates like `$is_set`.

If [Objects](https://litexlang.com/doc/Manual/Objects) are the mathematical things you talk about, predicates are the basic ways to make judgments about them. In ordinary mathematical language, they are the verbs of small facts:

```text
1 + 1       // an object
1 + 1 = 2   // a fact
2           // an object
2 $in N     // a fact
```

Common atomic facts:

```litex
1 + 1 = 2
```

Here `=` is the main relation(predicate), and `1 + 1` and `2` are the arguments. This factual statement is true by calculation.

> Note: In Litex, expressions such as `1 + 1`, `x - y`, or `f(x)` are usually treated as **objects** or **terms**. They name values. They are not facts by themselves, so they are not true or false.

> Note: The **verb** of a factual statement is the part that makes a judgment: `=`, `!=`, `<`, `$in`, `$is_set(...)`, or a custom predicate such as `$is_one(...)`. For example, `1 + 1` has no truth value, but `1 + 1 = 2` does.

> Hint: When reading an atomic fact, first find the verb that is being checked. The remaining pieces are the objects the verb talks about.

More examples with builtin predicates:

```litex
2 != 3
0 < 1
not 1 < 0
1 $in {1, 2}
$is_set({1, 2})
```

> Note: Builtin predicates and builtin objects are connected by many builtin verification rules. These predicates and rules are the common concepts and rules from basic mathematics, not advanced hidden machinery. Each single rule is usually intuitive: for example, `1 $in {1, 2}`, `2 < 3`, `2 != 3`, or `$is_set({1, 2})`. The surprising part is the total size of the background knowledge. Basic mathematics has many small relationships, and Litex has hundreds of them built in for standard numbers, sets, functions, tuples, comparisons, equality, and membership.

> Note: Because of this, using builtin predicates and builtin objects is often much more convenient than rebuilding the same ideas with custom predicates. When you write facts with standard forms such as `$in`, `$is_set`, `=`, `<`, `R`, `Z`, or `{1, 2}`, Litex can often use hundreds of built-in relationships behind the scenes.

> Hint: Prefer builtin predicates and builtin objects when they express what you mean. Use custom `prop` definitions when you need a new mathematical idea that is not already covered by the builtin vocabulary.

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

When several comparisons belong to the same ordered path, prefer a chain such as `a < b < c` instead of writing separate facts such as `a < b` and `b < c`. The chain is shorter, shows the structure more clearly, and gives Litex a direct shape for applying builtin order support.

> Hint: If a chain is hard to debug, split it into its adjacent pieces first.

> Hint: Try to use `<` consistently instead of switching back and forth between `<` and `>`. For example, prefer `a < b < c` over `c > b > a` when either form would say the same thing. A consistent direction makes proof steps easier to read and easier for builtin order rules to match.

---

## Disjunctions

A **disjunction** says that at least one branch holds.

```litex
1 = 2 or 1 = 1
```

Litex can verify this because the second branch is true.

A branch is usually an atomic fact, a conjunction of atomic facts, or a chain.

> Hint: To prove `A or B`, it is enough for Litex to prove one side.

Disjunctions also work together with the `by cases` statement. After Litex knows `A or B`, `by cases` can split the proof into one branch where `A` is assumed and another branch where `B` is assumed.

```litex
have x R

by cases:
    prove:
        x = 0 or x != 0
    case x = 0:
        ...
    case x != 0:
        ...
```

> Hint: Think of `or` as the factual statement shape, and `by cases` as the proof statement that uses that shape.

---

## Existential facts

An **existential fact** says that there is a witness satisfying some conditions.

```text
exist x R st { x = 1 }
```

Read this as: there exists an `x` in `R` such that `x = 1`.

You can also state uniqueness:

```text
exist! x R st { x = 0 }
```

And non-existence:

```text
not exist x R st { x != x }
```

The body after `st` is the list of facts the witness must satisfy.

> Hint: To prove an `exist` goal, Litex usually needs a concrete witness. In proof code, use `witness` when you want to tell Litex which object should be used as the witness.

> Hint: To use an already known `exist` fact, use `have by exist` to give names to the witnesses and bring their body facts into the current context.

Example:

```litex
know exist u R st { u = 1 }

have by exist v R st { v = 1 }: h
h = 1
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
forall! x R => {x = x}
forall! x R: x > 0 => {x != 0}
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

```text
not forall x R:
    x > 0
```

Read this as: it is not true that every real number is greater than `0`.

> Hint: `not forall` is different from putting `not` inside the conclusion. If you want to say there is a counterexample to a universal claim, use `not forall`.

