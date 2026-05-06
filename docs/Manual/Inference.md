# Inference

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Manual/Inference

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Inference.md

_The more I think about language, the more it amazes me that people ever understand each other at all._

_- Kurt Gödel_

Verification answers the question: **can this fact be proved now?**

Inference happens after that. Once a fact is verified or introduced by `know`, Litex stores it in the current environment and may derive more facts from it. Those derived facts become ordinary known information for later proof steps.

The main purpose is usability. Inference saves the user from manually writing the obvious next facts again and again.

This is different from [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules). Verification rules close the current goal. Inference adds useful consequences after a fact has already been accepted. For the full loop from verification to storage and inference, see [Proof Process](https://litexlang.com/doc/Manual/Proof_Process).

---

## The Mental Model

Think of inference as automatic bookkeeping.

If you tell Litex:

```text
x $in N_pos
```

Litex remembers not only that membership fact, but also useful consequences such as:

```text
0 < x
```

If you tell Litex:

```text
A $subset B
```

Litex can remember the universal membership consequence:

```text
forall x A:
    x $in B
```

The point is not to replace proof. The point is to keep basic mathematical consequences available so later facts can match known information more naturally.

---

## Which Facts Trigger Inference

Most inference rules are triggered by **atomic facts**: equalities, memberships, comparisons, predicates, subset facts, and similar small claims.

Some larger fact shapes have special inference behavior:

- `exist!` adds a uniqueness statement: any two witnesses satisfying the body must agree.
- `not exist` adds the usual universal De Morgan form.
- `not forall` adds an existential counterexample.
- equality chains add the equalities forced by transitivity, and those equalities then infer as usual.

Some larger facts do **not** trigger this extra pass by themselves:

- `and`
- `or`
- outermost `forall`, including `forall` with `<=>:`

Their atomic pieces may still trigger inference when those pieces are assumed, proved, or stored separately.

---

## Equality Inference

Equality inference is mainly about remembering equivalent forms and structural information.

### Difference Equals Zero

If one side is `0` and the other side is a difference `u - v`, inference adds `u = v`.

```text
known:
    a - b = 0

inferred:
    a = b
```

### Concrete Numeric Values

If one side simplifies to a concrete number, Litex treats the other side as known to equal that number for substitution and numeric reasoning.

```text
known:
    x = 2

later goal:
    x + 1 = 3

reason:
    x can be resolved to 2
```

This may not always appear as a separate displayed `infer_facts` line. Sometimes it is stored as side information used later by resolution.

### Simple Linear Equations

If an equality has a simple linear form and one side is a concrete number, inference may treat the main unknown as fixed to that number, in the same way as the numeric-value case.

```text
known:
    x + 1 = 3

remembered:
    x is fixed to 2
```

### Tuples And Cartesian Products

If one side is a tuple and the other side is not, Litex remembers tuple information about the other object.

```text
known:
    t = (a, b)

inferred:
    $is_tuple(t)
```

If one side is a literal Cartesian product such as `cart(R, Q)`, Litex remembers that the other object is a Cartesian product, along with its number of factors and related metadata.

```text
known:
    d = cart(R, Q)

inferred:
    $is_cart(d)
```

### Displayed Sequences, Matrices, And Functions

If one side is a finite sequence literal or a matrix literal and the other side is a name, Litex remembers that the name has that sequence or matrix shape.

If one side is an anonymous function and the other side is a name, Litex remembers the function argument list and, when present, the defining equation.

These rules are mostly bookkeeping rules. They help later object checks and equality checks avoid repeating shape information.

### Predicate Definitions

For a user-defined `prop` with `<=>:` clauses, once `$P(args)` is known, inference instantiates the corresponding definition facts by plugging in those arguments.

```text
prop unit_x(x R):
    forall x R:
        =>:
            x = 1
        <=>:
            x + 0 = 1

known:
    $unit_x(a)

available through inference:
    a + 0 = 1
```

What gets inferred depends on how the predicate is defined.

---

## Membership Inference

Membership facts are one of the most common sources of inferred information.

### Number Sets

Membership in more specific number sets gives sign or nonzero information.

```text
known:
    k $in N

inferred:
    0 <= k
```

```text
known:
    x $in R_pos

inferred:
    0 < x
```

```text
known:
    x $in R_neg

inferred:
    x < 0
```

```text
known:
    x $in R_nz

inferred:
    x != 0
```

Plain membership in `Z`, `Q`, or `R` alone does not add a sign fact.

### Finite Enumerations

Membership in an enumerated finite set becomes a finite disjunction.

```text
known:
    a $in {1, 2}

inferred:
    a = 1 or a = 2
```

### Products And Tuples

Membership in `cart(...)` adds tuple information and aligns product-set bookkeeping.

```text
known:
    u $in cart(R, R)

inferred:
    $is_tuple(u)
```

### Ranges

Membership in a half-open integer range gives integer membership and two-sided bounds.

```text
known:
    i $in range(2, 6)

inferred:
    i $in Z
    2 <= i
    i < 6
```

Membership in a closed range gives closed bounds.

```text
known:
    i $in closed_range(1, 3)

inferred:
    i $in Z
    1 <= i
    i <= 3
```

### Set Comprehensions

Membership in a set comprehension adds membership in the base set and each filter condition with the bound variable replaced by the element.

```text
known:
    x $in { y R: 0 <= y }

inferred:
    x $in R
    0 <= x
```

### Function-Like Sets And Families

Membership in `fn(...)` records function-space information for suitable function heads, so later goals can use the expected domain and codomain.

Membership in `finite_seq(...)`, `seq(...)`, and `matrix(...)` is handled similarly because these objects are read as function-like types.

For membership in a `family` instance such as `\name(...)`, Litex expands the family to the set it denotes, then applies the usual membership inference rules to that expanded set.

---

## Subset And Superset

From `A $subset B`, Litex infers that every element of `A` is also in `B`.

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

From `A $superset B`, Litex infers that every element of `B` is also in `A`.

```litex
prove:
    let A, B set:
        A $superset B
    forall x B:
        x $in A
```

Inside a `forall ... =>:` block, the conclusion cannot be another raw `forall`. In examples like these, use `let` to store the subset or superset fact, then write the inferred universal membership fact separately.

---

## Order Inference

Order inference mainly turns a comparison with a concrete constant into a simpler sign fact.

If exactly one side of an inequality is a numeric constant, Litex may compare the other side with `0`.

```text
known:
    2 <= a

inferred:
    0 < a
```

```text
known:
    -1 >= b

inferred:
    b <= 0
```

When the right-hand side is `0` and the left-hand side is not already `(-1) * u`, Litex may flip the inequality into a statement about `-1` times the left-hand side.

```text
known:
    x < 0

inferred:
    -1 * x >= 0
```

There is no matching automatic rule when `0` is on the left.

---

## Function Restriction

For `$restrict_fn_in`, inference narrows the recorded function-space information to the more specific function type you gave. It does not need to restate the whole function definition.

```text
known:
    $restrict_fn_in(f, smaller_fn_type)

remembered:
    f can be used with the smaller function type
```

---

## Facts With No Extra Inference

Some builtin atoms are left as they are for this pass. Examples include negated comparisons, `$is_set`, `not $restrict_fn_in`, and similar facts.

They can still be used in proofs. Inference simply does not unfold them further here.

---

## Read The Output Message

When Litex runs, the output may include `infer_facts` or other recorded information. Read that message when you want to understand what inference added after a fact was stored.

If a later fact succeeds unexpectedly, the reason is often that an earlier fact inferred useful information such as a sign condition, a membership consequence, a tuple shape, or a numeric substitution.
