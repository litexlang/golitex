# Factual Statements

In Litex you often start from a **factual statement** (also called a **logical statement**): one claim the checker should respect—like “this equation holds” or “for every number in this range, that inequality holds.” Litex does not guess; it only follows the language’s rules. If the rules justify the claim, the result is **true**. If the evidence is not there, you get **unknown**—which is preferable to a silent “yes.”

Proofs work the same way as on paper: you have some facts, apply allowed steps, and obtain new facts. Factual statements are the sentences that enter that game.

## Shapes of a fact (overview)

Below is a **road map**. Each row is a different *shape* a fact can take. The sections after the table explain them in order—from the smallest building blocks upward.

| Shape | What it means (in one line) | Typical look |
|-------|-----------------------------|----------------|
| **Atomic** | One basic claim: equality, order, membership, or a single predicate applied to terms. | `1 = 1`, `0 < 1`, `1 $in {1, 2}`, `not 1 < 0` |
| **Existential** | “There is …” / “there is exactly one …” / “there is no …” | `exist x R st { x = 1 }` |
| **Disjunction** | At least one branch holds (`or`). | `1 = 2 or 1 = 1` |
| **Conjunction** | Several atomics all hold (`and`, or separate lines). | `1 = 1 and 2 < 3` — or two lines without `and` |
| **Chain** | Shorthand for several comparisons in a row (e.g. `a < b < c`). | `0 < 1 < 2` |
| **Universal** | “For all … (optionally assuming …), … holds.” | `forall s set: s = s` and blocks with `=>:` |
| **Universal with equivalence** | Same `forall` header, but you also give an `iff` block (`<=>:`). | `x > y` iff `y < x` under the same prefix |
| **Negated universal** | “It is not true that for all …” | `not forall x R: x > 0` |

### Atomic fact

An **atomic** fact is one **indivisible** judgment at this level: one relation (or negation of one) between terms. Picture it as a single sentence with one **verb** (equals, less-than, “is in set”, …) and its **arguments**—no outer `and`, `or`, or quantifier left to peel off.

Chains like `a < b < c` are **not** atomic; they are **chain** facts (abbreviations for several atomics).

**Syntax:** One unit. **Relations** you would write on paper—equality and order—use ordinary tokens with **no** `$`: `=`, `!=`, `<`, `>`, `<=`, `>=`, and negations like `not t1 < t2`. Everything else is a **prop** (predicate): spell it with a leading **`$`**. Builtin props include verbs such as `$in` and `$is_set`; you can also declare **custom** props. If a prop takes **exactly two** arguments, you may use **infix** form `arg1 $name arg2`; otherwise use **prefix** form `$name(arg1, arg2, …)`. Joining several atomics with `or` / `and` changes the shape (see below).

```litex
1 = 1
2 != 3
0 < 1
not 1 < 0

# binary prop: infix `arg1 $in arg2`
1 $in {1, 2}

# prop with other arity: prefix `$is_set(…)`
$is_set({1, 2})

# define custom prop:
prop is_odd(n Z):
    n % 2 = 1

$is_odd(1)
```

### Existential fact

**Existential** facts say: something exists (`exist`), something exists uniquely (`exist!`), or nothing fits (`not exist`). After `st { … }`, you list the facts the witness must satisfy.

**Syntax:** Optional `not`, then `exist` or `exist!`, then typed variables (`x T, …`), then `st`, then `{ … }` with comma-separated inner facts.

```litex
exist x R st { x = 1 }
```

### Disjunction

**Disjunction**: “one of these holds,” with `or` between branches. At this layer each branch is an atomic, a conjunction of atomics, or a chain—not an arbitrary nest of `forall` / `exist` unless the grammar for your context allows it.

**Syntax:** `A or B` (and more `or …` if needed).

```litex
1 = 2 or 1 = 1
```

### Conjunction

**Conjunction**: “all of these hold,” using `and` between **atomic** facts. Litex **prefers** separate lines at the same indentation: same meaning, easier to read.

**Syntax:** `atom0 and atom1 …`, or—**preferred**—one atomic per line, no `and`.

```litex
1 = 1 and 2 < 3

# same meaning; preferred
1 = 1
2 < 3
```

### Chain fact

A **chain** strings binary relations on one line (usually inequalities). Logically it is only **shorthand**: `a < b < c` means `a < b` **and** `b < c`. No extra logical power—just notation.

**Syntax:** `t0 rel0 t1 rel1 …` with relations the chaining grammar accepts (`<`, `>`, `<=`, `>=`, and `=` where allowed).

```litex
0 < 1 < 2

# same as
0 < 1 and 1 < 2
```

### Universal quantification

**Universal** facts: fix typed variables, optionally assume some **domain** facts, then require **conclusions** for every instance that satisfies the domain.

**Block form:** After `forall` (or `forall!` where the bang/inline rules apply), list variables and types, then `:`. If there is **no** domain guard, put each conclusion on its own indented line under the header. If there **is** a guard, list the guard facts, then a line `=>:`, then the conclusions **indented one step further**.

**Compact one-line form:** Patterns like `forall! a T: dom => { conc }` or `forall! a T: { fact, … }` are allowed; if the parser complains, use a **block** `forall` instead.

```litex
forall s set:
    s = s

forall t R:
    100 < t
    =>:
        0 < t
```

### Universal with equivalence

Sometimes you package a law together with an **equivalent** restatement: after the `=>:` block, add `<=>:` and another indented block. Both sides are tied to the same `forall` header and domain.

**Syntax:** Same header as block `forall`. Body: `=>:` block, then line `<=>:`, then the second block (same indentation role as the first `=>:` block).

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

### Negated universal

**Not forall** denies a universal claim: there is a counterexample. The block mirrors the `forall` you are refuting—same parameters and `=>:` layout when a domain guard is present.

**Syntax:** `not forall` (no `!`), then the same header as the positive universal, then the indented body. In some inner positions only a full block is legal; the checker’s message tells you when to lift the statement.

```litex
not forall x R:
    x > 0
```
