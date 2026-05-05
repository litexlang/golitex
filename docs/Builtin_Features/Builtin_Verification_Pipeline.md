# Builtin Verification Pipeline

Try all snippets in browser: https://litexlang.com/doc/Manual/Factual_Statements

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Factual_Statements.md

**Litex** and **LaTeX** are both notations for writing mathematics, and the surface syntax often feels similar (quantifiers, relations, set braces, subscripts, and so on). LaTeX’s job is typesetting; **Litex**’s job is **correctness**: the checker inspects each step so that factual statements can be accepted as true only when they are well-defined and justified under the language rules—then they become known facts you may reuse later. On paper you would do the same proof sketch; in Litex the machine helps ensure you do not slip.

> The result of a *factual statement* —or, in more mathematical terms, a **logical statement**—is either true or unknown. Unknown means the statement is either false, or the checker cannot determine whether it is true or false because of the lack of information.

## Shapes of a factual statement (overview)

In mathematics there are different **kinds** of factual statements: each shape has its own way of being written and its own pattern of verification in the checker. The shapes are not isolated—**they fit together** (for example, chains expand to conjunctions of atomics, and `or`/`and` combine the same atomic building blocks). Here is a overview of the shapes:

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

### Verify Atomic Factual Statements

An **atomic** fact is one **indivisible** judgment at this level: one relation (or negation of one) between terms. Picture it as a single sentence with one **predicate** (equals, less-than, “is in set”, …) and its **arguments**.

Atomic facts are the smallest building blocks of factual statements. They are the ones that are not further decomposable into smaller statements. Since other factual statements are built from atomic facts, we need to know how to verify them first.

> Builtin predicates include verbs such as `$in` and `$is_set` and `=`, `!=`, `<`, `>`, `<=`, `>=`.

> The user can define custom predicates using the `prop` keyword.

> Chains like `a < b < c` are **not** atomic; they are **chain** facts (abbreviations for several atomics).

> In practice, once you understand how **atomic** facts are verified, the verification of the other fact shapes is easy to follow: they are mostly the extensions of atomic checks, organized by conjunction, disjunction, chains, quantifiers, and familiar structure.

Examples of atomic facts:

```litex
1 = 1 # predicate: =, arguments: 1, 1
2 != 3 # predicate: !=, arguments: 2, 3
0 < 1 # predicate: <, arguments: 0, 1
not 1 < 0 # predicate: negation of <, arguments: 1, 0

# predicate: $in, arguments: 1, {1, 2}
1 $in {1, 2}

# predicate: $is_set, arguments: {1, 2}
$is_set({1, 2})

# define custom predicate: is_odd(n) is equivalent to n $in Z and n % 2 = 1
prop is_odd(n Z):
    n % 2 = 1

# predicate: $is_odd, arguments: 1
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
abstract_prop p(x)
know:
    not forall x R:
        $p(x)

not forall x R:
    $p(x)
```

## Verify Well-Definedness of Facts

## Verify Atomic Facts

### Verify Non-Equational Atomic Facts

### Verify Equational Atomic Facts

### Verify Existential Facts

### Verify Disjunction Facts

### Verify Conjunction Facts

### Verify Chain Facts

### Verify Universal Facts

### Verify Universal with Equivalence Facts

### Verify Negated Universal Facts