# Factual Statements

In Litex, many stories begin with a small sentence: you write a **factual statement** (also called a **logical statement**), like laying on paper a promise still waiting to be decided. Litex will not declare “obviously true” for you; it only takes what you said and probes it with the cool, dependable rules of the Litex language. When the probe succeeds, the answer is **true**. When the evidence is not enough, it says **unknown**—honest rather than pretending to know everything.

If you think of mathematics as a journey that only moves from premises to conclusions, the whole edifice is built the same way: you hold known facts, take one step along strict rules, and gain a new fact. The world widens bit by bit, like roots branching in the dark—yet every step remains accountable.

## Shapes of a fact

The spine is familiar: **atomic** judgments (one **predicate** or **relation** applied to **terms**—informally a single **verb** with its **noun** arguments); **existential** and **universal** quantification and their **negated** surface forms (`not exist`, `not forall`); **disjunction**; and a few extra surface conveniences (**conjunction**, **chains**, **forall** with an **iff** block). Every factual statement falls under **one** of the shapes below. **Each row is unpacked in its subsection**, with commentary, **syntax**, and longer examples.

| Shape | Role | Examples |
|-------|------|----------|
| **Atomic** | **Atomic formula**: one **predicate** / **relation** applied to a list of **terms** (informally, a single **verb** with **noun**-like arguments); includes equality, order, membership, many `$builtin` forms and their negations, … | `1 = 1`, `0 < 1`, `1 $in {1, 2}`, `not 1 < 0` |
| **Existential** | Packaging with `exist`, `exist!` (unique witness), or `not exist`. | `exist x R st { x = 1 }`, `exist! b R st { $p(b, 1) }`, `not exist y R st { $p(y, 2) }` (the last two typically need an `abstract_prop` in context) |
| **Disjunction** | Alternatives joined with `or`. | `1 = 2 or 1 = 1` |
| **Conjunction** | Atomic facts joined with `and`. | `1 = 1 and 2 < 3` (prefer two lines: `1 = 1` then `2 < 3`) |
| **Chain** | **Syntactic sugar only**: notation such as `a < b < c` is shorthand for the **conjunction** of the pairwise binary relations (`a < b` and `b < c`). It adds no new logical primitive; it is notation for readability, though the checker may exploit order structure on chains for convenience. | `0 < 1 < 2`, `a <= b < c` |
| **Universal** | `forall`, optionally with domain hypotheses before `=>:`. | `forall! a R: { a > 0, a + 1 > 1 }`; `forall s set:`<br>`    s = s`; `forall` with hypotheses before `=>:` (full pattern in subsection below) |
| **Universal with equivalence** | The same universal prefix together with an `iff` block (`<=>:`)—an equivalent reformulation under that prefix. | `forall x, y R:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`=>:`<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`x > y`<br>&nbsp;&nbsp;&nbsp;&nbsp;`<=>:`<br>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`y < x` |
| **Negated universal** | Denial of a universal claim: `not forall …`. | `not forall x R:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`x > 0` |

### Atomic fact

In logical vocabulary, an **atomic** fact is an **atomic formula**: you pick one **predicate** or **relation symbol** `P` and supply **terms** `t_1`, …, `t_n` naming the objects that fill its argument places—grammar-school pictures match this: `P` is the lone **verb** (equals, lies in, …), and each `t_i` is a **noun**-like expression (constants, tuples, or larger phrases that denote a single value). The fact asserts that relation holds of those arguments, or states a negation still packaged as one such judgment, or is an equality between terms, or another **non-compound** form Litex treats at this layer (membership, ordering, many `$builtin` forms). There is no outer `and`, `or`, or quantifier to strip off here. Chains such as `a < b < c` are **not** atomic—they are a **chain** fact (see below).

**Syntax:** A single **atomic** unit at this layer. Common patterns: `t1 = t2`, `t1 != t2`; comparisons (`<`, `>`, `<=`, `>=`) and their negations (`not t1 < t2`, …); membership `t1 $in t2`; and predicate calls `$name(t1, …, tn)` (abstract or builtin). Do **not** join several such judgments with `or` / `and` here—that yields disjunction / conjunction shapes instead.

```litex
1 = 1
2 != 3
0 < 1
not 1 < 0
1 $in {1, 2}
$is_set({1, 2})
```

### Existential fact

**Existential** facts assert that something exists (`exist`), that something exists uniquely (`exist!`), or that no witness exists (`not exist`). The body lists typed variables and a finite bundle of facts they must satisfy (possibly with nested `forall` inside the body).

**Syntax:** Optionally `not`, then `exist` or `exist!`, then a comma-separated list of parameters with types (`x1 T1, x2 T2, …`), then `st`, then `{ … }`. Inside the braces, separate the required facts with commas. (Proofs often introduce these goals with `witness exist … from …`.)

```litex
exist x R st { x = 1 }

exist a R st { $p(a, 1) }
exist! b R st { $p(b, 1) }
not exist y R st { $p(y, 2) }
```

### Disjunction

**Disjunction** is “one of these cases holds,” written with `or` between branches. Each branch is, at this layer, an atomic fact, a conjunction of atomics, or a chain.

**Syntax:** `branch0 or branch1` (and further `or branchk` if needed). Each `branch` is parsed as an atomic, `and`-of-atomics, or chain—not an arbitrary nested `forall`/`exist` unless the parser allows that composition in your context.

```litex
1 = 2 or 1 = 1
```

### Conjunction

**Conjunction** is “all of these hold at once,” written with `and`, between **atomic** facts only at this level (unlike generic logical “and” mixing arbitrary subformulas in prose). Litex **encourages** stating separate facts on **separate lines** instead of stringing them with `and`; the single-line form below means the same as the two-line form right under it.

**Syntax:** `atom0 and atom1` (repeat `and …` as needed), or—**preferred**—write each `atomk` on its **own line** at the same block indentation with **no** `and`.

```litex
1 = 1 and 2 < 3

# same meaning, preferred style
1 = 1
2 < 3
```

### Chain fact

A **chain** is a string of binary relations on the same line—typically order comparisons. As in the table, this is **not** a separate logical notion: it abbreviates the conjunction of those pairwise atomics. The checker may still apply order closure on chains where axioms justify it.

**Syntax:** One line of the form `t0 rel0 t1 rel1 … tn`, where each `reli` is a binary relation token the chaining grammar accepts (e.g. `<`, `>`, `<=`, `>=`, and `=` where allowed). No `and` appears between the segments; whitespace follows normal Litex rules.

```litex
0 < 1 < 2

# Equivalent to 
0 < 1 and 1 < 2
```

### Universal quantification

**Universal** facts fix typed variables, optionally assume **domain** facts (hypotheses before `=>:`), and require **consequent** facts for every instantiation that satisfies the domain.

**Syntax (block):** After `forall` (or `forall!` where the inline/bang rules apply), list bound variables with their types, then `:`. If there are **no** domain assumptions, put the conclusions directly under the header, each on its own indented line. If there **are** domain assumptions, list them first; then a line `=>:`; then the conclusions, each indented one level **deeper** than `=>:`.

**Syntax (inline `forall!`):** On one line, patterns like `forall! a T: dom => { conc }` or `forall! a T: { fact, … }` are supported; see `examples/inline_forall.lit`. Restrictions apply when `forall` / `not forall` appears inside other constructs—follow parser errors or use a **block** `forall` instead.

```litex
forall s set:
    s = s

forall t R:
    100 < t
    =>:
        $a_lt_c(0, 100, t)
        0 < t
```

### Universal with equivalence

Sometimes you state a universal law together with an **equivalent** reformulation: a `forall` block and an `iff` block (`<=>:`) so that the two sides are mutually entailing under the same quantifier prefix and domain.

**Syntax:** Same header as a block `forall`. In the body, include a `=>:` section (facts implied by the universal claim), then a `<=>:` marker line, then another **indented** block of facts (the equivalent conclusion at the same logical level as the first `=>:` block).

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

### Negated universal

**Not forall** is the explicit denial of a `forall` statement: there is a counterexample to the claimed universal. Surface syntax is `not forall` with the same block structure as the corresponding `forall`.

**Syntax:** `not forall` (without `!`), then the same parameter list and `:` as in the positive case, then an indented block listing the facts that would have to hold **for all** instances—what you are refuting. For a refutation with a domain guard, use the same `=>:` layout as in `forall`. Some inner positions forbid `not forall` without a block; the checker will tell you when to hoist it to a full block.

```litex
not forall x R:
    x > 0
```
