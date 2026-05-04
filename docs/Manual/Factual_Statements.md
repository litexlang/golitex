# Factual Statements

In Litex, many stories begin with a small sentence: you write a **factual statement** (also called a **logical statement**), like laying on paper a promise still waiting to be decided. Litex will not declare “obviously true” for you; it only takes what you said and probes it with the cool, dependable rules of the Litex language. When the probe succeeds, the answer is **true**. When the evidence is not enough, it says **unknown**—honest rather than pretending to know everything.

If you think of mathematics as a journey that only moves from premises to conclusions, the whole edifice is built the same way: you hold known facts, take one step along strict rules, and gain a new fact. The world widens bit by bit, like roots branching in the dark—yet every step remains accountable.

## Shapes of a fact

The spine is familiar: an **atomic** judgment (a predicate or relation with arguments, i.e. one **verb** and its parameters); **existential** and **universal** quantification and their **negated** surface forms (`not exist`, `not forall`); **disjunction**; and a few extra surface conveniences (**conjunction**, **chains**, **forall** with an **iff** block). In the implementation, every factual statement is classified into exactly one arm of the `Fact` enum; the table uses the same Rust names. **Each row is unpacked below** with commentary and examples.

| `Fact` variant | Rust payload type | Role |
|----------------|-------------------|------|
| `AtomicFact` | `AtomicFact` | One atomic judgment (equality, order, membership, many `$builtin` forms and their negations, …). |
| `ExistFact` | `ExistFactEnum`: `ExistFact`, `ExistUniqueFact`, `NotExistFact` | Existential packaging: `exist`, `exist!` (unique witness), `not exist`. |
| `OrFact` | `OrFact` | Disjunction (`or`) between branches. |
| `AndFact` | `AndFact` | Conjunction (`and`) of atomic facts. |
| `ChainFact` | `ChainFact` | **Syntactic sugar only**: notation such as `a < b < c` is shorthand for the **conjunction** of the pairwise binary relations (`a < b` and `b < c`). It does not introduce a new logical primitive; it is there for readability, though the checker may exploit order structure on chains for convenience. |
| `ForallFact` | `ForallFact` | Universal quantification, optionally with domain hypotheses before `=>:`. |
| `ForallFactWithIff` | `ForallFactWithIff` | A `ForallFact` together with an `iff` block (`<=>:`), i.e. an equivalent reformulation under the same prefix. |
| `NotForall` | `NotForallFact` | Denial of a `forall` (`not forall …`). |

### Atomic fact

An **atomic** fact is a single judgment that does not decompose into a smaller factual statement at this layer: equalities and inequalities, membership and subset facts, many `$builtin` predicates, negated forms of those, and similar. Chains such as `a < b < c` are **not** atomic—they are a dedicated **chain** fact (see below).

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

```litex
exist x R st { x = 1 }

# typically alongside `abstract_prop p(a, b)` (see examples/exist.lit)
exist a R st { $p(a, 1) }
exist! b R st { $p(b, 1) }
not exist y R st { $p(y, 2) }
```

### Disjunction (`OrFact`)

**Disjunction** is “one of these cases holds,” written with `or` between branches. Each branch is, at this layer, an atomic fact, a conjunction of atomics, or a chain.

```litex
1 = 2 or 1 = 1
```

### Conjunction (`AndFact`)

**Conjunction** is “all of these hold at once,” written with `and`, between **atomic** facts only at this level (unlike generic logical “and” mixing arbitrary subformulas in prose).

```litex
1 = 1 and 2 < 3
```

### Chain fact

A **chain** is a string of binary relations on the same line—typically order comparisons—parsed as one `ChainFact`. As in the table, this is **not** a separate logical notion: it abbreviates the conjunction of those pairwise atomics. The kernel may still apply order closure on chains where axioms justify it.

```litex
0 < 1 < 2
```

### Universal quantification (`ForallFact`)

**Universal** facts fix typed variables, optionally assume **domain** facts (hypotheses before `=>:`), and require **consequent** facts for every instantiation that satisfies the domain.

```litex
forall s set:
    s = s

forall t R:
    100 < t
    =>:
        $a_lt_c(0, 100, t)
        0 < t
```

### Universal with equivalence (`ForallFactWithIff`)

Sometimes you state a universal law together with an **equivalent** reformulation. Litex represents that as one `ForallFact` plus an `iff` block (`<=>:`): you are asking the kernel to treat the two sides as mutually entailing under the same quantifier prefix and domain.

```litex
forall x, y R:
    =>:
        x > y
    <=>:
        y < x
```

### Negated universal (`NotForall`)

**Not forall** is the explicit denial of a `forall` statement: there is a counterexample to the claimed universal. Surface syntax is `not forall` with the same block structure as the corresponding `forall`.

```litex
not forall x R:
    x > 0
```
