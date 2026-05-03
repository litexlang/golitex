# Builtin statements

Try all snippets in browser: https://litexlang.com/doc/Builtin_Features/Builtin_Statements

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Builtin_Features/Builtin_Statements.md


A **statement** is one top-level or nested step Litex reads and executes: introducing names, asserting facts, opening proofs, or dispatching proof tactics. This page matches the statement forms the language supports.

---

## Fact (`Fact`)

Assert a formula (equality, ordering, membership, `forall`, `exist`, compounds with `and` / `or`, etc.). Verification uses the checker rules in scope.

```litex
prove:
    1 + 1 = 2
```

---

## Local definition (`let`)

**`let`** introduces names whose types and defining properties are bundled in a block. It is local to the surrounding proof or scope.

```litex
prove:
    let a R:
        a = 1
    a = 1
```

---

## Named predicate (`prop`)

**`prop name(…) :`** defines a new predicate symbol together with its characterizing properties (often an if-and-only-if-style body).

```litex
prove:
    prop p(x R):
        x = x
```

---

## Abstract predicate symbol (`abstract_prop`)

**`abstract_prop q(…)`** declares a predicate name and arity only; you later assert or prove `$q(…)` as atomic facts.

```litex
prove:
    abstract_prop q(a)
```

---

## Typed parameters (`have`)

**`have x S, y T`** introduces parameters with the given types (membership in standard sets or set-valued types).

```litex
prove:
    have x R, y Z
```

---

## Defined constant (`have … = …`)

**`have a S = expr`** introduces a name and fixes it equal to a value or expression.

```litex
prove:
    have a R = 1
    a = 1
```

---

## Naming witnesses (`have by exist`)

When an existential is already **known**, **have by exist** chooses names that satisfy the existential body.

```litex
prove:
    know exist u R st {u > 0, u < 1}
    have by exist v R st {v > 0, v < 1}: w
    w > 0
```

---

## Function from one defining equation (`have fn … = …`)

**`have fn f(x S) T = body`** defines a function by a single expression on its domain.

```litex
prove:
    have fn f(x R) R = x + 1
    do_nothing
```

---

## Piecewise function (`have fn` with `case`)

**`have fn g(z S) T :`** followed by **`case`** branches gives a definition by cases.

```litex
prove:
    have fn g(z R) R :
        case z = 2: 3
        case z != 2: 4
    do_nothing
```

---

## Function by induction on a parameter (`have fn by induc`)

Defines a function on an inductive domain (e.g. nonnegative integers) with base and step **`case`** branches.

```litex
prove:
    know forall x Z:
        x % 2 = 0 or x % 2 = 1

    have fn by induc from 0: h(x Z: x >= 0) R:
        case x = 0: 1
        case x = 1: 1
        case x >= 2:
            case x % 2 = 0: h(x - 2) + h(x - 1)
            case x % 2 = 1: h(x - 2) + h(x - 1)
```

---

## Parametric family (`family`)

**`family name(params) = …`** defines a parameterized set or function space; instantiate it with **`\pf(R)`**-style syntax (backslash then the family name and arguments).

```litex
prove:
    family self_seq(s set) = fn(x N_pos) s

    forall a \self_seq(R):
        a $in fn(y N_pos) R
        a(1) = a(1)
```

---

## Algorithm and evaluation (`algo` / `eval`)

**`algo m(x):`** gives an executable presentation of a function (often parallel to **`have fn`**). **`eval m(…)`** runs that algorithm on concrete inputs to simplify results.

```litex
prove:
    have fn m(x N_pos) R:
        case x = 1: 1
        case x != 1: 0

    algo m(x):
        case x = 1: 1
        case x != 1: 0

    eval m(1)
    m(1) = 1
```

```litex
prove:
    have g fn(x Z) Z

    know:
        forall x Z:
            x > 0
            =>:
                g(x) = g(x-1) + 1
        g(0) = 0
        forall x Z:
            x < 0
            =>:
                g(x) = g(x+1) - 1

    algo g(x):
        case x > 0: g(x-1) + 1
        case x = 0: 0
        case x < 0: g(x+1) - 1

    eval g(3)
    g(3) = 3
```

---

## Claim (`claim`)

**`claim:`** states a goal and bundles a sub-proof (and optional lemmas) that establishes it.

```litex
prove:
    claim:
        prove:
            1 + 1 = 2
        1 + 1 = 2

    claim:
        prove:
            2 = 2
        2 = 2
```

---

## Assume known facts (`know`)

**`know:`** (or **`know`** with a block) adds lemmas or axioms to the current environment without proving them in this snippet.

```litex
prove:
    know:
        1 = 1
```

---

## Nested proof (`prove`)

**`prove:`** opens a lemma or sub-proof: a nested list of statements closed before the parent continues.

```litex
prove:
    prove:
        2 = 2
```

---

## Import and run file

**`import "path.lit"`** pulls another file into scope. **`run_file "path.lit"`** runs a file as a separate episode. Paths and project layout decide what works in your setup; use the same quoting style your toolchain expects.

---

## No-op (`do_nothing`)

A trivial proof step (placeholder or explicit skip).

```litex
prove:
    do_nothing
```

---

## Clear environment (`clear`)

**`clear`** drops the current top environment and parse-time name map so later lines start fresh (often used so a second `let` with the same name is allowed in a new block).

```litex
prove:
    let a R:
        a = 1
    a = 1

clear

let a R:
    a = 2
a = 2
```

---

## Evaluate an expression (`eval`)

Besides algorithms, **`eval expr`** can reduce closed expressions according to evaluation rules.

```litex
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]
```

---

## Witness for `exist` (`witness exist`)

**`witness exist … from …:`** supplies explicit values and a sub-proof that they satisfy the existential body, concluding **`exist …`**.

```litex
prove:
    witness exist x, y R st {x > y} from 1, 0:
        1 > 0

    exist a, b R st {a > b}
```

---

## Witness non-emptiness (`witness $is_nonempty_set`)

Shows a set is nonempty by naming a member and proving membership.

```litex
prove:
    have s set

    witness $is_nonempty_set(s) from 1:
        know 1 $in s

    $is_nonempty_set(s)
```

---

## Proof by cases (`by cases`)

Splits a goal along a finite disjunction; each **`case`** branch finishes the goal under that assumption.

```litex
prove:
    have fn k(z R) R :
        case z = 2: 3
        case z != 2: 4

    have x R

    x = 2 or x != 2

    by cases:
        prove:
            k(x) > 2
        case x = 2:
            k(x) = 3
            k(x) > 2
        case x != 2:
            k(x) = 4
            k(x) > 2
```

---

## Proof by contradiction (`by contra`)

Assumes the positive form of a statement, derives a contradiction (`impossible`), and concludes the negation.

```litex
prove:
    abstract_prop p0(x, y)
    abstract_prop q0(x, y)

    know forall a, b R:
        $p0(a, b)
        =>:
            $q0(a, b)

    know not $q0(1, 2)

    by contra:
        prove:
            not $p0(1, 2)
        $p0(1, 2)
        impossible $q0(1, 2)
```

---

## Enumerate a finite set (`by enumerate finite_set`)

Finite “for all members of this enumerated set” reasoning—useful for small domains and Cartesian products of finite sets.

```litex
prove:
    let a R:
        a $in {1, 2}

    a = 1 or a = 2

    by enumerate finite_set:
        prove:
            forall a2 {1, 2, 3}:
                a2 < 4
```

---

## Induction (`by induc`)

**`by induc n from base:`** proves **`P(n)`** for a discrete parameter from a base and step known (or proved) in the environment.

```litex
prove:
    abstract_prop r0(a)

    know:
        $r0(0)
        forall n Z:
            n >= 0
            $r0(n)
            =>:
                $r0(n + 1)

    by induc n from 0:
        prove:
            $r0(n)

    forall m Z:
        m >= 0
        =>:
            $r0(m)
```

---

## Bounded iteration shell (`by for`)

**`by for:`** packages a proof skeleton that iterates over a bounded index set (e.g. a **`range`**).

```litex
prove:
    by for:
        prove:
            forall i range(0, 10):
                i < 10
        do_nothing
```

---

## Set equality by extensionality (`by extension`)

Proves **`A = B`** by mutual inclusion, often with **`by enumerate finite_set`** on each side.

```litex
prove:
    by extension:
        prove:
            {1, 2} = {2, 1}
        by enumerate finite_set:
            prove:
                forall x {1, 2}:
                    x $in {2, 1}
        by enumerate finite_set:
            prove:
                forall y {2, 1}:
                    y $in {1, 2}

    {1, 2} = {2, 1}
```

---

## Function membership (`by fn`)

Uses the graph-style characterization of a function value in a function space.

```litex
prove:
    have fn f(x R) R = 1

    by fn: f
```

---

## Instantiate a family (`by family`)

Introduces a **`family`** instance after checking the defining **`forall`** pattern.

```litex
prove:
    family pf(a set) = fn(x a) a

    forall a \pf(R):
        a $in fn(y R) R
        a(1) = a(1)

    by family: \pf(R)
```

---

## Tuple reasoning (`by tuple`)

Structured reasoning on a tuple (components, product typing).

```litex
prove:
    let u set:
        u = (2, 3)

    by tuple: u
```

---

## Function-set membership (`by fn set`)

Proves that a value lives in a **`fn(… ) …`** function set by exhibiting the graph-style axioms (domain, existence of witnesses, uniqueness).

```litex
prove:
    let s set

    know:
        forall u s:
            u $in cart(cart(R, Q), Z)
            tuple_dim(u) = 2

        forall u s:
            exist x R, y Q, z Z st {x > y, x > 2, u = ((x, y), z)}

        forall x R, y Q:
            x > y
            x > 2
            =>:
                exist u s, z Z st {u = ((x, y), z)}

        forall u, v s:
            u $in cart(cart(R, Q), Z)
            v $in cart(cart(R, Q), Z)
            u[1] = v[1]
            =>:
                u = v

    by fn set: s $in fn(x R, y Q: x > y, x > 2) Z

    s(100, 99) = s(100, 99)
```

---

## Enumerate a closed integer interval (`by enumerate ……`)

For **`x`** known to lie in **`closed_range(lo, hi)`**, **`by enumerate lo...hi: x`** runs the finite enumeration tactic on that interval.

```litex
prove:
    have x closed_range(0, 10)

    by enumerate 0...10: x
```

```litex
prove:
    have a Z
    have x closed_range(a, a + 10)

    by enumerate a...a + 10: x
```

---

For verification shortcuts that close many atomic goals without extra `prove:` structure, see [Builtin verification rules](Builtin_Verification_Rules.md).
