# Builtin statements

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Manual/Statements

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Statements.md

_If you can't explain it to a six year old, you don't understand it yourself._

_- Albert Einstein_

A **statement** is a basic line or block of Litex code. You use statements to do mathematical reasoning, make definitions such as `prop`, functions, and sets, and prove facts from known facts or axioms.

This page is a practical reference. Read each section as: **what the statement means**, **when to use it**, and **what shape the code usually has**.

Statements are the outer actions in a Litex file. Some statements contain [Factual Statements](Factual_Statements.md), which are checked through the flow described in [Proof Process](Proof_Process.md).

---

## Assert a fact

Write a fact directly when you want Litex to verify it from what is already known. Facts include equality, order, membership, `forall`, `exist`, and compound facts with `and` / `or`.

```litex
1 + 1 = 2
```

> Hint: A bare fact should already follow from the current context. If you want to prove a fact in a sub-proof and add only the final fact back to the current context, use `claim:`.

Common fact types:

| Kind | Fact type | Example |
|------|-----------|---------|
| Atomic fact | Equality | `1 + 1 = 2` |
| Atomic fact | Inequality / order | `2 < 3`, `3 <= 3` |
| Atomic fact | Membership | `2 $in R` |
| Atomic fact | Predicate fact | `$prime(17)` |
| Atomic fact | Atomic negation | `2 != 3`, `not 1.1 $in Z` |
| Compound fact | Conjunction | `1 < 2 and 2 < 3` |
| Compound fact | Disjunction | `1 < 2 or 1 >= 2` |
| Compound fact | Chain | `1 <= 2 = 2 < 3` |
| Quantified fact | Existence | `exist x R st {x > 0}` |
| Quantified fact | Unique existence | `exist! x R st {x = 0}` |
| Quantified fact | Universal fact | `forall! x R: x = x` |

For a fuller explanation, see [Factual Statements](https://litexlang.com/doc/Manual/Factual_Statements).

---

## Named predicate (`prop`)

Use **`prop`** to name a mathematical property. The body says what the property means.

After a `prop` is defined, Litex can verify later predicate facts by using that definition. In the example below, `$p(1)` holds because `1 $in R` and `1 = 1`.

```litex
prop p(x R):
    x = x

$p(1)
```

> Example: after defining `prop p(x R): ...`, you can write `$p(1)` instead of repeating the definition each time.

---

## Abstract predicate symbol (`abstract_prop`)

Use **`abstract_prop`** when you want a predicate symbol but do not want to define it yet. It only declares the name; it does not give the predicate any mathematical property by itself.

If you want an abstract predicate to have a property, introduce that property with `know`.

```litex
abstract_prop p(x)

know forall x R:
    $p(x)

$p(1)
```

> Hint: `abstract_prop` is useful for examples, axiomatized theories, and temporary placeholders while developing a proof.

---

## Typed parameters (`have`)

Use **`have x S`** to introduce a new object `x` of `set` or `nonempty_set` or `finite_set` or set like `R`(real numbers), `Z`(integers), `{1, 2, 3}`(enumerated set), `cart(R, Z)`(Cartesian product), etc. We say `x` has *type* `S`.

```litex
have x R, y Z
```

This records that `x` belongs to `R` and `y` belongs to `Z`, so later facts can use them.

> Hint: `have x S` is not a free way to create an element of any set. Litex must be able to verify that `S` is nonempty, for example by knowing `$is_nonempty_set(S)`, before it can introduce a new object `x` with `x $in S`.

## What "type" means in Litex?

The word **type** in Litex does not mean a type in type theory. Litex is based on set theory. A parameter type is one of a few surface forms:

```litex
have x R
have A set
have B nonempty_set
have C finite_set
```

`have x R` means `x $in R`: the "type" `R` is a set that contains `x`.

`set`, `nonempty_set`, and `finite_set` are closer to actions than ordinary object types. They introduce a new name and record facts about it:

```litex
have A set
have B nonempty_set
have C finite_set

$is_set(A)
$is_nonempty_set(B)
$is_finite_set(C)
```

Since Litex follows the set-theoretic view, every object you introduce is an object in the set-theoretic universe. In this sense, `$is_set(x)` holds for any introduced object `x`.

The same parameter-type idea also appears in `forall`, `exist`, `prop`: you can write parameters such as `forall x R, y set:` or `exist A set st { ... }`. Function signatures are more restrictive. When defining a function, each input position must use an object as its domain, such as `fn(x R) Z`; you cannot use action-like forms such as `set`, `nonempty_set`, or `finite_set` as a function input requirement.

---

## Defined constant (`have … = …`)

Use **`have a S = expr`** to introduce a name and fix its value. For example, `have a R = 1` introduces a constant `a` with value `1` and in set `R`.

```litex
have a R = 1
a = 1
```

> Hint: use this for constants. A function should normally be introduced with `have fn`.

---

## Naming witnesses (`have by exist`)

When an existential fact is already known, **`have by exist`** gives names to its witnesses. After that, you can use the witness properties directly.

```litex
know exist u R st {u > 0, u < 1}
have by exist v R st {v > 0, v < 1}: w
w > 0
```

---

## Function from one defining equation (`have fn … = …`)

Use **`have fn f(x S) T = body`** when the value of the function is given by one expression.

```litex
have fn f(x R) R = x + 1

forall x R:
    f(x) $in R
    f(x) = x + 1
```

> Example: this says that for each `x R`, the value `f(x)` satisfies `f(x) $in R` and `f(x) = x + 1`.

---

## Piecewise function (`have fn` with `case`)

Use **`case`** branches when the formula for a function depends on conditions.

```litex
have fn g(z R) R :
    case z = 2: 3
    case z != 2: 4

forall z R:
    g(z) $in R

forall z R:
    z = 2
    =>:
        g(z) = 3

forall z R:
    z != 2
    =>:
        g(z) = 4
```

> Hint: the cases should cover the domain you intend to use.

---

## Function from unique existence (`have fn … by forall … exist!`)

Use this when mathematics tells you that for every input there exists a **unique** output. Litex then introduces the corresponding function.

```litex
abstract_prop p(x)
abstract_prop F(x, y)
have A set
have B set

know forall x A:
    $p(x)
    =>:
        exist! y B st {$F(x, y)}

have fn f by forall x A:
    $p(x)
    =>:
        exist! y B st {$F(x, y)}

forall x A:
    $p(x)
    =>:
        $F(x, f(x))
```

> Meaning: the unique witness `y` is now named by the function value `f(x)`.

> Hint: the `forall` after `by` must already be known. Its conclusion must be exactly one `exist!` fact with one output parameter.

---

## Function by induction on a parameter (`have fn by induc`)

Use **`have fn by induc`** to define a function on an inductive domain, such as nonnegative integers. Base cases and the recursive step are written as `case` branches.

The intended meaning is close to strong induction for defining a function. The first `case` lines give the starting values. The final `case x >= ...:` is the recursive step: when defining `h(x)`, the right-hand side may use values of the same function that are already defined, from the starting value up to `x - 1`. It may not use `h(x)` itself or any later value such as `h(x + 1)`.

If the final recursive step has nested `case` branches, those branches should cover all possible situations for the current `x`. They should also behave like a real case split: overlapping branches must not give conflicting values. If two branches can both apply, their right-hand sides should be provably equal under the overlap.

```litex
know forall x Z:
    x % 2 = 0 or x % 2 = 1

have fn by induc from 0: h(x Z: x >= 0) R:
    case x = 0: 1
    case x = 1: 1
    case x >= 2:
        case x % 2 = 0: h(0) + h(x - 1)
        case x % 2 = 1: h(x - 2) + h(x - 1)
```


---

## Object definition without  (`let`)

Use **`let`** to introduce names together with assumptions or definitions about them. The names are local to the surrounding proof or block.

```litex
let a R:
    a = 1
a = 1

let b, c R: b < c

b < c
```

> Hint: `let` and `know` both introduce new facts without verification. Litex allows this and warns you because these statements are useful when you intentionally add axioms or temporary assumptions, but abusing them can make the system unsound. In most cases, do not use them; use `have`, a bare fact, or `claim` when you want Litex to verify the reasoning.

---

## Parametric family (`family`)

**`family name(params) = …`** defines a parameterized set or function space; instantiate it with **`\pf(R)`**-style syntax (backslash then the family name and arguments).

A `family` is different from a function introduced by `have fn`. A function is an object that takes input values. A `family` is a template for building an object, usually a set or a function space. Because it is only a template, its parameters can use forms such as `s set`. Each time you write `\self_seq(R)`, Litex substitutes `R` for `s` in the right-hand side of the family definition and uses the resulting object.

```litex
family self_seq(s set) = fn(x N_pos) s

forall a \self_seq(R):
    a $in fn(y N_pos) R
    a(1) = a(1)
```

---

## Algorithm and evaluation (`algo` / `eval`)

**`algo m(x):`** gives an executable presentation of a function (often parallel to **`have fn`**). **`eval m(…)`** runs that algorithm on concrete inputs to simplify results.

An `algo` is not the same as a function in a programming language such as Python. When you define an `algo`, Litex checks that the case flow really matches the function facts you have given. In the example below, the two cases must agree with the definition of `m`.

`algo` also does not compute by floating-point approximation. It works with exact symbolic arithmetic, so the current evaluator only supports operations such as `+`, `-`, `*`, and integer powers.

```litex
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

> Hint: Like algorithms in ordinary programming languages, an `algo` can still run forever during evaluation if its recursive calls do not terminate.

---

## Claim (`claim`)

**`claim:`** states a goal and bundles a sub-proof (and optional lemmas) that establishes it.

The point of `claim` is that the proof process does not enter the main environment. The temporary facts used inside the proof stay inside the claim; only the final fact you wanted to prove is added to the surrounding context.

```litex
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

> Hint: `know` is an axiom-like statement. Litex allows it and warns you, but in most ordinary proofs you should prefer facts that Litex verifies directly, or use `claim` to prove a fact in a sub-proof before adding it to the context.

```litex
# three primitive terms:
have point nonempty_set
have line nonempty_set
have plane nonempty_set

# All elements on a line or a plane are points (power_set: the set of all subsets of a set)
know:
    forall l line:
        l $in power_set(point)
    forall pl plane:
        pl $in power_set(point)
```

---

## Nested proof (`prove`)

**`prove:`** opens a lemma or sub-proof: a nested list of statements closed before the parent continues.

It does not affect the outside environment at all. You can think of it as a scratch space for checking a piece of reasoning: facts introduced or proved inside the `prove` block disappear when the block ends.

```litex
prove:
    2 = 2
```

---

## run file

**`run_file "path.lit"`** runs a file as a separate episode. Paths and project layout decide what works in your setup; use the same quoting style your toolchain expects.

```text
run_file "local_path_to_file.lit"
```

---

## No-op (`do_nothing`)

A trivial proof step (placeholder or explicit skip). Write `do_nothing` or `...` to skip a proof step.

```litex
do_nothing
...
```

---

## Clear environment (`clear`)

**`clear`** drops the current top environment and parse-time name map so later lines start fresh (often used so a second `let` with the same name is allowed in a new block).

```litex
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
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]] # matrix addition

eval sum(1, 2, '(x Z) Z {sum(2, 3, '(y Z) Z {x + y})}) # sum of a sum
```

---

## Witness for `exist` (`witness exist`)

**`witness exist … from …:`** supplies explicit values and a sub-proof that they satisfy the existential body, concluding **`exist …`**.

Existence proofs are often used together with `have by exist`: first prove that some object exists, then name the witness so later lines can use an object with the stated properties.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist a, b R st {a > b}

have by exist x, y R st {x > y}: w, z
w > z
```

---

## Witness non-emptiness (`witness $is_nonempty_set`)

Shows a set is nonempty by naming a member and proving membership.

```litex
witness $is_nonempty_set({1, 2, 3}) from 1:
    1 $in {1, 2, 3}

$is_nonempty_set({1, 2, 3})
```

---

## Proof by cases (`by cases`)

Splits a goal along a finite disjunction; each **`case`** branch finishes the goal under that assumption.

```litex
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

> Hint: Many `by ...` statements are not random proof commands. They match the logical shape of the factual statement you are trying to prove or use. For example, `by cases` matches an `or` fact, `by contra` matches negation, and `by induc` matches an inductive or universal pattern over a discrete domain. Other `by ...` statements are tied to specific object structures: `by for` works with bounded ranges, `by enumerate` works with finite objects, and `by extension` works with set equality.



---

## Bounded iteration shell (`by for`)

**`by for:`** packages a proof skeleton that iterates over a bounded index set (e.g. a **`range`**).

```litex
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

## Enumerate a closed integer interval (`by enumerate ……`)

For **`x`** known to lie in **`closed_range(lo, hi)`**, **`by enumerate lo...hi: x`** runs the finite enumeration tactic on that interval.

```litex
have x closed_range(0, 10)

by enumerate 0...10: x
```

```litex
have a Z
have x closed_range(a, a + 10)

by enumerate a...a + 10: x
```

---

## Set-theoretic bridge tactics (`by fn`, `by family`, `by tuple`, `by fn set`)

These statements are usually not the most useful things to write in ordinary proofs. They exist mainly so every object that appears in Litex has a definite set-theoretic meaning. For example, a function is represented by graph-style facts, a tuple by its components and product typing, and a `family` instance by substituting arguments into its template.

| Statement | What it connects to |
|-----------|---------------------|
| `by fn: f` | The graph-style facts behind a known function `f` |
| `by family: \pf(R)` | The object obtained by substituting `R` into a `family` template |
| `by tuple: u` | The set-theoretic structure of a tuple object |
| `by fn set: s $in fn(...) ...` | The graph-style conditions that make a set behave as a function |

> Hint: Most users do not need these statements at first. They are mainly semantic bridge tools: useful when you need to expose the set-theoretic object behind a Litex surface form.

---

## Statement summary

The sections above explain the common use cases. This table is a quick map of the statement families.

| Statement | Main use |
|-----------|----------|
| fact line | Verify a mathematical fact from the current context |
| `prop` | Define a named mathematical property |
| `abstract_prop` | Declare a predicate symbol without defining it |
| `have x S` | Introduce an object with a type or set |
| `have x S = expr` | Introduce a named value |
| `have by exist` | Name witnesses from a known existential fact |
| `have fn ... = ...` | Define a function by one formula |
| `have fn ... : case ...` | Define a function by cases |
| `have fn ... by forall ... exist!` | Define a function from unique existence |
| `have fn by induc` | Define a recursive function by induction |
| `let` | Introduce local names and local assumptions |
| `family` | Define a parameterized set or function space |
| `algo` / `eval` | Define and run executable mathematical algorithms |
| `claim` | State a goal and prove it in a sub-block |
| `know` | Add facts or axioms to the current context |
| `prove` | Open a nested proof block |
| `import` / `run_file` | Use code from another file |
| `do_nothing` | Explicit no-op proof step |
| `clear` | Reset the current working context |
| `witness exist` | Prove an existential by giving witnesses |
| `witness $is_nonempty_set` | Prove a set is nonempty by giving an element |
| `by cases` | Prove a goal by splitting into cases |
| `by contra` | Prove by contradiction |
| `by enumerate finite_set` | Check a finite list of cases |
| `by enumerate n...m` | Check a finite integer interval `n <= x <= m` |
| `by induc` | Prove a statement by induction |
| `by for` | Run a bounded proof skeleton |
| `by extension` | Prove set equality by mutual membership |
| `by fn` / `by fn set` / `by family` / `by tuple` | Expose the set-theoretic meaning behind function, family, and tuple objects |

> Hint: when learning Litex, start with `have`, `know`, bare facts, `claim`, and `by cases`. The other statements become useful when your proofs need definitions, functions, induction, or finite enumeration.
