# Litex Cheatsheet                           

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_Cheatsheet

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_Cheatsheet.md


*version: 0.1.0*

---

_Simple can be harder than complex: You have to work hard to get your thinking clean to make it simple. But it’s worth it in the end because once you get there, you can move mountains._

_– Steve Jobs_

---

Litex is a **simple, set-theoretic** formal language for mathematics: enough structure for everyday arguments without a long apprenticeship. Each construct is meant to match a **real mathematical idea** and stays as close to natural language as possible.

This quick reference summarizes Litex syntax and meaning alongside minimal examples.

---

## Facts (formulas the checker understands)

Most mathematical content in Litex is a **fact**: it may appear after `know`, as a goal under `claim` / `prove:`, as a **bare line** the checker must verify, or nested inside `exist` / `forall`. Below, each subsection uses **Meaning**, **Syntax**, **Example**, and sometimes a **Hint**.

---

### Atomic fact

**Meaning.** A single primitive judgment: equality or inequality between expressions, membership (`$in`), a built-in predicate (`$is_nonempty_set`, …), a user-defined predicate call (`$p(…)`), or the negation of such a statement (`not …`). These are the building blocks of larger facts.

**Syntax.** One atomic formula, e.g. *expr* `=` *expr*, *expr* `<` *expr*, *expr* `$in` *set*, `$`*name*`(` *args* `)`, `not` *atomic*, etc.

**Example.**

```litex
prove:
    1 + 1 = 2
    2/3 < 4/5
    1.5 $in R
    $is_set(Z)
    not $is_nonempty_set({})
```

> **Hint — storing a linear equality.** When an equality is recorded, if one side evaluates to a numeric literal and the other is a single “layer” around one non-constant leaf (`+`, `-`, `*`, `/` with the other operand a literal), the checker also records the solved equality for that leaf (e.g. `t - 1 = 6` also stores `t = 7`). For `*`, division is used only when the coefficient literal is **not** zero (never divide by `0`).

---

### Existential fact

**Meaning.** “There exist values for the parameters such that every fact in the brace holds (∃).”

**Note.** `exist!` uses the **same** header and brace shape; the difference is uniqueness (see **Existential with uniqueness**): proving or storing `exist!` also involves the matching **`forall`** uniqueness fact.

**Syntax.** `exist` *parameter groups (names and types / sets)* `st` `{` *facts separated by commas* `}`.

**Example.**

```litex
witness exist x R st {x > 0, x < 1} from 0.5

exist x R st {x > 0, x < 1}
```

> **Hint — the word “witness” is used for proving exist fact by giving a concrete object for the parameter.** Here 0.5 is a witness for the parameter `x`.

---

### Existential with uniqueness (`exist!`)

**Meaning.** Same existential (∃) claim as `exist` for the braced facts. **Uniqueness** is enforced by also requiring the companion **`forall`** fact (“any two parameter tuples satisfying the body agree / are equal”). **Verification:** discharging an `exist!` goal needs that uniqueness `forall` proved (or already known), in addition to the usual witness reasoning. **Storage:** when `exist!` is recorded in the environment, the runtime **also stores** that generated uniqueness **`forall`**.

**Syntax.** `exist!` *parameter groups* `st` `{` *facts separated by commas* `}` — the lexer splits this as the keyword `exist` followed by `!` (whitespace optional).

**Example.**

```litex
abstract_prop p(a, b)
abstract_prop q(a, b)

know:
    exist a, b, c R st {$p(a, b), $q(b, c)}
    forall a1, b1, c1 R, a2, b2, c2 R:
        $p(a1, b1)
        $q(b1, c1)
        $p(a2, b2)
        $q(b2, c2)
        =>:
            (a1, b1, c1) = (a2, b2, c2)

exist! a, b, c R st {$p(a, b), $q(b, c)}

abstract_prop t(a)

know:
    exist a R st {$t(a)}
    forall a1, a2 R:
        $t(a1)
        $t(a2)
        =>:
            a1 = a2

exist! a R st {$t(a)}
```

---

### Disjunction (`or`)

**Meaning.** At least one of the disjuncts is true.

**Syntax.** *fact* `or` *fact* (you can nest longer `or` chains).

**Example.**

```litex
prove:
    have a R = 1
    a = 1 or a = 2
```

> **Hint — the word “have” is used for introducing a parameter and fixing it to a given value.** Here `a` is introduced and fixed to 1.

> **Hint - when fact1 is correct then fact1 or fact2 or ... factn is correct.**

---

### Conjunction (`and`)

**Meaning.** Every conjunct is true at the same time.

**Syntax.** *fact* `and` *fact* (you can chain with repeated `and`).

**Example.**

```litex
1 = 1 and 1 + 2 = 3
```

This is equivalent to:

```litex
1 = 1
1 + 2 = 3
```

> **Hint.** In Litex, the nicer way to write `fact1 and fact2` is to put them on separate lines in the same block.

---

### Chain fact

**Meaning.** The same relation is repeated along a list of terms (e.g. *a < b < c* packages *a < b* and *b < c* in one surface form).

**Syntax.** *expr* *rel* *expr* *rel* *expr* … with one relational symbol throughout the chain.

**Example.**

```litex
prove:
    1 < 2 < 3 = 3 * 1 <= 8
```

This is equivalent to:

```litex
1 < 2
2 < 3
3 = 3 * 1
3 * 1 <= 8
```

> **Hint — chains and what gets stored.** When you write a **single-direction** chain of order and equality along the line (e.g. *a ≤ b = c < d*, mixing `=`, `<=`, `<` in one “increasing” direction), the checker does not only keep the **step-by-step** facts along the chain. It also **adds the implied comparisons between farther-apart endpoints** (transitive closure respecting `=` blocks and where strict `<` must stay strict). For that example you effectively get facts such as *a ≤ c*, *a < d*, and *b < d* in the context as well. That is usually very convenient—you can cite the short chain once and reuse the consequences later.

---

### Universal fact (`forall` with `=>:`)

**Meaning.** “For all instantiations of the parameters, if the optional domain facts hold, then each conclusion holds.” This is the usual hypothetical universal: lemmas, axioms, theorems with hypotheses.

**Syntax.** `forall` *parameter groups* `:` optional domain facts (one or more lines), then `=>:` and one or more conclusion facts (typically indented).

**Example.**

```litex
forall a R:
    a > 0
    =>:
        a + 1 > 1
```

> **Hint — the word “type” in `forall` / `exist` headers.** People often read this as “programming types” or “type theory”; in Litex it is **not** that. After a parameter name, the next token is either (i) a **named set** the object is assumed to lie in—treated like `a $in Z`—or (ii) one of **`set`**, **`finite_set`**, **`nonempty_set`**, which stand for **`$is_set`**, **`$is_finite_set`**, **`$is_nonempty_set`** and do **not** mean “membership in a set called `set`.”
>
> ```litex
> forall a Z:
>     a $in Z
>
> forall a set, b finite_set, c nonempty_set:
>     $is_set(a)
>     $is_finite_set(b)
>     $is_nonempty_set(c)
> ```
>
> So in `forall a Z:`, the header already gives `a $in Z`. The only exceptions are those three keywords: they are **predicates on the parameter**, not a containing set. `forall a set, b finite_set, c nonempty_set:` gives you `$is_set(a)`, `$is_finite_set(b)`, `$is_nonempty_set(c)`. Keep in mind that `set`, `finite_set`, `nonempty_set` are **syntax sugar** to express properties of the parameter, not a containing set.

---

### Universal fact with iff (`forall` with `<=>:`)

**Meaning.** “For all …, the left fact is equivalent to the right fact.” Used for **definitions** and reversible characterizations. Some places (e.g. certain `claim` goals) do not allow an iff-`forall` as the stated goal.

**Syntax.** `forall` *parameter groups* `:` optional domain facts, then `<=>:` and the two directions (layout matches your `know` / library style).

**Example.**

```litex
forall a, b R:
    =>:
        a <= b
    <=>:
        0 <= b - a
```

## Statements in general

**Meaning.** A **statement** is usually one line or a header plus an indented block. Facts are the main payload; reserved words introduce definitions, hypotheses, witnesses, and tactics.

**Syntax.** One non-empty line starts a statement; continuation lines are indented under that header. The first token (if it is a keyword) selects which grammar applies; otherwise the line is parsed as a fact to verify.

**Example.**

```litex
know:
    1 + 1 = 2

claim:
    prove:
        2 + 2 = 4
    prove:
        4 = 2 + 2
```

> **Hint.** **`know:`** adds hypotheses without proof. **`claim:`** states one goal in an inner **`prove:`** and then discharges it with further steps. Most step-by-step work uses nested **`prove:`** blocks.

---

## Definitions and declarations

### `prop` — defined predicate

**Meaning.** Give a named proposition and its **definition** as a list of facts (what holds iff the predicate holds).

**Syntax.** `prop` *name* `(` *parameters* `)` `:` newline, indented facts; or end the header after `)` with no body.

**Example.**

```litex
prop divides(a Z, b Z):
    exist k Z st { b = k * a }
```

---

### `abstract_prop` — declared predicate only

**Meaning.** Reserve a predicate symbol and its arity for abstract reasoning; no defining body.

**Syntax.** `abstract_prop` *name* `(` *parameter names separated by commas* `)`.

**Example.**

```litex
abstract_prop P(a, b)
```

---

### `struct` — structured type

**Meaning.** Preview syntax for record-like declarations and field access.

`struct` is currently documented separately because its syntax and semantics are still changing. See [Preview Features](https://litexlang.com/doc/Preview_Features) for the current `struct`, field access, struct parameter, and `by struct` behavior.

---

### `family` — parametric type family

**Meaning.** A type constructor: for fixed parameters, the right-hand side names a definite set (e.g. a function space).

**Syntax.** `family` *name* `(` *parameters* `)` `=` *object*.

**Example.** (Name `mat_grid` is illustrative; `matrix` is reserved.)

```litex
family mat_grid(s set, m N_pos, n N_pos) = fn(i closed_range(1, m), j closed_range(1, n)) s
```

---

### `algo` — executable algorithm

**Meaning.** A computational definition used with **`eval`**: branch on parameters with `case` … and returns.

**Syntax.** `algo` *name* `{` *parameters* `}` `:` newline, then `case` branches (and optionally a default return block).

**Example.**

```litex
prove:
    have fn f(x R) R = 1
    algo f(x):
        1
    eval f(0)
```

---

## Introducing objects and functions

### `have` — parameters or values

**Meaning.** Introduce names in scope for the rest of the block: **typed parameters** (membership / type keywords), **fixed values** with `=`, **functions** (single equation or `case` branches), **inductive functions** (`have fn by induc from` …), or **names from an existential** already known (`have by exist` …).

**Syntax.**

- `have` *groups* — types only, no `=`.
- `have` *groups* `=` *objects* …
- `have fn` *name* *function-space clause* `=` *object*
- `have fn` *name* *clause* `:` newline, `case` *fact* `:` *object* …
- `have by exist` *exist … st { … }* `:` *names*

**Example.**

```litex
prove:
    have x R = 1
    x $in R
    have a R, b R
    a + b = b + a
```

> **Hint.** Piecewise functions and induction variants:

`have_fn_case_by_case.lit`:

```litex
have fn self_max(x, y R) R:
    case x > y: x
    case x <= y: y
```

`have_fn_by_induc.lit`:

```litex
know forall x Z:
    x % 2 = 0 or x % 2 = 1

have fn by induc from 0: f(x Z: x >= 0) R:
    case x = 0: 1
    case x = 1: 1
    case x >= 2:
        case x % 2 = 0: f(x - 2) + f(x - 1)
        case x % 2 = 1: f(x - 2) + f(x - 1) + 100
```

---

### `know` — hypotheses

**Meaning.** Assume facts (axioms, lemmas, or previously proved results) without proof.

**Syntax.** `know` `:` newline and indented facts; or `know` followed by one `forall` / fact on the same head line; or several comma-separated atomic / exist-shaped facts on one line.

**Example.**

```litex
know:
    forall a R:
        a + 0 = a
```

---

## Claims and proof structure

### `claim`

**Meaning.** State a **goal** (one fact after inner `prove:`) and then a linear proof. The goal cannot be an iff-`forall` form.

**Syntax.** `claim` `:` newline; first sub-block is `prove` `:` with exactly one fact; following sub-blocks are proof steps. **Shorthand:** `claim` `=>` *fact* `:` on the header line, then indented proof steps (no inner `prove:`).

**Example.**

```litex
claim:
    prove:
        1 = 1 and 1 + 2 = 3
    1 = 1
    1 + 2 = 3
```

---

### `prove`

**Meaning.** Nested proof: a sequence of statements for a sub-goal or lemma.

**Syntax.** `prove` `:` newline, indented statements.

**Example.**

```litex
prove:
    know:
        2 = 2
    2 = 2
```

---

### `do_nothing`

**Meaning.** A no-op step (e.g. when a tactic expects a non-empty body).

**Syntax.** `do_nothing`.

**Example.**

```litex
prove:
    do_nothing
```

---

### `clear`

**Meaning.** Clear only the **current** (top) environment and the **current** (top) parse-time name map: the top env is replaced by an empty one, and the top name map is emptied. The single builtin layer is left unchanged when it is the only layer. Use a **top-level** statement if you need the same source name again—inside one `prove:` block the body is parsed in one pass, so a second `let` with the same identifier is still rejected at parse time.

**Syntax.** `clear`.

**Example.**

```litex
prove:
    let a R:
        a = 1
    a = 1

clear

prove:
    let a R:
        a = 2
    a = 2
```

---

## Witnesses

### `witness exist … from …`

**Meaning.** Prove an existential by giving concrete witnesses and a small proof that the brace conditions hold.

**Syntax.** `witness exist` *existential* `from` *objects* … optional `:` and indented proof (see parser rules if you omit `:`).

**Example.**

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist x, y R st {x > y}
```

---

### `witness $is_nonempty_set(…) from …`

**Meaning.** Prove a set is nonempty by naming a member and showing membership.

**Syntax.** `witness $is_nonempty_set(` *set* `) from` *object* `:` proof block.

**Example.**

```litex
have s finite_set = {1}

witness $is_nonempty_set(s) from 1:
    know 1 $in s

$is_nonempty_set(s)
```

---

## Proof tactics (`by …`)

**Meaning.** Tactics all start with **`by`** and a second keyword; they package common proof patterns (cases, contradiction, induction, …).

**Syntax.** `by` *tactic* `:` … (shape depends on tactic; each entry below).

**Example.** Each tactic subsection below ends with a full code sketch (same content as the matching `by_*.lit` file in the repo).

> **Same goal, three tactics.** A single arithmetic fact such as `1 = 1` can be proved with **`by cases`** (exhaustive branches), **`by contra`** (assume the negation, then `impossible`), or **`claim`** (state the goal and finish in one step). `by cases` and `claim` support the **header shorthand** `… => goal:`. `by contra` writes the goal directly after `by contra`, as in `by contra 1 = 1:`.

### `by cases`

**Meaning.** Prove a goal under each case of a cover (disjunction of case assumptions).

**Syntax.** `by cases` `:` `prove` `:` *goal* newline, then `case` *assumption* `:` proof … Each `prove:` fact must not be `forall` (use atomic, exist, or/and combinations, or chains). **Shorthand:** `by cases` `=>` *goal* `:` on the header line, then `case` arms (no inner `prove:`).

**Example.**

```litex
by cases:
    prove:
        1 + 1 = 2
    case 1 + 1 = 2:
        1 + 1 = 2
    case 1 + 1 != 2:
        1 + 1 = 2
        impossible 1 + 1 = 2
```

Execution:

1. verify case1 or case2 or ... or caseN
2. verify case by case: assume the case assumption, verify the case body, then conclude the case assumption. 
    2.1 If the case assumption is impossible, write `impossible <fact>` at end of the case body. Verify that the fact itself and its negation are both true in this proof scope. Then contradiction is derived. So this case is impossible we no longer need to consider it.
    2.2 If the case assumption is not impossible, run the case body and the goal must be proved in this case.

---

### `by contra`

**Meaning.** Prove the fact in `prove:` by assuming its **negation**, deriving a contradiction, and closing with **`impossible`** on an atomic fact that is jointly inconsistent in the checker’s sense.

**Syntax.** `by contra` `:` `prove` `:` *atomic goal* newline, proof… `impossible` *atomic fact*. **Shorthand:** `by contra` *atomic goal* `:` on the header line, then optional proof blocks and closing `impossible`.

**Example.**

```litex
abstract_prop p(a)

have b R, c R

# Assume $p(a + b) implies $p(a) for all a R
know forall a R:
    $p(a + b)
    =>:
        $p(a)

# Assume $p(c) is false
know not $p(c)

by contra:
    prove:
        not $p(c + b)
    impossible $p(c)

by contra 1 = 1:
    impossible 1 != 1
```

Execution:

1. assume the negation of the goal
2. verify the goal body
3. At end of proof body, write `impossible <fact>`. Verify that the fact itself and its negation are both true in this proof scope. Then contradiction is derived.

> **Hint.** The fact after `prove:` is what you **conclude**, not the assumption; the assumption is its negation.

---

### `by enumerate finite_set`

**Meaning.** Prove a `forall` whose parameters range over **finite list sets** `{ … }`. The checker forms the Cartesian product of those lists, assigns each combination to the parameters, and for each tuple runs the same **domain → optional proof → then** flow as **`by for`** (which enumerates integers from `range` / `closed_range` instead of list-set members).

**Syntax.** Same layout as `by for`: header is `by enumerate` `finite_set` `:` (keyword `finite_set` before the colon). The first body block is `prove:` containing **exactly one** nested block, parsed as a single **`forall`** fact. Shorthand: `by enumerate finite_set` inline `forall!` `:` with proof steps in the body.

- Each `forall` parameter’s type must be a **list set** `{ … }` (the value of each parameter is always one element of that list).
- The `forall` may use **domain** lines before `=>:` and **then** lines under `=>:`; or omit `=>:` so every line under `forall` is a conclusion (no domain), like ordinary `forall` parsing.
- **Domain checks** match `by for`: if a domain fact is verified **true**, it is assumed; if **unknown**, the checker may **skip** that tuple when the same “skippable negation” as in `by for` is verified **true**; otherwise the step fails. After domains succeed (or the branch is skipped), optional proof blocks run, then each **then** fact must verify.
- Further body blocks after `prove:` are proof steps, parsed in a local parsing-time name scope (names do not leak to the file).

**Example.**

```litex
by enumerate finite_set:
    prove:
        forall a {1, 2}:
            a = 1 or a = 2
    do_nothing
```

**Example (domain and `=>:`).**

```litex
by enumerate finite_set:
    prove:
        forall a {1, 2}:
            a > 1
            =>:
                a = 2
    do_nothing

by enumerate finite_set forall! a {1, 2}, b {3, 4}: a > 1, b > 3 => {(a, b) = (2, 4)}:
    ...
```

Integer **closed_range** membership with literal endpoints uses **`by enumerate` *lo*`...`*hi* `:`** *object* (next section), not list-set enumeration.

---

### `by enumerate` *range* `:` *object*

**Meaning.** From membership of an object in a **closed interval** with **integer literal** endpoints, store the finite disjunction *obj = lo* `or` *obj = lo+1* `or` … `or` *hi* (you must already know the object lies in that `closed_range`).

**Syntax.** `by enumerate` *lo* `...` *hi* `:` *object* — *range* parses to `Obj::ClosedRange` (same as `closed_range(lo, hi)`); *object* is any expression the parser accepts as an `obj`.

**Example.**

```litex
prove:
    have x closed_range(0, 10) # equivalent to have x 0...10

    by enumerate 0...10: x

prove:
    have a Z
    have x closed_range(a, a + 10)

    by enumerate a...a + 10: x
```

---

### `by induc`

**Meaning.** Induction on an integer parameter from a given base. In a local environment, optional proof steps run first; then for each goal the checker verifies the base instance (with *param* := *object*), that *object* lies in `Z`, and that the usual induction-step `forall` (hypothesis *param* ≥ base together with the goal template implies the *param*+1 instance) holds. On success, the corresponding universal fact (`forall` *param* in `Z`, *param* ≥ base ⇒ goals) is stored. You still need a usable induction principle in context (e.g. from `know`).

**Syntax.**

```text
by induc param from object:
    prove:
        goal_1
        goal_2
        …
    proof_statement
    …
```

- The first body block must be `prove:`; each nested block under it is one atomic-style goal (`ExistOrAndChainAtomicFact`).
- Further blocks are optional proof steps (same idea as after `prove:` in `claim` / `by enumerate finite_set`). They are parsed under a local parsing-time name scope so names introduced there do not leak to the file.
- Multiple goals share one proof segment and one local run; each goal is checked in turn after that proof.

**Example.**

```litex
# Minimal `by induc` example: first block is `prove:` (one or more goals);
# optional proof blocks follow (here empty — lemmas come from `know`).

abstract_prop p(a)

know:
    $p(0)
    forall n Z:
        n >= 0
        $p(n)
        =>:
            $p(n + 1)

by induc n from 0:
    prove:
        $p(n)
    $p(0)
    forall n Z:
        n >= 0
        $p(n)
        =>:
            $p(n + 1)

# Derived from the above by induction
forall n Z:
    n >= 0
    =>:
        $p(n)
```

```litex
claim:
    prove:
        forall x Z:
            0 <= x
            =>:
                x % 2 = 0 or x % 2 = 1

    by induc x from 0:
        prove:
            x % 2 = 0 or x % 2 = 1

        0 % 2 = 0

        claim:
            prove:
                forall y Z:
                    0 <= y
                    y % 2 = 0 or y % 2 = 1
                    =>:
                        (y + 1) % 2 = 0 or (y + 1) % 2 = 1

            by cases:
                prove:
                    (y + 1) % 2 = 0 or (y + 1) % 2 = 1
                case y % 2 = 0:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (0 + 1) % 2 = 1
                case y % 2 = 1:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0
```

---

### `by for`

**Meaning.** For `forall` with parameters in **`range`** or **`closed_range`**, enumerate values, assume domain facts, run the proof, check conclusions. For **list sets** `{ … }` instead of ranges, use **`by enumerate finite_set`** (same `prove:` / `forall` shape; see above).

**Syntax.** `by for` `:` `prove` `:` single `forall` (only those range forms), then proof steps. Shorthand: `by for` inline `forall!` `:` with proof steps in the body.

```litex
by for:
    prove:
        forall n range(0, 10):
            n < 10
    do_nothing

by for:
    prove:
        forall n closed_range(0, 10):
            n <= 10
    do_nothing

by for forall! n range(0, 10): n < 10:
    ...
```

---

### `by extension`

**Meaning.** Set equality by extensionality (typically mutual inclusion).

**Syntax.** `by extension` `:` `prove` `:` *set* `=` *set* newline, proof.

**Example.**

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

### `by fn`

**Meaning.** Use the graph / membership characterization of a function you already introduced.

**Syntax.** `by fn` `:` *object*.

**Example.**

```litex
have f fn(x R)R

by fn : f
```

---

### `by fn set`

**Meaning.** Show a function belongs to a **function set** `fn(… conditions …) co-domain`.

**Syntax.** `by fn set` `:` *func* `$in fn` *function-set*.

**Example.**

```litex
let f set

know:
    forall x1 f:
        x1 $in cart(R, Q, Z)
        tuple_dim(x1) = 3

    forall x1 f:
        exist x2 R, x3 Q, z Z st {x2 > x3, x2 > 2, x1 = (x2, x3, z)}

    forall x2 R, x3 Q:
        x2 > x3
        x2 > 2
        =>:
            exist x1 f, z Z st {x1 = (x2, x3, z)}

    forall x1, x2 f:
        x1 $in cart(R, Q, Z)
        x2 $in cart(R, Q, Z)
        x1[1] = x2[1]
        x1[2] = x2[2]
        =>:
            x1 = x2

by fn set: f $in fn(x1 R, y1 Q: x1 > y1, x1 > 2) Z

f(100,99) = f(100,99)
```

---

### `by family`

**Meaning.** Use an instantiated **family** (syntax `\` *name* `(` *args* `)`; `family` is only the definition keyword).

**Syntax.** `by family` `:` *object*.

**Example.**

```litex
family self_seq(s set) = fn(x N_pos) s

forall a \self_seq(R):
    a $in fn(y N_pos)R
    a(1) = a(1)

family p(a set) = fn(x a) a

by family: \p(R) # 生成 \p(R) = fn(x R) R。即用实参 R 替换形参 a
```

---

### `by struct`

**Meaning.** Preview syntax for instantiating a `forall` fact with tuple data for a struct parameter.

The old `by struct: struct ...` form is no longer the current design. See [Preview Features](https://litexlang.com/doc/Preview_Features) for the current `by struct P from (...) as Point:` form and its boundaries.

---

### `by tuple`

**Meaning.** Tuple / product-space reasoning on an object.

**Syntax.** `by tuple` `:` *object*.

**Example.**

```litex
by tuple: (1, 2)
```

---

## Evaluation and files

### `eval`

**Meaning.** Evaluate a call using the **`algo`** attached to a function (and other forms supported by the runtime’s `eval` pipeline, such as numeric expressions and matrix literals).

**Syntax.** `eval` *expression* (typically a function application).

**Example.**

```litex
let f set
know f $in fn(x R, y R) R

know:
    forall x, y R:
        x < 0
        =>:
            f(x, y) = f(x + 1, y)

    forall x, y R:
        x = 0
        =>:
            f(x, y) = y

    forall x, y R:
        x > 0
        =>:
            f(x, y) = f(x - 1, y)

algo f(x, y):
    case x < 0: f(x + 1, y)
    case x = 0: y
    case x > 0: f(x - 1, y)
```

---

### `import`

**Meaning.** Load another module or file path into scope.

**Syntax.** `import` `"path"` [`as` *name*] or `import` *module* [`as` *name*].

**Example.**

<!-- litex:skip-test -->
```litex
import "other.lit"
```

---

### `run_file`

**Meaning.** Run another `.lit` file.

**Syntax.** `run_file` `"path"`.

**Example.**

<!-- litex:skip-test -->
```litex
run_file "./runfile2.lit"

$p(1, 2)
```

---

## Local parameters (`let`)

**Meaning.** Introduce names with types (membership in a set, or built-in kinds like `set` / `finite_set` / `nonempty_set`) **without** requiring the checker to prove the ambient set nonempty first; optionally add an indented block of facts that constrain those names (“let … such that …”). Less common than `have` for introducing working variables in proofs.

**Syntax.** `let` *parameter groups with types* `:` newline, then indented facts; the `:` block can be omitted if there are no constraints.

**Example.**

```litex
prove:
    let a, b, c set:
        $is_nonempty_set(a)
    $is_nonempty_set(a)
```

---

## Keyword cheat sheet (first word on a line)

**Meaning.** Quick lookup: how a line is classified from its first token.

**Syntax.** First column = allowed prefix; second = role.

**Example.**

| Starts with | Role |
|-------------|------|
| `prop` | Define predicate |
| `abstract_prop` | Declare predicate |
| `struct` | Define structure type |
| `family` | Define type family |
| `algo` | Define algorithm for `eval` |
| `have` | Introduce parameters, values, functions, or witnesses from `exist` |
| `let` | Local parameters / constraints (optional block) |
| `know` | Assume facts |
| `claim` | Theorem + proof |
| `prove` | Nested proof block |
| `witness` | Witness for `exist` or nonempty set |
| `exist` / `exist!` | Existential facts (latter needs uniqueness in context; see **Existential with uniqueness**) |
| `by` | Proof tactic (`cases`, `contra`, `enumerate finite_set`, `enumerate` *range* `:`, `induc`, `for`, `extension`, `fn`, `fn set`, `family`, `finite_seq`, `seq`, `matrix`, `struct`, `tuple`) |
| `eval` | Run algorithm |
| `import` | Import module/file |
| `run_file` | Run a file |
| `do_nothing` | No-op |
| `clear` | Clear top env + top parse-time name map |
| *(other)* | Assert a fact to verify |

> **Hint.** Details and edge cases are covered in the **Example** code blocks above; the repository **`examples/`** folder may contain longer variants.

