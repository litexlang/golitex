# Quick Reference                           

*version: 0.1.0*

_Jiachen Shen and The Litex Team_

---

_Simple can be harder than complex: You have to work hard to get your thinking clean to make it simple. But it’s worth it in the end because once you get there, you can move mountains._

_– Steve Jobs_

---

Litex is a **simple, set-theoretic** formal language for mathematics: enough structure for everyday arguments without a long apprenticeship. Each construct is meant to match a **real mathematical idea** and stays as close to natural language as possible.

This quick reference summarizes Litex syntax and meaning alongside minimal examples. More on the project: [Litex](https://litexlang.com), [GitHub](https://github.com/litexlang/golitex).

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

---

### Existential fact

**Meaning.** “There exist values for the parameters such that every fact in the brace holds (∃).”

**Syntax.** `exist` *parameter groups (names and types / sets)* `st` `{` *facts separated by commas* `}`.

**Example.**

```litex
witness exist x R st {x > 0, x < 1} from 0.5

exist x R st {x > 0, x < 1}
```

> **Hint — the word “witness” is used for proving exist fact by giving a concrete object for the parameter.** Here 0.5 is a witness for the parameter `x`.

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
abstract_prop P(a R, b R)
```

---

### `struct` — structured type

**Meaning.** A record-like type: field declarations, optionally an iff-block (`<=>:`) tying instances to a predicate on `self`.

**Syntax.** `struct` *name* `(` *parameters* `)` `:` field lines, optional `<=>:` block.

**Example.**

```litex
struct point(s set):
    x s
    y s
```

---

### `family` — parametric type family

**Meaning.** A type constructor: for fixed parameters, the right-hand side names a definite set (e.g. a function space).

**Syntax.** `family` *name* `(` *parameters* `)` `=` *object*.

**Example.**

```litex
family matrix(s set, m N_pos, n N_pos) =
    fn(i closed_range(1, m), j closed_range(1, n)) s
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

> **Hint.** Piecewise functions and induction variants are easier to copy from **`examples/have_fn_case_by_case.lit`** and **`examples/have_fn_by_induc.lit`**.

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

**Syntax.** `claim` `:` newline; first sub-block is `prove` `:` with exactly one fact; following sub-blocks are proof steps.

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

## Witnesses

### `witness exist … from …`

**Meaning.** Prove an existential by giving concrete witnesses and a small proof that the brace conditions hold.

**Syntax.** `witness exist` *existential* `from` *objects* … optional `:` and indented proof (see parser rules if you omit `:`).

**Example.** See **`examples/witness_exist.lit`**.

---

### `witness $is_nonempty_set(…) from …`

**Meaning.** Prove a set is nonempty by naming a member and showing membership.

**Syntax.** `witness $is_nonempty_set(` *set* `) from` *object* `:` proof block.

**Example.** See **`examples/witness_nonempty.lit`**.

---

## Proof tactics (`by …`)

**Meaning.** Tactics all start with **`by`** and a second keyword; they package common proof patterns (cases, contradiction, induction, …).

**Syntax.** `by` *tactic* `:` … (shape depends on tactic; each entry below).

**Example.** See the tactic you need in **`examples/by_*.lit`**.

### `by cases`

**Meaning.** Prove a goal under each case of a cover (disjunction of case assumptions).

**Syntax.** `by cases` `:` `prove` `:` *goal* newline, then `case` *assumption* `:` proof …

**Example.** **`examples/by_cases.lit`**.

---

### `by contra`

**Meaning.** Prove the fact in `prove:` by assuming its **negation**, deriving a contradiction, and closing with **`impossible`** on an atomic fact that is jointly inconsistent in the checker’s sense.

**Syntax.** `by contra` `:` `prove` `:` *atomic goal* newline, proof… `impossible` *atomic fact*.

**Example.** **`examples/by_contra.lit`**.

> **Hint.** The fact after `prove:` is what you **conclude**, not the assumption; the assumption is its negation.

---

### `by enumerate`

**Meaning.** Prove a universal claim over parameters ranging in **finite list sets** `{ … }`.

**Syntax.** `by enumerate` *param* *list set* [, … ] `:` `prove` `:` *goals* … optional extra steps.

**Example.** **`examples/list_set_and_enumerate.lit`**.

---

### `by induc`

**Meaning.** Induction on an integer parameter from a given base; needs a suitable induction principle in context.

**Syntax.** `by induc` *param* `from` *object* `:` body blocks.

**Example.** **`examples/by_induc.lit`**.

---

### `by for`

**Meaning.** For `forall` with parameters in **`range`** or **`closed_range`**, enumerate values, assume domain facts, run the proof, check conclusions.

**Syntax.** `by for` `:` `prove` `:` single `forall` (only those range forms), then proof steps.

**Example.** **`examples/for.lit`**, **`examples/diagonal_matrix.lit`**.

---

### `by extension`

**Meaning.** Set equality by extensionality (typically mutual inclusion).

**Syntax.** `by extension` `:` `prove` `:` *set* `=` *set* newline, proof.

**Example.** **`examples/by_extension.lit`**.

---

### `by fn`

**Meaning.** Use the graph / membership characterization of a function you already introduced.

**Syntax.** `by fn` `:` *object*.

**Example.** **`examples/by_fn.lit`**.

---

### `by fn set`

**Meaning.** Show a function belongs to a **function set** `fn(… conditions …) co-domain`.

**Syntax.** `by fn set` `:` *func* `$in fn` *function-set*.

**Example.** **`examples/by_fn_set.lit`**.

---

### `by family`

**Meaning.** Use an instantiated **family** (e.g. `family` *name* `(` *args* `)`).

**Syntax.** `by family` `:` *object*.

**Example.** **`examples/by_family.lit`**.

---

### `by struct`

**Meaning.** Use the defining data of a **struct** instance.

**Syntax.** `by struct` `:` *object*.

**Example.** **`examples/by_struct.lit`**.

---

### `by tuple`

**Meaning.** Tuple / product-space reasoning on an object.

**Syntax.** `by tuple` `:` *object*.

**Example.** **`examples/by_tuple.lit`**.

---

## Evaluation and files

### `eval`

**Meaning.** Evaluate a call using the **`algo`** attached to a function.

**Syntax.** `eval` *expression* (typically a function application).

**Example.** **`examples/algo_eval.lit`**.

---

### `import`

**Meaning.** Load another module or file path into scope.

**Syntax.** `import` `"path"` [`as` *name*] or `import` *module* [`as` *name*].

**Example.**

```litex
import "other.lit"
```

---

### `run_file`

**Meaning.** Run another `.lit` file.

**Syntax.** `run_file` `"path"`.

**Example.** **`examples/runfile.lit`**.

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
| `by` | Proof tactic (`cases`, `contra`, `enumerate`, `induc`, `for`, `extension`, `fn`, `fn set`, `family`, `struct`, `tuple`) |
| `eval` | Run algorithm |
| `import` | Import module/file |
| `run_file` | Run a file |
| `do_nothing` | No-op |
| *(other)* | Assert a fact to verify |

> **Hint.** Details and edge cases are easiest to see in **`examples/`** next to the checker behavior you care about.
