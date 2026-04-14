# Manual

_Jiachen Shen and The Litex Team_

---

_Simple can be harder than complex: You have to work hard to get your thinking clean to make it simple. But it’s worth it in the end because once you get there, you can move mountains._

_– Steve Jobs_

---

Litex is a **simple, set-theoretic** formal language for mathematics: enough structure for everyday arguments without a long apprenticeship. Each construct is meant to match a **real mathematical idea** and stays as close to natural language as possible.

This manual provides a straightforward guide to using Litex. More on the project: [Litex](https://litexlang.com), [GitHub](https://github.com/litexlang/golitex).

---

## Facts (formulas the checker understands)

Most mathematical content in Litex is a **fact**: it may appear after `know`, as a goal under `claim` / `prove:`, as a **bare line** the checker must verify, or nested inside `exist` / `forall`. Below, each subsection follows the same pattern as elsewhere in this manual: **Meaning**, **Syntax**, **Example**.

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
know:
    exist x R st {x > 0, x < 1}
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

---

### Conjunction (`and`)

**Meaning.** Every conjunct is true at the same time.

**Syntax.** *fact* `and` *fact* (you can chain with repeated `and`).

**Example.**

```litex
prove:
    know:
        1 = 1 and 1 + 2 = 3
    1 = 1 and 1 + 2 = 3
```

---

### Chain fact

**Meaning.** The same relation is repeated along a list of terms (e.g. *a < b < c* packages *a < b* and *b < c* in one surface form).

**Syntax.** *expr* *rel* *expr* *rel* *expr* … with one relational symbol throughout the chain.

**Example.**

```litex
prove:
    1 < 2 < 3
```

---

### Universal fact (`forall` with `=>:`)

**Meaning.** “For all instantiations of the parameters, if the optional domain facts hold, then each conclusion holds.” This is the usual hypothetical universal: lemmas, axioms, theorems with hypotheses.

**Syntax.** `forall` *parameter groups* `:` optional domain facts (one or more lines), then `=>:` and one or more conclusion facts (typically indented).

**Example.**

```litex
know:
    forall a R:
        a > 0
        =>:
            a + 1 > 1
```

---

### Universal fact with iff (`forall` with `<=>:`)

**Meaning.** “For all …, the left fact is equivalent to the right fact.” Used for **definitions** and reversible characterizations. Some places (e.g. certain `claim` goals) do not allow an iff-`forall` as the stated goal.

**Syntax.** `forall` *parameter groups* `:` optional domain facts, then `<=>:` and the two directions (layout matches your `know` / library style).

**Example.**

```litex
know:
    forall a, b R:
        =>:
            a <= b
        <=>:
            0 <= b - a
```

---

### Bare line (assert a fact as a statement)

**Meaning.** You assert one fact; the kernel tries to prove it from the current context—same role as a proof step that is only a formula.

**Syntax.** A whole line that is **not** introduced by a reserved keyword (see the cheat sheet): the line is parsed as one fact.

**Example.**

```litex
prove:
    know:
        2 = 2
    2 = 2
```

Further patterns: **`examples/atomic_fact.lit`**, **`examples/or_fact.lit`**, **`examples/and_fact.lit`**, **`examples/chain_fact.lit`**, **`examples/verify_exist_fact.lit`**, **`examples/use_forall_arithmetic_to_prove.lit`**.

---

## Statements in general

A **statement** is usually one line or one indented block. Facts are the main payload; special keywords introduce definitions, hypotheses, witnesses, and tactics.

Many proof blocks use **`prove:`** followed by indented steps. **`claim:`** introduces a stated goal (one fact) and its proof. **`know`** adds hypotheses without proof.

---

## Definitions and declarations

### `prop` — defined predicate

**Meaning.** Give a named proposition and its **definition** as a list of facts (what holds iff the predicate holds).

**Syntax.** `prop` *name* `(` *parameters* `)` `:` newline, indented facts; or end the header after `)` with no body.

### `abstract_prop` — declared predicate only

**Meaning.** Reserve a predicate symbol and its arity for abstract reasoning; no defining body.

**Syntax.** `abstract_prop` *name* `(` *parameter names separated by commas* `)`.

### `struct` — structured type

**Meaning.** A record-like type: field declarations, optionally an iff-block (`<=>:`) tying instances to a predicate on `self`.

**Syntax.** `struct` *name* `(` *parameters* `)` `:` field lines, optional `<=>:` block.

### `family` — parametric type family

**Meaning.** A type constructor: for fixed parameters, the right-hand side names a definite set (e.g. a function space of sequences).

**Syntax.** `family` *name* `(` *parameters* `)` `=` *object*.

### `algo` — executable algorithm

**Meaning.** A computational definition used with **`eval`**: branch on parameters with `case` … and returns.

**Syntax.** `algo` *name* `{` *parameters* `}` `:` newline, then `case` branches (and optionally a default return block).

---

## Introducing objects and functions

### `have` — parameters or values

**Meaning.**

- **Typed parameters:** introduce variables with types or membership, in scope for the rest of the block.
- **With `=`:** introduce parameters and fix them to given values.
- **Functions:** define a function on a domain, either by a single equation or by **`case`** branches (piecewise).
- **Inductive function:** `have fn by induc from` *start* `:` … (see **`examples/have_fn_by_induc.lit`**).
- **From an existential:** `have by exist` *existential fact* `:` *witness names* — name witnesses once an existential is already known.

**Syntax (sketch).**

- `have` *groups* — only types, no `=`.
- `have` *groups* `=` *objects* …
- `have fn` *name* *function-space clause* `=` *object*
- `have fn` *name* *clause* `:` newline, `case` *fact* `:` *object* …
- `have by exist` *exist … st { … }* `:` *names*

### `know` — hypotheses

**Meaning.** Assume facts (axioms, lemmas, or previously proved results) without proof.

**Syntax.** `know` `:` newline and indented facts; or `know` followed by one `forall` / fact on the same head line; or several comma-separated atomic / exist-shaped facts on one line.

---

## Claims and proof structure

### `claim`

**Meaning.** State a **goal** (one fact after inner `prove:`) and then a linear proof. The goal cannot be an iff-`forall` form.

**Syntax.** `claim` `:` newline; first sub-block is `prove` `:` with exactly one fact; following sub-blocks are proof steps.

### `prove`

**Meaning.** Nested proof: a sequence of statements for a sub-goal or lemma.

**Syntax.** `prove` `:` newline, indented statements.

### `do_nothing`

**Meaning.** A no-op step (e.g. when a tactic expects a non-empty body).

**Syntax.** `do_nothing`.

---

## Witnesses

### `witness exist … from …`

**Meaning.** Prove an existential by giving concrete witnesses and a small proof that the brace conditions hold.

**Syntax.** `witness exist` *existential* `from` *objects* … optional `:` and indented proof (see parser rules if you omit `:`).

### `witness $is_nonempty_set(…) from …`

**Meaning.** Prove a set is nonempty by naming a member and showing membership.

**Syntax.** `witness $is_nonempty_set(` *set* `) from` *object* `:` proof block.

---

## Proof tactics (`by …`)

All start with **`by`** and a second keyword.

### `by cases`

**Meaning.** Prove a goal under each case of a cover (disjunction of case assumptions).

**Syntax.** `by cases` `:` `prove` `:` *goal* newline, then `case` *assumption* `:` proof …

### `by contra`

**Meaning.** Prove the fact in `prove:` by assuming its **negation**, deriving a contradiction, and closing with **`impossible`** on an atomic fact that is jointly inconsistent in the checker’s sense.

**Syntax.** `by contra` `:` `prove` `:` *atomic goal* newline, proof… `impossible` *atomic fact*.

**Note.** The fact after `prove:` is what you **conclude**, not the assumption; the assumption is its negation.

### `by enumerate`

**Meaning.** Prove a universal claim over parameters ranging in **finite list sets** `{ … }`.

**Syntax.** `by enumerate` *param* *list set* [, … ] `:` `prove` `:` *goals* … optional extra steps.

### `by induc`

**Meaning.** Induction on an integer parameter from a given base; needs a suitable induction principle in context.

**Syntax.** `by induc` *param* `from` *object* `:` body blocks.

### `by for`

**Meaning.** For `forall` with parameters in **`range`** or **`closed_range`**, enumerate values, assume domain facts, run the proof, check conclusions.

**Syntax.** `by for` `:` `prove` `:` single `forall` (only those range forms), then proof steps.

### `by extension`

**Meaning.** Set equality by extensionality (typically mutual inclusion).

**Syntax.** `by extension` `:` `prove` `:` *set* `=` *set* newline, proof.

### `by fn`

**Meaning.** Use the graph / membership characterization of a function you already introduced.

**Syntax.** `by fn` `:` *object*.

### `by fn set`

**Meaning.** Show a function belongs to a **function set** `fn(… conditions …) codomain`.

**Syntax.** `by fn set` `:` *func* `$in fn` *function-set*.

### `by family`

**Meaning.** Use an instantiated **family** (e.g. `family` *name* `(` *args* `)`).

**Syntax.** `by family` `:` *object*.

### `by struct`

**Meaning.** Use the defining data of a **struct** instance.

**Syntax.** `by struct` `:` *object*.

### `by tuple`

**Meaning.** Tuple / product-space reasoning on an object.

**Syntax.** `by tuple` `:` *object*.

---

## Evaluation and files

### `eval`

**Meaning.** Evaluate a call using the **`algo`** attached to a function.

**Syntax.** `eval` *expression* (typically a function application).

### `import`

**Meaning.** Load another module or file path into scope.

**Syntax.** `import` `"path"` [`as` *name*] or `import` *module* [`as` *name*].

### `run_file`

**Meaning.** Run another `.lit` file.

**Syntax.** `run_file` `"path"`.

---

## Local parameters (`let`)

**Meaning.** Introduce names with types (membership in a set, or built-in kinds like `set` / `finite_set` / `nonempty_set`) **without** requiring the checker to prove the ambient set nonempty first; optionally add an indented block of facts that constrain those names (“let … such that …”). Less common than `have` for introducing working variables in proofs.

**Syntax.** `let` *parameter groups with types* `:` newline, then indented facts; the `:` block can be omitted if there are no constraints.

---

## Keyword cheat sheet (first word on a line)

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

Details and edge cases are easiest to see in **`examples/`** alongside the checker behavior you care about.
