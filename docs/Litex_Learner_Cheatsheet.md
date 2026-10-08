# Litex Learner Cheatsheet

Choose the next declaration, proof step, or repair from this page. Litex checks
statements in source order; accepted objects and facts become context for later
statements. Every runnable block below is self-contained.

For installation use [setup](setup.md). The [Manual](Manual.md) owns the exact
language contracts; [CLI](cli.md) owns commands and output.

## Find your next move

| I need to… | Start here |
| --- | --- |
| Introduce a value, function, or condition | [Choose a statement](#choose-a-statement) |
| State hypotheses and a conclusion | [Write facts and hypotheses](#write-facts-and-hypotheses) |
| Define something and prove a law about it | [Definition → theorem → use](#definition--theorem--use) |
| Give or extract a witness | [Existence and scope](#existence-and-scope) |
| Choose a proof method | [Proof actions](#proof-actions) |
| Understand a failed statement | [Common places to get stuck](#common-places-to-get-stuck) |
| Look up number sets, indices, or structures | [Objects and domains](#objects-and-domains) |
| Run a file and inspect its result | [Run and read feedback](#run-and-read-feedback) |

## The working model

```litex
have x R = 2
x + 1 = 3
x^2 = 4
```

`have` introduces the real object and its value. Each following fact is checked
and, on success, becomes available to the next statement.

| Category | Example | Job |
| --- | --- | --- |
| Object | `x`, `R`, `{1, 2}`, `x + 1` | A mathematical value or expression. |
| Fact | `x = 2`, `x $in R`, `$P(x)` | A proposition about objects. |
| Statement | `have`, `prop`, a bare fact, `claim` | Introduce, define, or check information. |
| Feedback | `success`, `proof_method`, `stores`, `why_failed` | Explain the outcome and usable context. |

Before writing a line, identify its objects, their domains, and the exact fact
needed next. Inspect existing builtin and module interfaces before declaring a
new mathematical concept.

## Choose a statement

The forms below are schematic; `S`, `T`, `value`, and `goal` stand for your
actual objects and facts.

| Later code needs | Form | What it contributes |
| --- | --- | --- |
| An arbitrary member | `have x S` | A name and membership; requires nonemptiness. |
| A value with a declared carrier | `have x S = value` | Checks `value $in S`; records membership and equality. |
| A name for an expression | `let name = value` | An equality alias, not mutable assignment. |
| A callable value | `have fn f(x S) T = body` | A function with its domain, output carrier, and equation. |
| A named mathematical condition | `prop P(x S): facts` | A definition; assert an instance as `$P(a)`. |
| A local derivation | `claim: ? goal` | Proves and exports its goal; helpers stay local. |
| A named reusable result | `thm name: ? goal` | Proves the fact and gives it a citation interface. |

A condition and a value have different uses. This definition establishes the
particular instance by checking its body:

```litex
prop is_above_two(t R):
    t > 2
by def $is_above_two(3)
```

Declaring `prop` alone proves no instances. `abstract_prop` supplies only a
signature. If the next line needs `f(x)`, define a callable function rather
than encoding that value as a predicate. See [R02](Manual.md#r02-choose-the-language-form-by-mathematical-role).

## Write facts and hypotheses

| Mathematical shape | Form |
| --- | --- |
| Equality, order, membership | `a = b`, `a <= b`, `a $in S` |
| A named property | `$P(a)` |
| A chain of adjacent facts | `a = b = c`, `a <= b < c` |
| Conjunction or alternatives | `$P(a) and $Q(a)`, `$P(a) or $Q(a)` |
| Existence / unique existence | `exist x S st {facts}`, `exist! x S st {facts}` |
| Universal result | `forall x S:` with indented facts |

In a conditional universal, hypotheses precede `=>:` and conclusions follow it:

```litex
forall x R:
    x > 0
    =>:
        x != 0
```

Without the arrow, all listed facts are conclusions. A premise-free universal
lists its conclusions directly. `forall` binders and premises are local; they
do not introduce global objects or global assumptions.

A bare `forall` body contains facts. Commands such as `witness`, `by def`, and
`release thm` belong in a proof body. Use one header for universal conclusion
parameters; consult the [fact contracts](Manual.md#factual-statements) before
nesting quantifiers. Flat `and`/`or` forms are not an arbitrary Boolean grammar.

## Definition → theorem → use

The reciprocal's nonzero condition belongs to its callable domain. The named
theorem uses its active goal binder and exposes the defining equation:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
thm reciprocal_product:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1

release thm reciprocal_product(2)
reciprocal(2) * 4 = (reciprocal(2) * 2) * 2 = 1 * 2 = 2
```

Read this as a domain contract, a proved universal law, an explicit instance,
and a subsequent calculation. The theorem's `x` is local; use it directly in
the proof body. Every theorem call still checks its arguments and premises.

| Citation | Effect |
| --- | --- |
| `release thm name(args)` | Instantiate a root `forall` theorem and publish all conclusions. |
| `by thm name(args) => fact` | Select one directly returned atomic conclusion, without rewriting it. |
| `release thm name` | Cite a named non-`forall` theorem fact. |

A zero-parameter root `forall` still uses `name()`. Selection cannot target a
chain, conjunction, existential, or universal fact; release the result and use
explicit subsequent steps. Avoid repeating an already published conclusion
unless it performs a necessary representation change.

See [R01](Manual.md#r01-define-and-use-a-reciprocal-function),
[P05](Manual.md#p05-a-function-equation-may-need-to-be-exposed-before-substitution),
and the [theorem-call contract](Manual.md#theorem-fact-shapes-and-call-spelling).

## Existence and scope

To prove existence, give a satisfying witness. To use an existence fact that
verifies, extract a fresh name with `obtain`:

```litex
witness exist w R st {w^2 = 4} from 2
obtain root from exist w R st {w^2 = 4}
root^2 = 4
```

`obtain` checks its source; it cannot invent an unproved witness. The binder
`w` is local to the existential. The new name `root` belongs to the surrounding
scope. Add a witness proof body when it performs real intermediate reasoning.

In “for every `x`, there is a `y`”, choose the witness inside the active `x`
scope. A claim activates its goal's binders and exports the completed goal:

```litex
claim:
    ? forall x R:
        exist y R st {y = x + 1}
    witness exist y R st {y = x + 1} from x + 1
```

The claim does not export a global `x` or `y`. Unique existence additionally
requires uniqueness: `2` is a witness for `w^2 = 4`, but `-2` is another one.
A genuinely unique specification can be checked directly:

```litex
witness exist! w R st {w = 2} from 2
```

See [witnesses](Manual.md#s35-existential-witnesses),
[unique witnesses](Manual.md#s36-unique-existential-witnesses), and
[local claims](Manual.md#s33-local-claims).

<a id="6-small-proofs-write-the-route-only-when-needed"></a>

## Proof actions

State a direct target first when ordinary verification can establish it. For a
proof needing an explicit mathematical move, choose the corresponding action.
The entries below are abbreviated forms, not complete runnable programs.

| Needed move | Action | Contract/example |
| --- | --- | --- |
| Use a positive concrete definition | `by def $P(args)` | [S47](Manual.md#s47-explicit-definition-folding) |
| Cite a named result | `release thm` / selected `by thm` | [S25–S26](Manual.md#s25-publish-theorem-conclusions) |
| Supply / extract a witness | `witness` / `obtain` | [Existence](#existence-and-scope) |
| Prove a common result in exhaustive branches | `by cases:` | [S39](Manual.md#s39-proof-by-exhaustive-cases) |
| Derive a contradiction from the classified opposite | `by contra:` ending in `impossible` | [S40](Manual.md#s40-proof-by-contradiction) |
| Check a displayed finite set | `by enumerate finite_set:` | [S41](Manual.md#s41-finite-set-enumeration) |
| Iterate a concrete integer range | `by for:` | [S44](Manual.md#s44-finite-range-iteration) |
| Prove a natural-number invariant | `by induc n from lower:` | [S42](Manual.md#s42-ordinary-induction) |
| Use all earlier induction cases | `by strong_induc n from lower:` | [S43](Manual.md#s43-strong-induction) |
| Prove set / function equality | `by extension` / `by fn_extension` | [S45–S46](Manual.md#s45-set-extensionality) |

Finite enumeration checks each permitted assignment and its local premises:

```litex
by enumerate finite_set:
    ? forall x {1, 2}:
        x > 0
```

An induction supplies a base and successor step. The induction hypothesis is
available only in the step; proof helpers remain inside their case:

```litex
claim:
    ? forall n N:
        2^n >= n + 1
    by induc n from 0:
        ? 2^n >= n + 1
        ? from n = 0:
            2^n = 1 = n + 1
        ? induc:
            2^(n + 1) = 2^n * 2^1 = 2^n * 2
            2^n * 2 >= (n + 1) * 2
            (n + 1) * 2 = (n + 1) + (n + 1) >= (n + 1) + 1
            2^(n + 1) = 2^n * 2 >= (n + 1) * 2 >= (n + 1) + 1
```

## Common places to get stuck

Read the earliest stopping phase before changing the proof. These rejected
blocks are intentional boundary examples and are excluded from positive tests.

### An arbitrary member has no chosen value

**Expected search miss (`search_proof`):**

<!-- litex:skip-test -->
```litex
have x R
x = 0
```

The declaration establishes real membership, not `x = 0` or `x != 0`. If the
intended object is zero, introduce that value explicitly:

```litex
have x R = 0
x + 1 = 1
```

### An expression must be meaningful on its whole domain

**Expected function-body failure (`have_fn_equal`):**

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R) R = 1 / x
```

The domain includes zero. For the partial reciprocal, use the guarded
[definition above](#definition--theorem--use). A function with a value at zero
needs a definition specifying it. The same check applies to argument carriers
and index bounds; preserve the intended mathematical domain during repair.

### A fact list cannot execute a proof command

**Expected parse error:**

<!-- litex:skip-test -->
```litex
forall x R:
    witness exist y R st {y = x + 1} from x + 1
```

Use the [claim form](#existence-and-scope), whose proof body can execute the
command with the goal binder active.

| When later code stops | Inspect next |
| --- | --- |
| A function application fails WD | Its exact input carrier and guards; a known value equation does not waive them. |
| A larger equality misses | Expose the changed subterm or defining equation, then connect the outer expression. |
| `$P(a)` is unproved | Establish the definition's clauses; declaring `prop` supplied vocabulary only. |
| `exist!` fails | Check uniqueness as well as the witness body. |
| A name disappears after a proof | The goal is exported; its local binders and helpers are not. |
| A theorem selection fails | Match a returned atomic conclusion structurally; rewrite in a separate step. |

See the [pitfall cards](Manual.md#pitfalls-and-missing-proof-steps) for checked
rejections and their nearest repairs. A search miss does not refute a fact and
does not by itself establish a kernel bug. `trust` assumes a fact; it leaves
proof debt rather than repairing a verification route.

## Objects and domains

| Object family | Useful forms and boundaries |
| --- | --- |
| Number sets | `N`, `Z`, `Q`, `R`, `C`; `N` includes zero, `N+` is positive. |
| Signed/nonzero sets | For example `R+`, `R-`, `R*`, `C*`; use documented spellings. |
| Sets | `{1, 2}`, `{x R: x > 0}`, `union(A, B)`, `power_set(S)`; a builder is bounded by its carrier. |
| Membership and inclusion | `x $in S`, `A $subset B`; inclusion and equality have different obligations. |
| Functions | `fn(x R) R`, guarded domains, `fn_range(f)`; carriers and guards constrain each call. |
| Tuples/sequences | `(a, b)`, `cart(R, R)`, `finite_seq(S,n)`, `seq(S)`; indices start at 1. `release tuple def t` publishes the exact finite-sequence membership and coordinates; `release cart def cart(A,B)` publishes the complete set definition. See [S52](Manual.md#s52-release-a-tuple-definition). |
| Exact computation | `eval expression` checks domains and publishes the verified source/result equality. |

Function parameter carriers and the return carrier use the enclosing scope;
they cannot refer to that signature's own parameters. Guards and the body can.
For example, `fn(x R: x > 0) R {x + 1}` has a guard-dependent domain. Do not
infer arbitrary dependent function signatures from ordinary `forall` binder
dependencies. See [S01](Manual.md#s01-expression-defined-functions).

A struct is useful when a mathematical structure must be a value with fields:

```litex
struct Point:
    x R
    y R
have p &Point = (1, 2)
release struct def p
p.x = p(1) = 1
p.y = p(2) = 2
```

Use [structs](Manual.md#s16-structured-carriers) and
[templates](Manual.md#s17-parameterized-declaration-families) for the exact construction
and law contracts. Existing builtin concepts need no local redefinition.

## Supported syntax and recommended writing

| Supported spelling | Recommended for new ordinary examples |
| --- | --- |
| Bare `by thm name(args)` | `release thm name(args)` for an unselected call. |
| Inline `forall x R: x > 0 => x != 0` | Multiline `forall` with visible hypotheses and conclusions. |
| Documented Unicode aliases | ASCII keywords and operators for typing, searching, and diagnostics. |

These are preferences, not parser restrictions. Keep `by thm ... => fact` for
selection. `×` denotes Cartesian product; numerical multiplication is `*`.
`⊂` is proper subset, while `⊆` is non-strict subset. Check the
[alias reference](Manual.md#unicode-mathematical-input-aliases-preview).

Write `-(x^2)` for the negative of a square, `(-x)^2` for the square of a
negative value, and `x^(-1)` for a negative exponent. Prefer a direct
`by def $P(args)` and a bodyless witness when their obligations already verify.
Keep intermediate facts when they perform an actual derivation or necessary
bridge.

## Run and read feedback

```bash
litex -lang en -e '1 + 1 = 2'
litex -lang en -strict -f path/to/file.lit
litex -lang en -strict -r path/to/project
```

In a source checkout, build with `cargo build --release` and use
`target/release/litex`. `-f` mounts its direct parent's `litex.config` when
present and runs the configured prefix through that file; otherwise it runs
the file alone. `-r` checks a complete configured project.

Use `litex` for the REPL or `litex -session -f path/to/file.lit` to continue a
successful file run. End an indented REPL block with a blank line. Session
output contains interactive text; use a separate batch command for a final
JSON check.

For machine readers, use `-lang en`. Require exit 0 and these fields in the
batch envelope (other fields omitted here):

```json
{
  "kind": "run",
  "success": true,
  "session_error": null
}
```

| Outcome | Next action |
| --- | --- |
| Success | Inspect `proof_method`, `stores`, and `infers` when deciding what to reuse. |
| Statement `success: false` | Read `why_failed.phase` and `why_failed.goal`; the failed statement adds no successful facts. Earlier accepted statements remain usable. |
| Non-null `session_error` | Read the hard error; the current run/session stops. |

A soft-failed statement makes the overall batch fail even if later statements
succeed. Do not infer success from nested evidence text or treat a failed
assertion as its negation. See [CLI outcomes](cli.md#statement-outcomes).

`-strict` rejects executed user `trust`, `trust have`, and `axiom`, including
dependencies. Abstract predicate signatures and named foundation releases
remain allowed. Verification still depends on the checker, builtin/inference
rules, and loaded mathematics; report explicit assumptions and unresolved
proof debt accurately. See the [trust contract](Manual.md#trust-and-strict-mode).

For larger developments, follow the relevant module's `README.md` and
`math_collections.md`, then consult [examples](../examples/README.md) and
[math showcases](../showcases/math_concepts_in_litex/README.md).

Verification of this revision is recorded in the
[focused audit](audits/learner-cheatsheet-redesign-2026-10-07.json).
