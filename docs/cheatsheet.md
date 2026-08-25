# Litex Cheat Sheet

Use this page while writing Litex and deciding what to try next. It is a quick
authoring index, not the language specification. The [Manual](Manual.md) is
canonical; [Examples](Examples.md) provides complete, runnable patterns; and
the [CLI reference](cli.md) defines command behavior.

## Start With One Checked Fact

```litex
prop is_one(x R):
    x = 1

1 = 1
by def $is_one(1)
```

Read this bottom-up: establish ordinary facts, ask Litex to check them in the
current context, and reuse accepted facts later. Reach for a proof command only
when stating the target directly is not enough.

## Choose What To Introduce

| What later code needs | Use | Remember |
|---|---|---|
| An arbitrary object in a nonempty set | `have x S` | Introduces `x` and `x $in S` |
| A local abbreviation for an already well-defined object | `let name = value` | Stores `name = value`; it does not define a carrier |
| A name for a specific value | `have x S = value` | Checks the carrier and stores the equality |
| A callable value | `have fn f(x S) T = body` | Use a function, not a predicate encoding its graph |
| A concrete named property | `prop P(x S): ...` | Gives a definition that `by def` can fold |
| An external property interface | `abstract_prop P(x)` | Declares no defining facts and proves no instance |
| One nearby derived fact | `claim:` with an indented `? fact` | Keeps proof machinery local |
| A stable reusable result | `thm name: ...` | Creates a named theorem interface and stores its universal fact |
| An explicit assumption | `trust fact` | Creates trust debt; strict mode rejects it |

Use `have` when later code must cite a value, `have fn` when it must call a
value, `prop` when it must assert `$P(args)`, and `thm` when the result deserves
a reusable mathematical name. Do not promote a one-proof helper without a real
second consumer.

Name a repeated nontrivial object when the proof treats it as one mathematical
atom, and choose a role-based name such as `event_union` or
`probability_terms`. Use `let` for a pure local abbreviation and typed `have`
when the carrier is itself useful evidence. Do not name by character count:
keep one-use transparent calculations expanded, use `prop` for long facts, and
improve a shared `setting`, `struct`, template, or function interface when the
same parameter bundle recurs across independent proofs. If an inner alias
would require repeated transport under a larger constructor, name that outer
mathematical object instead.

## Write The Fact Shape

| Mathematical shape | Common Litex shape |
|---|---|
| Atomic fact | `a = b`, `a $in A`, `$P(a)` |
| Equality or order chain | `a <= b = c < d` |
| Flat conjunction | `atomic and atomic` |
| Outer disjunction | `branch or branch` |
| Existence | `exist x S st {facts}` |
| Unique existence | `exist! x S st {facts}` |
| Universal fact | `forall x S: assumption => conclusion` or the indented block form |
| Negated quantified fact | `not exist ...` or `not forall ...` |

`and` is a flat list of atomic facts; `or` joins supported completed branches.
Neither is a general recursively nested Boolean grammar. If an existential or
set-builder body needs a quantified condition, name that condition with a
concrete `prop` and place its atomic call in the body.

Declare every parameter of a universal conclusion in one `forall` header. A
conclusion cannot itself be another `forall`; write `forall x X, y Y: ...`
instead of placing `forall y Y` inside the conclusion for `x`.

## Parenthesize Negatives Around Powers

Never use `-t^2` as an allegedly unambiguous Litex expression. Make the syntax
tree visible whenever prefix `-` meets exponentiation:

| Intended mathematics | Required authoring shape |
|---|---|
| Opposite of the square | `-(t^2)` or `-1 * (t^2)` |
| Square of the negative value | `(-t)^2` |
| Negative exponent | `t^(-1)` |

The same rule applies inside larger products and sums. Automated authoring
agents must insert these parentheses rather than infer an unstated intention.

## Choose The Proof Action

| Goal or available fact | Try first | Boundary |
|---|---|---|
| A direct carrier, arithmetic, equality, membership, or inferred consequence | State the target directly | Do not wrap a fact Litex already knows |
| A positive concrete predicate whose body is proved | `by def $P(args)` | Folds only the matching positive definition target |
| Properties of a definition-owned struct expression | `by struct def expression` | Verifies membership, then opens exactly one layer; direct `x &Struct` symbols are the only automatic case |
| One atomic consequence of a named theorem | `by thm name(args) => fact` | Use bare `by thm` when several conclusions are needed |
| A semantic constructor with compound requirements | Its reserved `by thm` interface | One-layer automation does not invent quantified premises |
| An existential target | `witness ... from ...` | Match the target's witnesses and carriers exactly |
| A known existential whose witnesses are needed | `obtain ... from ...` | The source existential must already be known |
| A universal fact over `range` / `closed_range` | `by for` | This is bounded integer iteration, not arbitrary quantifier automation |
| A universal fact over displayed finite domains | `by enumerate finite_set` | Every quantified domain must be concretely enumerable |
| A known member of an integer range | `by enumerate range` / `by enumerate closed_range` | Produces equality alternatives for that member |
| Equality of two sets | `by extension` | Prove both membership directions; use the function route for functions |
| A known disjunction or exposed alternatives | `by cases` | Cases must come from an exhaustive source already in context |
| A negative or contradiction-shaped goal | `by contra` | End with an actual contradiction and `impossible` |
| A discrete or finite-set invariant | `by induc` / `by strong_induc` | The parameter, base, and invariant must match a supported shape |
| A universal proof that needs cases, theorem calls, witnesses, or induction | Wrap it in `claim`, or use `thm` when reusable | Do not put proof-control commands in a bare `forall` conclusion list |

Use this search order:

1. State the ordinary mathematical move.
2. Try the exact target as a known, builtin, or inferred fact.
3. Choose the matching proof action above.
4. Search the standard library and nearby source for an existing interface.
5. Add the smallest intermediate equality, carrier fact, or theorem call that
   the verifier demonstrates is necessary.
6. Write a manual proof spine only after the native route and existing
   interfaces genuinely do not fit.

For exact syntax, generated subgoals, and runnable variants, follow the
Manual's [Proof Process](Manual.md#proof-process) chapter and the
[proof-pattern examples](Examples.md#proof-patterns).

## Triage A Failure

| First failing phase | Check next | Do not conclude yet |
|---|---|---|
| Parse | Indentation, binder syntax, delimiters, and supported fact nesting | The mathematics is unsupported |
| Name or type resolution | Imports, spelling, arity, callable metadata, and exact carrier | A theorem is missing |
| Well-definedness | Domain membership, nonzero divisors, index bounds, and argument well-definedness | The target is false |
| Verification returns `unknown` | Known facts, one native proof action, an existing interface, then one small bridge fact | `trust` is required |
| A statement verifies but later use fails | What fact or object was stored, and whether it is callable or executable | The earlier statement had no effect |

For an algebraic failure, split one large jump into a short equality chain. For
rewriting inside a function, sequence, sum, product, or recursive call, prove
the changed inner value or index first.

## Five Journal-Backed Repair Tracers

These routes summarize repeated failed-to-repaired transitions in proof
journals. They are authoring decisions, not new language rules: first match the
earliest phase, then try the smallest indicated change in the real caller.

| Symptom | Next move | Keep this boundary | Runnable pair |
|---|---|---|---|
| The parser rejects a plausible mathematical move | Put the same move on a current proof surface such as `claim:` plus an indented `?` goal | Reaching proof verification does not prove the goal | [Phase first](Examples.md#phase-first-repair-the-surface-before-the-proof) |
| A definition or application is not well-defined | Establish the exact argument carrier, index bound, divisor premise, or typed construction first | Do not retain carrier echoes whose deletion still passes | [Carrier first](Examples.md#carrier-first-make-the-object-legal-before-proving-with-it) |
| One compound equality or comparison is `unknown` | State the smallest changed inner value once, then continue with one outer equality or order chain | Preserve an inner representation equation when a deletion probe breaks its consumer | [Inside out](Examples.md#inside-out-rewrite-the-smallest-changed-subterm-first) |
| The proof passes but reads like a verifier trace | Delete theorem-result echoes, witness-body repeats, and endpoint logs one class at a time | Restore only the first exact bridge whose removal fails in context | [Proof liveness](Examples.md#liveness-delete-echoes-but-keep-a-proven-live-bridge) |
| Later code must apply data that was introduced only as a set-shaped value | Expose the exact `fn` interface, or construct the refined value before selecting it | A passing implementation is still wrong if it changes the source-facing domain | [Interface fidelity](Examples.md#interface-fidelity-make-callable-data-callable-without-changing-the-object) |

The first four rows are ready for held-out behavior evaluation. Interface
fidelity still needs its historical boundary refreshed by a current clean
file gate before it can be considered for permanent skill promotion.

## Run And Inspect

| Need | Command |
|---|---|
| Check one source string | `litex -e '1 = 1'` |
| Check a registered project file | `litex -f path/to/file.lit` |
| Check a standalone scratch file and exit | `litex -runner -isolated -f scratch.lit` |
| Get one machine-readable result | `litex -runner -f path/to/file.lit` |
| Inspect full failure phases | `litex -detail -f path/to/file.lit` |
| Audit a complete project and reject explicit trust | `litex -strict -runner -r path/to/project` |
| Probe repeatedly before one registered file | `litex -compact -session -before path/to/file.lit` |

`-f` requires a `litex.config` in the file's direct parent. Use `-isolated -f`
for a standalone file, `-r` for a project's complete export tree, `-runner`
for scripts and CI, and `-strict` for a full dependency and trust audit. See
[CLI](cli.md) for precise loading, output, exit-code, and session contracts.

## Hard Boundaries

- `by def` folds a definition; it is not general proof automation.
- `by struct def e` needs an existing definition-owned view; later membership alone cannot select one.
- `claim` proves a fact; it does not introduce a callable object.
- `prop` names a property; it does not replace `have` or `have fn`.
- An explicit theorem selection should not be followed by the identical fact
  as an echo.
- `unknown` calls for phase classification and the next smallest bridge before
  proof debt.
- Code containing `trust`, `trust have`, or `axiom` is not fully checkable.

When this page and the Manual appear to disagree, follow the Manual and report
the stale cheat-sheet entry.
