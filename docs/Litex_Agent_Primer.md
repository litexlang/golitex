# Litex agent primer

A compact onboarding text for an agent that must write Litex. It is meant to be
read once, as a file, instead of loading `Manual.md` or `Learn_Litex.md` into the
conversation. The same content is bundled with the project skill
`.agents/skills/litex-formalizer/`.

Use it with [Agent Prompt Authoring](Agent_Prompt_Authoring.md), which explains
the layout, the incremental checking loop and the measured effects. Every
snippet below is a pattern the current release accepts; replace the names, not
the shapes.

---

One fact per line, checked in order. Accepted lines stay usable; a rejected line
reports `why_failed`, so fix forward, never rewrite.

Check incrementally: append to `solution.lit`, then run `./step`. It sends only
the new statements to a live session, so a statement costs milliseconds and one
short line of output. `./check solution.lit` once at the end is the whole-file
strict gate. Never re-run the whole file after every line: that re-checks and
re-prints everything and is the main way a Litex session becomes expensive.

## Declarations

```litex
have x R = 2                        # an object with a value
have x R+                           # a positive real
have fn f(x R: x != 0) R = 1 / x    # function; after the `:` are its domain conditions
have fn sq(A, B cart(R, R)) R = (B(1) - A(1))^2 + (B(2) - A(2))^2

prop P(a, b R):                     # predicate = a list of conditions
    a > 0
    b > a
```

`R R+ N N+ Z Q` are the number domains. `cart(R, R)` is a pair; use `p(1)`,
`p(2)` for its coordinates.

## A theorem is a goal plus fact lines

```litex
thm name:
    ? forall x R:
        x > 0
        =>:
            x + 1 > 0
    x + 1 > 0
```

The goal after `?` is checked exactly as written; it cannot be weakened. Each
following indented line is a fact that must be provable from what came before.

## Facts

```litex
a = b = c                               # chain
a <= b < c                              # chain
|a - b| = |b - a|
$P(a)                                   # call a predicate
$P(a) or $Q(a)
exist t R st {0 < t, t < 1}
exist! n N+ st {n^2 = 4}
```

## Moves

```litex
by def $P(a)                            # publish the predicate's conditions
release thm name(a)                     # instantiate a root-`forall` theorem
by thm name(a) => fact                  # one atomic conclusion
witness exist x R st {x^2 = 4} from 2   # prove an existence
obtain t from exist t R st {...}        # consume an existence already available
by cases:                               # split an `or` fact already in context
    ? <goal>
    case $P(a):
        ...
by contra:                              # assume the negation, end in `impossible`
    ? <goal>
    ...
    impossible <contradiction>
```

## What the checker infers

* `a + k = b + k` publishes `a = b`.
* `a * k = b * k` publishes `a = b` when `k != 0`.
* `a / k = b / k` publishes `a = b` when `k != 0`.
* Chained equalities substitute into later lines.
* `sqrt(x^2) = x` is accepted directly when `x >= 0`; do not unfold `sqrt`.

Nothing else is automatic. Expansion, factoring, substitution of a function
body, and moving terms across `=` need their own fact line.

## Unique existence, in full

`exist!` needs a witness plus a uniqueness claim; the goal is written directly
on the `thm`:

```litex
thm t:
    ? exist! n N+ st {n^2 = 4}
    witness exist! n N+ st {n^2 = 4} from 2:
        2^2 = 4
        claim:
            ? forall u, v N+:
                u^2 = 4
                v^2 = 4
                =>:
                    u = v
            u^2 = v^2
            u = v
```

`prop` bodies are condition lists only. They cannot hold `exist`, `forall`, or
any claim; writing one there gives `expected '(' ...`. Put claims in a `thm`
goal or in a `claim:` block.

## Affine combinations and endpoint comparisons

Collapse an affine combination in one line:

```litex
(1 - t) * a + t * b = a + t * (b - a)
```

A sign fact then gives the endpoint comparison:

```litex
b - a > 0
t * (b - a) > 0
a + t * (b - a) > a
```

Go the other way with a difference bridge: one equality for `x - a` plus a sign
fact for that difference is enough, and `x > a` follows.

```litex
x - a = t * (b - a)
t * (b - a) > 0
x - a > 0
x > a
```

Do not expand such a step into many small rewrites. One equality line can carry
the whole polynomial identity.

## Two feedback turns

Rejected line `x^2 + x >= 2` alone inside a case: `why_failed` says
`Could not prove the goal`. Write the value first:

```litex
x^2 + x = 1 + 1 = 2
x^2 + x >= 2
```

Rejected goal `forall x R: sqrt(x^2) = x`: it is false for negative `x`, so
the goal needs the domain condition:

```litex
? forall x R:
    x >= 0
    =>:
        sqrt(x^2) = x
sqrt(x^2) = x
```

## Working style

Append one declaration or a few related facts, run `./step`, read the one-line
result, then continue. Structure the file so that you can append: definitions and
helper lemmas first, then the theorem. Inserting a lemma above accepted lines
forces a full re-check. A rejected line tells you exactly which check failed; add
the missing fact before it instead of restructuring the file. If `./step` prints
`RESYNC`, you rewrote earlier lines and the whole file was re-checked; prefer
appending. Run `./check solution.lit` once before you finish.

