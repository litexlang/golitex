# Litex agent primer

A compact onboarding text for an agent that must write Litex. It is meant to be
read once, as a file, instead of loading `Manual.md` or `Learn_Litex.md` into the
conversation.

Use it with [Agent Prompt Authoring](Agent_Prompt_Authoring.md), which explains
the layout, the incremental checking loop and the measured effects. Every
executable snippet below is self-contained. The Facts and Moves galleries are
schematic syntax references; their names and placeholders need a caller's context.

---

One fact per line, checked in order. Accepted lines stay usable; a rejected line
reports an `errors` entry, so fix the rejected statement and continue.

Check incrementally in `litex -lang en -strict -session`, submitting one
top-level statement at a time. Keep the same process after a normal failure.
Run `litex -lang en -strict -f solution.lit` at the final checkpoint. See the
[Agent Guide](AgentGuide.md) for accepted prefixes and deliberate restarts.

## Declarations

```litex
have value R = 2                    # an object with a value
have positive R+                    # a positive real
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

These are independent schematic forms, not consecutive steps of one proof.

```text
a = b = c                               # chain
a <= b < c                              # chain
|a - b| = |b - a|
$P(a)                                   # call a predicate
$P(a) or $Q(a)
exist t R st {0 < t, t < 1}
exist! n N+ st {n^2 = 4}
```

## Moves

Supply the declarations, premises and proof body indicated by each placeholder.

```text
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

These are examples of bounded automatic consequences. Definition unfolding,
nontrivial factoring and longer derivations can still need explicit fact lines
or proof commands.

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

`prop` bodies describe conditions. Put proof commands and claims in a `thm`
body or a `claim:` block.

## Affine combinations and endpoint comparisons

Collapse an affine combination in one line:

```litex
forall a,b,t R:
    (1 - t) * a + t * b = a + t * (b - a)
```

A sign fact then gives the endpoint comparison:

```litex
forall a,b,t R:
    a < b
    t > 0
    =>:
        b - a > 0
        t * (b - a) > 0
        a + t * (b - a) > a
```

Go the other way with a difference bridge: one equality for `x - a` plus a sign
fact for that difference is enough, and `x > a` follows.

```litex
forall a,b,t,x R:
    a < b
    t > 0
    x - a = t * (b - a)
    =>:
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
have x R = 1
x^2 + x = 1 + 1 = 2
x^2 + x >= 2
```

Rejected goal `forall x R: sqrt(x^2) = x`: it is false for negative `x`, so
the goal needs the domain condition:

```litex
claim:
    ? forall x R:
        x >= 0
        =>:
            sqrt(x^2) = x
    sqrt(x^2) = x
```

## Working style

Submit one declaration or proof statement, read its JSON result, then continue
in the same Session. Structure the file so that you can append: definitions and
helper lemmas first, then the theorem. Inserting a lemma above accepted lines
requires deliberately restarting and replaying the accepted prefix. A rejected
line tells you which check failed; add
the missing fact in the live Session before retrying it. Run the saved file's
clean strict gate before you finish.

