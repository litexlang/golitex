# Litex Proof Style

Use direct, local mathematical steps. Every Litex line must express a genuine
mathematical move or the smallest verifier-proven bridge; being checkable from
the current context is not by itself a reason to write the line.

## Contents

- [Proof Spine Before Syntax](#proof-spine-before-syntax)
- [Proof Liveness and Fact Cascades](#proof-liveness-and-fact-cascades)
- [Equality Chains](#equality-chains)
- [Same-Context / Cancellation Chains](#same-context--cancellation-chains)
- [Zero Product](#zero-product)
- [`trust` Policy](#trust-policy)

## Proof Spine Before Syntax

Before formalization, write a short ordinary-language proof at the abstraction
level used in normal mathematical practice. Then map each Litex block back to
one of its steps. A runnable proof is still badly shaped when it manually
reimplements a construction or theorem that the mathematical proof simply
cites.

For example, suppose bijectivity gives `f : N -> X` and the target asks for an
injection `X -> N`. The concise proof spine is:

1. take the inverse `g : X -> N` of the bijection `f`;
2. use that the inverse of a bijection is injective, and witness `g`.

The injectivity of `f` alone has the wrong direction and does not close the
goal. But manually defining `g` by unique preimages, reproving existence and
uniqueness for every `x`, and then reproving inverse injectivity is also the
wrong final abstraction when an inverse-function interface already exists.
Use that interface. If the library exposes only a unique-preimage theorem, use
it to discharge the selection step instead of replaying its proof. If no
inverse interface exists, record a general-interface gap rather than treating
the repeated local reconstruction as desirable proof style.

After verification, ask:

- Which natural-language step does each code block implement?
- Is any block proving a fact already packaged by an earlier theorem or
  definition?
- Did a verifier workaround silently become the apparent mathematics?
- Can a lower-level block be replaced by one named interface and still verify?
- Does the final proof expose roughly the same decisive moves as the proof
  spine?

## Proof Liveness and Fact Cascades

Do not accept a proof merely because every line verifies or because every fact
appears to have a later consumer. Generated proofs often materialize the
verifier's internal route instead of expressing the mathematical argument.
Call this **proof-trace redundancy** and distinguish:

- an **inference echo**, which repeats a fact already stored or inferred;
- a **dead fact** or **dead chain**, which does not reach any live output; and
- a **bypassable derivation chain**, whose lines consume one another but whose
  final useful fact is reachable without the chain.

For example, a proof may expand one set declaration into a fact cascade:

```litex
have S power_set(N) = {n X: n <= a}
S = {n X: n <= a}
a <= a
a $in {n X: n <= a}
a $in S
finite_set_min(S) $in S
finite_set_min(S) <= a
```

The later lines are not justified merely because each can feed the next one.
Test whether the declaration, the ambient facts about `a`, and the
`finite_set_min` interface already discharge the live downstream obligations.
If so, delete the entire cascade. This catches the common failure that an
ordinary unused-variable scan misses.

After a candidate proof verifies, run this audit:

1. Write down the live outputs: the theorem goal, required witnesses, exported
   claim conclusions, and source-facing calculations worth showing.
2. Walk backward and mark only facts needed to reach those outputs. Delete
   unmarked facts and subproofs.
3. For every surviving chain of definition unfolding, reflexivity, membership
   conversion, theorem-result repetition, or predicate folding, ask whether
   its endpoint follows directly from the context before the chain.
4. Delete the whole chain in the real enclosing `try:` context. Do not test
   only one isolated line: removing a complete bypassable path can succeed
   even when removing one of its locally consumed links fails.
5. If the shorter form fails, add back the smallest exact bridge indicated by
   verifier evidence. Do not restore the original waterfall wholesale.
6. Run the final file or project checkpoint. A fact graph or lexical search is
   only a candidate finder because inferred dependencies may be absent.

The final Litex blocks should correspond closely to the ordinary-language
proof spine. Keep a pedagogically meaningful estimate, case split, witness, or
named theorem application; remove the trace by which the verifier happened to
rediscover its automatic consequences.

## Reader Bridges After `by thm`

An explicit fact immediately after a theorem call is not automatically an
echo. Keep it when it tells the reader which returned conclusion matters,
which concrete source object a generic theorem has been instantiated at, or
which predicate or representation the next step consumes:

```litex
by thm closure_of_bounded_intervals(a, b)
closure_of_real_set('[a, b]) = '[a, b]
$is_closed_subset('[a, b])
```

The middle line is a reader bridge from the named closure theorem to the
defined closed-set predicate. In contrast, this final line adds no transition:

```litex
claim:
    ? P
    by thm p()
    P
```

Delete the pure goal echo. Usually retain at most one result line per theorem
call; a source-facing aggregation theorem may expose several distinct results
returned by one call.

## Proof-Spine Alignment Example

For uniqueness of an additive inverse, the natural proof has two moves: choose
one inverse for existence, then compare two inverses by one chain through
`y2 + (x + y1)`. The formal uniqueness block should therefore be one equality
chain, not separate logs for every use of commutativity, associativity, and the
zero law. If Litex cannot rewrite `x + y2` inside `(x + y2) + y1`, keep the one
explicit inner equality needed to seed that rewrite, then write the full
mathematical chain. This is a `verifier_bridge`; the surrounding law-by-law
cascade is not.

## Formalize Easy Examples

Do not use prose as a substitute for an easy textbook example. Add a `sketch:`
that states the example's actual objects and claims, or give it a checked
theorem when the proof is direct. The source comment may explain the example,
but a comment-only numerical or endpoint illustration is incomplete
translation coverage.

## Equality Chains

Prefer chains like:

```litex
a = b = c = d
```

When a jump fails, split it:

```litex
(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 3^2 - (2 * sqrt(2))^2
(2 * sqrt(2))^2 = 8
3^2 - (2 * sqrt(2))^2 = 9 - 8 = 1
```

## Same-Context / Cancellation Chains

When a proof applies the same algebraic context to both sides of an equality
or cancels a shared term, prefer one compact chain instead of several
one-step facts plus a final equality:

```litex
n = (n + 1) - 1 = succ(n) - 1 = succ(m) - 1 = (m + 1) - 1 = m
b = (a + b) - a = (a + c) - a = c
n = (n + k) - k = (m + k) - k = m
```

Use a named cancellation theorem when the cancellation is not the main proof
move, or when an existing local theorem already expresses the repeated step.
Do not add a new theorem just to avoid a short readable chain.

## Zero Product

If `u * v = 0` and `v != 0`, prefer:

```litex
u = 0 / v
u = 0 / v = 0
```

## `trust` Policy

Do not use `trust` to finish an example that should be checkable. Once a real
blocker is identified, keep `trust` on the narrowest blocked substep, document
the debt, and continue. A declaration containing `trust` is not `checkable`.
