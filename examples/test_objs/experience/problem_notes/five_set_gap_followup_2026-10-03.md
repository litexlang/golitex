# Final five set gaps — 2026-10-03

Task: the user requests extension for three family intersections, more explicit indexed-intersection steps, and forall Cartesian-member equality before extension. All five original goals are closed. No trust, AST, Env/Runtime, recursion/search policy or framework change.

## Tracer: singleton Cartesian product

Before, the correct set equality `cart({1}, {2}) = {(1, 2)}` failed search. Shape and coordinates were already checkable, but the old explicit tuple contract demanded a quantified coordinate proof even with a literal peer.

Now the owning source first proves:

```litex
claim:
    ? forall a cart({1}, {2}):
        a = (1, 2)
    tuple_dim(a) = 2
    a[1] = 1
    a[2] = 2
    release thm tuple_equal_from_coordinates(a, (1, 2))
```

It then explicitly transports equality to membership and runs `by extension`. Both tuple dimensions and every literal coordinate remain requirements. Two literal peers retain their existing component comparison; two symbolic peers retain the quantified contract. Two- and three-coordinate positives, both literal-peer orientations, wrong final coordinate and wrong dimension are tested.

## Intersection proof interfaces

The missing upstream member interfaces, rather than set extension itself, blocked the other four goals. The three new reserved entries reuse the existing explicit theorem application/evidence pipeline:

- family_intersect_member(x, family_intersect(F)): nonempty set F, every factor is a set, and x belongs to every set-valued factor.
- family_intersect_member_facts(x, family_intersect(F)): nonempty set F plus known intersection membership produces forall B F with the is_set(B) guard and x in B.
- index_intersect_member(x, index_intersect(I,X,A)): x in X and every indexed fiber membership; existing constructor WD still checks nonempty index, exact callable domain and powerset return carrier.

The source proofs genuinely verify all factors/fibers using finite enumeration. Family P02 still proves factor distinctness by contra first. Family P03 eliminates membership to its empty factor; it does not equate the empty absolute family intersection to {}. Indexed P02 keeps the complete k=1 -> k in N -> singleton subset -> powerset-return proof before declaring A. No special-case equality/value table was added.

## Acceptance

12 builtin_thm Rust tests pass, including all 28 native theorem catalog tracers, negative-premise/shape/empty/domain/rollback checks and tuple dimension/final-coordinate checks. Strict CLI gates pass 3 complete owning files (18 cases), 4 new interface/tuple tracers and 14 nearest negatives. cart(R) intentionally fails parsing at the documented minimum arity; it is not reported as a mathematical rejection. All other negative gates require ordinary failure without a session error.

Five gap sources are retired into their owning positives only after acceptance. Five new persistent negatives cover one-factor insufficiency, empty family, missing fiber, wrong last tuple coordinate and wrong dimension. The existing index_intersect N03 first proves the valid return carrier so the wrong index domain, not a failed prerequisite declaration, is tested.

Current audited inventory has 665 positives, 309 negatives and zero recorded gaps. Concurrent unrelated additions contribute to totals. No whole-corpus, To-Lean or release-package gate is claimed.

The [journal](../../proof_journals/five_set_gap_followup_2026-10-03.json) holds every material attempt, accepted source, retired originals, exact commands, release identities and complete Rust/CLI results. Two initial builds encountered a concurrent witness-diagnostic private-module import error; the other work corrected its public re-export path before the stable build. This task did not change that file.
