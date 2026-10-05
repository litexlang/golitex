# DefStructStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefStructStmt restriction and tooling observations.
- Related workspace: golitex.

These boundary notes are separate from the original K-number issue groups.
The dated observations below distinguish restrictions from unresolved semantics.

### Input: `struct Single:` with only `x R`

- Observed boundary: Parse error: `struct definition expects at least two fields`.
- Supported route: Two-field plain and parametric structs.
- Existing reproductions: [single-field-is-currently-unsupported.lit](../../negative/def_struct_stmt/single-field-is-currently-unsupported.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

## Phantom parameter identity — retested 2026-10-04

Task: user-requested conversation closeout retest. Label: `trust` (semantic
decision, not a demonstrated false mathematical equality). Category: discuss
shared struct carrier semantics before changing the existing contract.

```litex
struct Point<K nonempty_set,S nonempty_set>:
    value S
    tag N
forall t &Point<N,R>:
    t $in &Point<Z,R>
```

Currently passes: K does not occur in a field type. The old template
wrong-carrier negative consequently fails its Rust assertion. The positive
unique-function template now succeeds in both RootExport and Eval. Wrong
object values and missing template guards still reject; an actually used
field parameter retains its type boundary.

Both instances currently describe pairs with `value` in R and `tag` in N,
because K is unused. Explicit extension also proves:

```litex
by extension:
    ? &Point<N,R> = &Point<Z,R>
```

Bare equality and inequality searches both reject; that is weaker automatic
search, not evidence that the sets differ. The maintainer's “different?” reply
also said the original explanation was unclear, so it is not treated as
authorization for a new struct representation. The precise question is whether
the test intended `tag K`, or whether even an unused K must distinguish the
instances. No original wrong-carrier assertion has been removed or relabeled.
The final stable Rust run has 829 passes and this one remaining failed assertion.

Making unused K a separate identity cannot safely be achieved by only blocking
this membership proof: the current literal tuple construction and extension
definition still describe the same field set. No such partial patch is applied.

[Acceptance and raw controls](../../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#phantom).
[Current clarification and extension control](../../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).
[Canonical DEC04](../../../../plan/src收尾总清单.md#dec04).

Back to [issue index](../README.md).

## Serious-bug audit — 2026-10-05

The complete Rust gate now has 933 passes and the same one unused-K negative
assertion failure. No wrong numerical conclusion, strict trust bypass or new
state defect was observed from this example. The original test remains; this
turn does not repeat a semantic question or change struct representation.
Qualified struct parsing is now repaired and its real module/path/carrier
controls pass. [Consolidated acceptance](../../../../tests/tooling/acceptance/conversation-serious-bug-audit-2026-10-05.md).
