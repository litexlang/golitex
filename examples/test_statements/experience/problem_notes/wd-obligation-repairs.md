# Function return and struct argument WD repairs

## Task context

- Task: repair the user's confirmed function return-domain and struct argument-domain omissions.
- Scope: anonymous-function WD shared by named definitions and literals, struct-instance WD, and Detailed evidence projection.
- Workspace: golitex, 2026-10-02. The two soundness/WD blockers are resolved; adjacent failing filters are recorded separately.

## Required return membership

```litex
# Before: all three statements incorrectly succeeded under -strict.
# have fn f(x Z) N = x
# f(-1) = -1
# -1 $in N
# Now: the definition fails on the required x $in N obligation.
have fn identity(x Z) Z = x
identity(-1) = -1
have fn widened(x N) Z = x
widened(0) = 0
have fn restricted(x Z: x >= 0) N = x
restricted(0) = 0
```

`verify_anonymous_fn_local_env` now proves `body $in ret_set` for every body,
including a bound-parameter projection, under the checked parameter/domain
assumptions. The successful return proof is mandatory in
`AnonymousFnObjWellDefinedProof`. A failed definition never stores the function
signature. Named functions and anonymous literals share this boundary; returning
a second parameter or applying a literal cannot bypass it. Detailed named-function
results now retain both WD stages before their stored membership/equality evidence.

The exact old three-line exploit now rejects the first statement and stops on
the later undefined function name. Separate same-runtime probes verify that
`-1 $in N` and `-1 >= 0` fail after the rejected definition and that the function
name can be reused for a valid definition. This is the current parser's rollback
behavior, rather than three post-failure statement results.

## Instantiated struct argument types

```litex
# Before: the invalid instance was accepted after checking only expression WD.
# struct Box<n N>:
#     value R
#     tag R
# let bad = &Box<-1>
struct Box<n N>:
    value R
    tag R
let good = &Box<0>
struct Pair<S set, a S>:
    left S
    right S
let dependent = &Pair<{0}, 0>
```

Struct-instance WD generates substituted header type obligations using the
existing `type_facts_for_typed_arguments` API, verifies them, and retains the
proofs in `requirement_fact_verified` before recording a WD id. The complete
substitution checks dependent headers such as `S set, a S`. Wrong natural
arguments, empty `nonempty_set` arguments, infinite `finite_set` arguments and
wrong dependent elements reject. Undefined arguments and wrong arity still
reject. No AST shapes or Env/Runtime state APIs changed.

Audit correction: `S set` with argument `0` is valid under the existing builtin
contract that every well-defined object is a set. Its previous classification
as an invalid kind argument was mistaken. The repair checks that existing
contract; it does not change the foundation's set semantics. Current syntax has
no struct-header premise list; no such syntax was added.

## Acceptance and limits

- [Executable positive tracer](../../../wd/obj/return_and_struct_domains.lit).
- [Invalid function return](../../../wd_negative/function_projection_return_domain.lit).
- [Invalid struct argument](../../../wd_negative/struct_argument_domain.lit).
- [Before/after, persistent session, CLI and Rust evidence](../../proof_journals/wd_obligation_repairs.json).
- Rust boundary and Detailed evidence checks: `cargo test --release wd_obligation_tests`.
- Positive CLI: `target/release/litex -strict -lang en -f examples/wd/obj/return_and_struct_domains.lit` must exit 0 with all statement successes and no session error.
- Both negative files must exit 1. The function failure names `x $in N`; the struct failure names `-1 $in N`.

Seven focused tests, 27 positive/negative release probes, the 54-case historical
audit replay, and nine ordered release-session outcomes passed. The touched
documentation's 82 runnable fences passed. The registered examples filter
passes five tests; it is not a whole examples-tree gate. Soundness boundaries,
statement boundaries and Detailed projection filters also pass.

The adjacent declaration filter still aborts in a foreign-name induction test.
The transaction filter initially had two cart inference failures (135 of 137
passed). All three failures reproduced in a separate source copy with the five
WD repair files restored to their captured pre-repair contents. The induction
failure also persists with 16 MB thread stacks and remains open in
[the adjacent pending item](../../../../todo/2026-10-2/wd-neighbor-regressions.md).

The two cart failures stopped reproducing after concurrent changes: the exact
`is_cart_trust_infers_dimension_lower_bound` and
`store_equality_infers_cart_and_tuple_shape` tests both pass on the final shared
test binary. Their original controls, `have s set; trust $is_cart(s)` in ordinary
mode and `have s set = cart(R, R)` followed by `cart_dim(s) = 2`, are preserved
in those existing Rust fixtures and the journal. This repair claims neither
that concurrent fix nor a later complete transaction-filter pass. A previously
failing valid parameterized-struct membership probe likewise now passes through
concurrent ordered-struct work.

Late shared rebuilds briefly encountered unfinished forall/aggregate test and
projection wiring. Both the isolated repaired source copy and the final shared
`cargo test --release wd_obligation_tests` pass all seven tests; the final
`cargo build --release` and the 27/54 release probes also pass. The independent
induction failure remains a limit on broader regression claims.

The current CLI supports `-strict`, `-lang`, `-f`, `-e` and `-session`; the older
policy flags and literal `try:` wrapper are unavailable. The journal records
that interface drift and checks the supported JSON envelope and each statement
result. These focused gates do not establish exhaustive kernel soundness.
