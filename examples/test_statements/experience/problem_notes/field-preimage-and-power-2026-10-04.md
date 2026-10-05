# FN07 / GEO03: checked function fields and square inference

Task: answer the maintainer's two concrete questions and complete authorized
local Rust repairs, 2026-10-04. Both are category 2. No Stmt/Obj/Fact fields,
Env/Runtime representation or global search policy changed.

## FN07 — preserve the already checked field function

```litex
struct Ops:
    op fn(x R) R
    tag N
have fn shift(x R) R = x + 1
have ops &Ops = (shift, 0)
have by fn_preimage: a from ops.op(2) $in fn_range(ops.op)
a $in R
ops.op(a) = ops.op(2)
```

Before, the function type and source membership passed, then the application
builder returned None and execution raised InternalBug. The existing
`FnObjHead::FieldAccess` was simply missing from the helper's match. The repair
preserves its receiver/field identity and checked signature. The same omission
is repaired in inferred FnRange preimages and indexed union/intersection
applications; displayed field applications are recognized like named calls.

The unchanged native example now produces a valid witness and its equation.
Opaque range members publish an existential that can actually be obtained and
used. Conditional abstract fields work after their callable signature has
been checked. Wrong receiver, image source, arity, input carrier and guard
remain rejected; failed introductions discard their names, and completed
proof scopes allow fresh reuse. The previous complete typed-alias proof still
passes. This does not assert that the chosen witness must be 2.

Stable tracers: [field preimage](../../../stmt_nodes/definition/field_function_preimage.lit),
[field range](../../../infer/atomic/field_fn_range.lit),
[indexed family](../../../infer/atomic/field_indexed_family.lit).

## GEO03 — check the square's sign before searching its base's sign

```litex
have x R*
have square R = x^2
square $in R+
1 / square $in R
```

The equality's optional PositiveRealPower inference previously tried to prove
`0 < x` at the caller's search level. For a nonzero real determinant, its sign
need not be positive; this unnecessary search made the geometry prefix slow.
Now it first checks `0 < x^2` using the existing bounded builtin rules. Their
nonzero real even-power proof suffices. The exponent check, target membership
storage and original positive-base fallback remain checked and available.
The new child ceiling is capped at BuiltinRule and never raises its parent.

A controlled clone uses byte-identical Rust sources and the same Cargo project
path except for `positive_real_power.rs`. Its original AAS declaration-prefix
input takes 56.470 seconds with the old rule and 10.623 seconds with the new
rule. Two squares take 11.194 seconds; the multiplication control takes
11.678 seconds. These are measured runs, not a general runtime guarantee.
The diagnostic theorem retains its historical `0=0` target: this measures
the declarations and does not newly validate the complete AAS theorem.

The [nonzero-square tracer](../../../infer/equal/nonzero_real_square.lit)
passes. Negative real bases and negative even integer exponents pass; zero,
an arbitrary possibly-zero real base, i², negative odd powers and undefined
zero negative powers remain rejected. The supported symbolic natural-exponent
positive-base route still publishes R+.

## Acceptance and scope

46 affected Rust tests pass, including the eight new public-runtime tests,
declaration ownership/scope, existing power/range and permission boundaries.
The production CLI passes 22 expected positive/negative controls, one complete
typed-alias proof, seven new/existing file tracers, 378 statement checks and
175 basic semantic checks. No trust was added to discharge proof obligations.

This closes the FN07 construction omissions and the identified GEO03 square
search path. All-head coverage, independent proof replay, complete geometry,
full corpus/release collection and REL06 Detailed projection remain separate
work. Earlier failed exploratory inputs and the confounded first timing pair
are retained, with corrections, in the
[acceptance and raw receipts](../../../../tests/tooling/acceptance/field-preimage-and-power-2026-10-04.md).
