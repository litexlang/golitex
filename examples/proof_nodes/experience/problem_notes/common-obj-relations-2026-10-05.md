# Common Obj relationship completion, 2026-10-05

Task provenance: after the final cross-Obj audit, the user authorized trying the
remaining simple relationships. This is a bounded local rule/theorem completion;
it does not certify the whole Obj corpus or close all trigonometric migration cards.

## Tracer and mathematical contract

The unchanged original tracer is:

```litex
forall a,b Z,d N+:
    a!=0
    a%d=0
    b%d=0
    =>:
        gcd(a,b)%d=0
```

The baseline strict persistent session rejects this at `search_proof`. The new
`GcdCommonDivisor` leaf checks the positive divisor and both actual remainder
premises; parent WD retains integer inputs and excludes `gcd(0,0)`. The paired
[live example](../../equal/by_builtin_rule/gcd_common_divisor.lit) preserves the
former failure as commented source and the active original statement.

## Interfaces

| Relationship | Implementation and exact boundary | Durable source |
| --- | --- | --- |
| Common divisor / gcd | Positive integer divisor; signed integer operands, not both zero; both remainders zero | [gcd](../../equal/by_builtin_rule/gcd_common_divisor.lit) |
| Common multiple / lcm | Positive integer operands; integer common multiple may be signed or zero | [lcm](../../equal/by_builtin_rule/lcm_common_multiple.lit) |
| lcm nonzero | Both integer operands nonzero; parent WD keeps the integer domain | [nonzero lcm](../../atomic/by_builtin_rule/lcm_nonzero_operands.lit) |
| Factorial / range product | Existing induction, factorial successor and product endpoint; `n in N+`, factor `fn(k Z) Z{k}` | [named theorem](../../equal/by_builtin_rule/factorial_product_relation.lit) |
| Sine sign | `0<x<pi` implies `0<sin(x)`; strict endpoints | [sine sign](../../atomic/by_builtin_rule/sin_positive_open_pi.lit) |
| Sine strict order | `-pi/2<=a<b<=pi/2`; the two interval endpoints are permitted | [sine order](../../atomic/by_builtin_rule/sin_strict_monotone_half_pi.lit) |
| Change of logarithm base | Both bases positive and unequal to one, positive argument; all combinations of bases below/above one | [change of base](../../equal/by_builtin_rule/log_change_base_positive_nonunit.lit) |
| Powered logarithm base | Positive nonunit base, positive argument, nonzero real exponent within the existing supported power WD branches | [base power](../../equal/by_builtin_rule/log_base_power_positive_nonunit.lit) |
| Nonzero logarithm | Legal positive nonunit base and positive nonunit argument; exact selected guards are retained for both | [nonzero log](../../atomic/by_builtin_rule/log_nonzero_nonunit_argument.lit) |
| Nonunit positive power | Positive nonunit base and nonzero **integer** exponent; no general symbolic real-exponent WD extension | [nonunit power](../../atomic/by_builtin_rule/positive_nonunit_integer_power.lit) |

Seven new leaves and two expanded equality leaves each have dedicated typed
success evidence, Detailed projection and ten language explanations. Every
searched child uses the inherited premise state. No AST, Env, Runtime state,
truth-search policy, public syntax or Lean compiler changes are included.

The first below-one change-of-base test failed: asking for a derived argument
inequality at a restricted child ceiling was too deep. The nonzero logarithm
leaf now consumes the argument's existing positive-nonunit guard directly,
including actual `x<1` / `1<x` evidence. It does not raise the search ceiling.
The powered-base equality keeps real exponent evidence so existing legal
closed rational powers are not narrowed to integer exponents.

## Adjacent reciprocal and ceiling findings

Two existing logarithm tests failed during the related-family gate. The current
parser uses native `Neg(1)` for surface `(-1)`, while the existing reciprocal
matcher recognized only a literal negative one or `0-1`. The owning scalar
matcher now recognizes that exact native shape, keeping the same legal-base
and positive-argument evidence. [The durable reciprocal source](../../equal/by_builtin_rule/log_reciprocal_negative_one.lit)
preserves the original failure and checks both multiplier positions; a `(-2)`
control rejects.

A public verifier diagnostic shows the product-law goal's WD fails at
`BuiltinRule` but succeeds at `Strategy` and the normal root level. This happens
before the equality leaf. The old test expected acceptance at the lower level;
it now explicitly asserts that WD boundary and normal root success for all
four formulas. Strategy suffices for product/quotient/reciprocal; the symbolic
argument-power carrier needs the normal root route. No
search permission, state lifetime or mathematical rule was changed for that
fixture. A repeated complete forall now uses `by_known_forall_fact`, rather
than the atomic instantiation label expected by the old test. The fixture checks
that route and the actual source FactId. All earlier failures and the diagnostic source/output are retained
in the journal.

## Validation receipts

The final `cargo build --release --offline --lib --bin litex` passed on a stable
source snapshot. Its CLI SHA-256 is
`886b650d2b044954d862b17a0e5981828e4e5c8408b9b0c64228d168f3d4f6b9`.

- 25 distinct focused Rust tests pass: six new-family checks, six existing log
  checks after the fixture/matcher correction, two output contract checks and
  eleven adjacent factorial/lcm checks. The final new/log/output gates each
  had stable source fingerprints.
- Eleven durable files pass `-strict -f`, exit `0` and top-level `success: true`.
- Twelve independent CLI false/illegal controls reject, exit `1` and top-level
  `success: false`. The CLI binary remained identical throughout these gates.
- The final persistent session on that binary accepts all eleven files and
  rejects three additional selected controls; all fourteen frames match their
  expected result, and the session closes with exit `0`.
- An earlier session checked all nine original statements, all log-base guard
  combinations and theorem reuse: 23 accepted frames and 18 rejected controls.

After frozen acceptance, four shared membership/rewrite/WD source files changed.
Their exact manifest is retained in `record-end` in the journal. Every Rust file
touched by this task still matches the accepted release snapshot. The receipts
certify the fixed executable and scoped tests; they do not certify the later
whole working tree or unrelated ongoing changes.

The [journal](../../proof_journals/common-obj-relations-2026-10-05.json) preserves
all baseline, failed variant and accepted session sources with raw output, all
build/test receipts, the diagnostic and the final fingerprints. The focused
[Rust tests](../../../../tests/unit/execute/common_obj_relations/tests.rs) check
same-math use, nearby false/illegal controls, proof-source citations, ten-language
text, typed Detailed fields, inherited search ceilings and Failed discard/reuse.
Full repository/examples/docs/textbook/Lean gates are outside this bounded task.

## Remaining scope

LEG35 is only completed for the original positive sine interval. Negative sine
and cosine/tangent/cotangent interval signs remain under that card. LEG36 is
only completed for strict increasing sine on its principal interval; the
other strict/weak trigonometric interfaces remain under that card. The prior
81-relation audit and 38 author routes are historical scoped evidence, not a
new whole-repository gate. General symbolic real powers and their nonunit
certificates are outside this repair.
