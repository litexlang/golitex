# Finite linear combinations and span from std

These consumers import the actual `algebra` std package. Run from the repository
root after building the release executable:

```bash
python3 examples/algebra/finite_span/check.py
```

[main.lit](main.lit) verifies the trace `0,2,14` for coefficients `(2,3)` and
vectors `(1,4)`, then uses the shared selected-value theorem to compute
`2*1+3*4=14`. It calls the imported span-subspace theorem on `(1,2)`, exercises
coefficient addition/scaling/negation and transports the combination through
the identity linear map. Before promotion, these general constructions and
proofs were lecture-local. Its shared call is:

<!-- litex:skip-test -->
```litex
release thm Algebra::finite_span::span_is_subspace(R,real_field,R,scalars,2,(1,2))
```

This excerpt uses the preceding field/space instance in main.lit.
[empty.lit](empty.lit) proves the empty span is exactly the singleton vector
zero and checks repeated vectors. [zero_dimensional/main.lit](zero_dimensional/main.lit)
checks nonempty coefficient/vector lists in the singleton vector space.
[contracts.lit](contracts.lit) exercises every one of the 28 theorem signatures
using generic typed hypotheses. Those claims check imported APIs; they are not
28 additional mathematical results.

The [shared rejection context](negative/context.lit) constructs valid instances,
lists, a verified trace and named value facts. Each negative file passes its
valid prefix and rejects only its final statement:

| Fixture | Required boundary |
| --- | --- |
| wrong_length | The two-term selector rejects a three-entry vector list |
| wrong_empty_value | The empty combination cannot equal one in the real scalar line |
| wrong_value | The verified value 14 cannot be replaced by 15 |
| wrong_trace_start | A trace must start at vector zero |
| missing_trace | A complete supplied trace needs the actual recurrence before determining the selected value |
| index_zero | Coefficient indices start at one |
| affine_preservation | Combination preservation requires linearity of the complete supplied map |

The checker runs the full migrated lecture and independent consumers, compares
the complete std/WiX payload and copies the real std package into archive and
shared-data installation layouts. Both installed consumers run without a path
override. The root main/empty/contracts files are ordered exports; their own
mathematical declarations are independent and do not share short local names.

The source adds no trust, axiom, abstract_prop, native rule or new scalar/vector
structure. Two named source theorems expose definition consequences across
imports: the zero coefficient carrier and the selected combination's defining
relation. They are proved from the existing declarations. General basis
existence, exchange, dimension invariance and rank-nullity are not part of this
batch. See [std/algebra](../../../std/algebra/README.md) for the exact interfaces
and [math_collections.md](math_collections.md) for the mathematical dependencies.
