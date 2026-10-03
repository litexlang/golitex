# Exact numeric, periodic trig and modulus rejection controls

Every `.lit` here must return exit 1 and JSON `success: false` under
`target/release/litex -strict -f <file>`. The companion accepted artifacts are
in `examples/proof_nodes/equal/by_builtin_rule/` and
`examples/proof_nodes/atomic/by_builtin_rule/exact_fraction_order.lit`.
The focused Rust family is `exact_numeric_periodic_modulus`; the durable gate
is `examples/test_objs/proof_journals/exact_numeric_periodic_modulus_2026-10-03.json`.

These controls cover poles, missing integer-period evidence, the wrong signed
half-period, undefined canceled denominators, zero negative powers, false
fraction order, wrong/nonprincipal modulus roots and zero's strict positivity.
