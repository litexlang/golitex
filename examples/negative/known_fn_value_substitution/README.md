# Stored function-value rewrite controls

Run each file with `target/release/litex -lang en -strict -f <file>`.
Require exit 1, `success: false`, `session_error: null`, successful setup
statements and one final failure at the phase in [manifest.json](manifest.json).
The producer unit gate executes this manifest, checks the phase and empty
stores/infers, and retries the target in the same Runtime.

`wrong_constant` is a false mathematical conclusion. `missing_guard` and
`zero_divisor` fail well-definedness. The remaining files state true identities
that this bounded rewrite deliberately cannot discover: no stored value,
repeated substitution, distinct direct values, ordinary function arguments,
or a different application. Their failure is a search limit.

Positive partners are the [original tracer](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution.lit)
and the [multiple-call](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution_multiple_calls.lit),
[scalar arithmetic](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution_scalar_arithmetic.lit),
[exact-argument](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution_exact_arguments.lit),
[guarded](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution_guarded.lit)
and [duplicate-source](../../proof_nodes/equal/by_builtin_rewrite/known_fn_value_substitution_duplicate_sources.lit) examples.
