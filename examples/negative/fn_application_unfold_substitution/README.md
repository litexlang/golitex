# Function-application unfold substitution boundaries

The positive tracer is [function-body unfolding](../../proof_nodes/equal/by_builtin_rewrite/fn_application_unfold_substitution.lit).
The manifest distinguishes false conclusions, invalid domains and missing guards
from bounded search misses. Outermost original calls unfold once; ordinary call
arguments and newly inserted bodies are not scanned. Function membership alone
contains no body. Each failed final statement is retried in the same Runtime,
with publication and subsequent liveness checks.

These fixtures preserve the [one-layer design agreement](../../../src/execute/README.md#design-agreement):
the final equality fallback must not enable rewrite in ordinary premises or
the Strategy-capped residual. A search miss at that boundary is distinct from
a false conclusion or an application WD failure.
