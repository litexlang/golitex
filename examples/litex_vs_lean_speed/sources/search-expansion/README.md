# Search and expansion source pairs

Six same-statement comparisons, described in [the batch guide](../../search-and-expansion.md).

- `affine_sum_16`, `affine_sum_64`, `affine_sum_128`: inclusive Litex indices 1..N match Lean `k+1` over `Finset.range N`. Each has expanded and formula Lean routes.
- `quadratic_context_0`, `quadratic_context_12`, `quadratic_context_24`: the same quadratic inequality with explicitly artificial irrelevant context. Each has full-context, certificate-only and direct-lemma Lean routes.

All `.lit` files are strict, standalone positive examples. Each `.lean` file proves exactly the corresponding full quantified statement. The finite-sum identities use rational values; the quadratic inequalities use real values. No file contains `trust` or `sorry`.

Use the [batch runner](../../harness/search_expansion.py) for validation, false-neighbor controls and warm checking-path measurement. It keeps all six cases, regardless of which system or route is faster. See the [manifest](../../cases/search-expansion.json) for exact sources and controls.
