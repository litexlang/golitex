# Mathematical Design: First-Odd-Integer Pipeline

## Owned interface

This showcase owns one dependency-closed theorem and one downstream Mathlib
use. Its completion criterion is executable reuse, not the number of helper
lemmas.

### `kth_odd`

- Natural meaning: the `k`-th positive odd integer.
- Litex interface: `have fn kth_odd(k Z) Z = 2 * k - 1`.
- Generated Lean representation: an exact `Litex.Fn Litex.Z Litex.Z`.
- Evidence: function definition/result carrier plus checked definition
  reduction at applications used by the proof.

### Inclusive integer range sum

- Litex interface: `sum(1, n, kth_odd)`.
- Lean semantics: `∑ k ∈ Finset.Icc (1 : ℤ) n, kth_odd k`.
- Evidence: registered `aggregate.sum_single` and
  `aggregate.sum_split_last` certificates, including their exact rule IDs and
  fingerprints.

### `sum_first_odds`

- Natural meaning: the first `n` positive odd integers sum to `n²` for
  `n ≥ 1`.
- Litex proof: structured integer induction from `1`; the base calculation is
  inline, without a wrapper theorem or explicit theorem invocation.
- Canonical Lean view: `Litex.Same` over exact Litex carriers.
- External adapter view: integer equality over `Finset.Icc`, written in a
  separate non-generated Lean module.
- Downstream consumer: specialization of that external adapter at `n = 100`.

### `sum_first_ten_odds`

- Natural meaning: the first ten positive odd integers sum to `100`.
- Litex interface: a zero-binder named theorem whose proof is the direct chain
  `sum(1, 10, kth_odd) = 10^2 = 100`.
- Evidence: `KnownForallInstantiation` cites the exact `sum_first_odds` FactId
  at `10`; numeric normalization proves the second edge.
- Generated Lean view: a source-owned `Litex.Same` theorem that directly calls
  the generated universal theorem.

## Dependency spine

```text
Z and integer arithmetic
  ├─→ kth_odd definition and checked reductions
  ├─→ singleton/split-last registered sum certificates
  └─→ carrier facts for the sum and square
             ↓
inline base + split-last + exact IH FactId + inline function/square calculation
             ↓
generated canonical sum_first_odds theorem
             ↓ automatic specialization at 10 + numeric normalization
generated canonical sum_first_ten_odds theorem

external AI-authored Lean proof
             ↓
ExternalAI.sum_first_odds
             ↓ downstream import
firstHundredPositiveOddIntegersSum
```

## Export boundary

ToLean exports exactly the declarations owned by `main.lit`, using generated
support names only where required to represent source facts. It does not
recognize this theorem's shape to create a second public statement, and it
does not emit a native certificate, namespace, or consumer.

`LitexToMathlibPipelineAdapter.lean` owns the new Mathlib interface and its
Lean proof. Keeping that artifact separate makes the provenance honest: the
adapter is useful downstream, but it is not compiler output and is not
presented as a replay of the Litex Result.
