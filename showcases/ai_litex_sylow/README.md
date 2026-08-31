# AI + Litex: First Sylow Theorem

<!-- Narrative spine: First Sylow theorem -> dependency DAG -> one successor bottleneck -> transactional try/JSON loop -> proof journal -> materialized source -> clean replay -> reusable AI operator protocol. -->

This is a runnable lesson in using an AI system as a disciplined Litex proof
author. The mathematical case study is the complete First Sylow theorem path
in *Mathematics in Lean* Chapter 9. The operational case study follows one
high-leverage node in depth: pulling a prime-order subgroup of
`N_G(H) / H` back to a subgroup of `G` and proving its exact cardinality.

The lesson has two simultaneous outputs:

- a human-readable mathematical dependency graph; and
- a reproducible machine loop in which every candidate is a literal Litex
  transaction and every decision is grounded in JSON verifier output.

The final source is [main.lit](main.lit). The complete implementation remains
in the canonical MIL
[Chapter 9](../../scripts/mathematics_in_litex/textbook/chapter09-groups-and-rings.lit);
this showcase imports and cites it instead of copying thousands of lines.

## The mathematical route

Suppose `G` is finite, `p` is prime, and `p^n` divides `|G|`. The target is a
subgroup `H <= G` with `|H| = p^n`.

| Stage | Mathematical output | Canonical Litex interface | Used by |
| ---: | --- | --- | --- |
| 1 | Exact cardinality of a finite function space | `finite_function_space_count` | Cauchy tuple count |
| 2 | The additive cyclic group of order `p` | `cyclic_prime_group_laws`, `cyclic_indices_have_prime_size` | Rotation action |
| 3 | Product-one `p`-tuples have the required count | `cauchy_product_one_tuple_count` | Cauchy's theorem |
| 4 | A finite `p`-group action satisfies `card(X) congruent card(X^P) (mod p)` | `finite_p_group_fixed_point_congruence` | Cauchy and Sylow action counts |
| 5 | A prime divisor of a finite group order yields a subgroup of order `p` | `cauchy_prime_subgroup_exists_auto` | Normalizer quotient |
| 6 | `H` acts on `G/H`; fixed cosets are counted through `N_G(H)` | `sylow_coset_action_is_group_action`, `normalizer_quotient_cardinality_eq_fixed_cosets` | Quotient divisibility |
| 7 | `p` divides `|N_G(H)/H|`, hence the quotient has `K` of order `p` | `normalizer_quotient_has_prime_subgroup` | Pullback |
| 8 | The inverse image `P = pi^-1(K)` is a finite subgroup of `G` | `sylow_quotient_preimage_closed`, `sylow_quotient_preimage_finite` | Exact pullback size |
| 9 | `P` is in bijection with `K x H`, so `|P| = |K||H|` | `sylow_quotient_preimage_cardinality` | Successor step |
| 10 | A subgroup of order `p^k` grows to one of order `p^(k+1)` | `p_power_subgroup_successor` | Induction |
| 11 | Induction on the exponent produces order `p^n` | `p_power_subgroup_exists` | First Sylow theorem |

The table is a proof DAG, not a list of tactics. Before writing Litex, the AI
must know which node it is proving, the exact contract consumed by the next
node, and which earlier interfaces already own the underlying mathematics.

## Deep node: why the quotient preimage has size `|K||H|`

Let `K <= N_G(H)/H` and define

```text
P = {x in N_G(H) | pi(x) in K}.
```

The canonical proof does not assert the product formula directly. It builds
typed coordinate maps

```text
forward  : P     -> K x H
backward : K x H -> P
```

where `forward(x)` records the coset `xH` and the unique `H`-coordinate of
`x`, while `backward(q, h)` multiplies a chosen representative of `q` by
`h`. It proves both inverse laws, derives injectivity and surjectivity, and
then applies finite-cardinality preservation under a bijection:

```text
|P| = |K x H| = |K| * |H|.
```

If `|K| = p` and `|H| = p^k`, the successor calculation is the short final
chain

```text
|P| = |K| * |H| = p * p^k = p^(k + 1).
```

This is the right deep node for an AI lesson because the mathematics is
simple at the top level while the formal contract is exacting: every map has
a carrier, both inverse directions matter, and the final arithmetic depends
on the cardinality theorem rather than mere finiteness.

## Run the complete lesson

From the repository root, build the current release binary once:

```bash
cargo build --release
```

Replay all interactive frames through one persistent project session:

```bash
mkdir -p tmp/ai-litex-sylow
python3 showcases/ai_litex_sylow/replay_session.py \
  --output tmp/ai-litex-sylow/session_events.jsonl
```

The import is the cold prefix load. After the `ready` event, all four frames
reuse the same Runtime. The expected frame results are:

| Frame | Expected JSON | Meaning |
| --- | --- | --- |
| `B001` | `"ok": false` | The candidate calls the correct cardinality theorem with one argument missing; the outer `try:` rolls the declaration back. |
| `B002` | `"ok": true` | The corrected candidate calls the exact cardinality theorem and commits the declaration. |
| `B003` | `"ok": true` | A new theorem calls the committed `B002` declaration without replaying it, then performs the prime-power calculation. |
| `B004` | `"ok": true` | The endpoint cites the complete canonical `p_power_subgroup_exists` theorem. |

Session frame ids and journal source-block ids are intentionally different.
Frames `B001` and `B002` are two attempts at the same source block `P001`;
the remaining accepted source blocks are `P002` and `P003`.

At a coherent checkpoint, validate the event sequence and materialize the
contiguous accepted prefix:

```bash
python3 showcases/ai_litex_sylow/materialize.py \
  --events tmp/ai-litex-sylow/session_events.jsonl \
  --output-dir showcases/ai_litex_sylow
```

The materializer refuses an unexpected event sequence or diagnostic. It
strips the successful outer `try:` wrappers, writes `main.lit`, preserves both
attempts at `P001` in `proof_journal.json`, and creates the compact event
projection. It marks the source as pending until the clean gate below passes.

Finally, verify the materialized file from a clean process:

```bash
target/release/litex -compact -graph -f \
  showcases/ai_litex_sylow/main.lit
```

Acceptance requires both process exit code `0` and top-level `"ok": true`.
A successful session frame is staging evidence; it is not the final file gate.

That gate verifies `main.lit` relative to its configured imports. The runner
reports those imports as a trusted boundary. Audit the complete dependency
closure separately with:

```bash
python3 showcases/ai_litex_sylow/replay_session.py --strict \
  --output tmp/ai-litex-sylow/strict_startup.jsonl
```

The current closure audit is expected to stop before `ready`: strict mode
rejects an explicit trusted partial-order statement at
`MILAlternative::chap2_struct` line 863. That statement is unrelated to the
displayed Sylow route, but its presence means the full imported package is not
strictly checkable. Treat the ordinary file gate and this closure audit as two
different results.

## What the replay helper actually sends

The session transport and the Litex transaction are separate layers. For each
frame, the helper computes the UTF-8 payload size and sends

```text
run B002 <utf8-byte-count>\n<literal source bytes>
```

The source bytes themselves begin with one outermost `try:`. A failed
top-level `try:` returns a normal `block` event with `ok: false` and preserves
the imported prefix plus every earlier committed frame. A non-transactional
failed top-level statement would poison the session and make later frames
`skipped`.

`try:` is transactional, not an optimizer. It makes the workflow fast by
avoiding repeated construction of an already loaded context after failed
candidates.

## How the AI reads JSON

The AI always repairs the earliest failing phase.

| Signal in the event or trace | Next action |
| --- | --- |
| Parse error | Fix indentation or grammar; do not change the mathematics. |
| Name/type resolution error | Check package authorization, namespace, arity, and the declared carrier. |
| Well-definedness error | Supply exact domain, subset, nonzero, bound, or dependent-carrier evidence. |
| Proof reports an unknown conclusion | Search the current interfaces, select the theorem with the exact conclusion, or add the smallest mathematical bridge. |
| `ok: true` in a session block | Record accepted source without `try:`, its dependencies, and its reusable lesson before moving on. |
| Clean runner has top-level `ok: false` or nonzero exit | The artifact is not accepted, regardless of earlier session success. |

The stored journal is [proof_journal.json](proof_journal.json), the compact
event projection is [session_evidence.json](session_evidence.json), and the
closure result is [strict_audit.json](strict_audit.json). These files record
concise decision evidence, not private chain-of-thought. See
[AI_OPERATOR_PROTOCOL.md](AI_OPERATOR_PROTOCOL.md) for the reusable AI contract
and [SOURCE_MAP.md](SOURCE_MAP.md) for the exact canonical declarations.

## Trust and verification boundary

The materialized `main.lit` contains no direct `trust`, `axiom`, or
`abstract_prop`. Canonical MIL Chapter 9 also has zero direct occurrences of
those forms. The selected First Sylow route cites Chapter 9 and the explicit
group/divisibility interfaces it uses.

The current MIL package is larger than this route. Importing it also loads
later chapters with separately recorded trust debt, and `MILAlternative`
contains an unrelated trusted partial-order statement. This showcase does not
claim that the entire imported package is trust-free; its zero-direct-trust
claim is scoped to `main.lit`, Chapter 9, and the displayed Sylow dependency
route. The Litex verifier, builtin rules, and inference rules remain part of
the trusted implementation boundary of this demonstration. No Lean replay or
independent kernel audit is claimed here.
