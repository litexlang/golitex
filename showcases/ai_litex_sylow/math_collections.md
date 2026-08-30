# Mathematical and Operational Interface Inventory

## Scope

This module teaches one complete theorem route and one proof-authoring route.
It does not redeclare groups, quotient groups, finite cardinality, cyclic
groups, or Sylow subgroups. Those concepts remain visible through explicit
imports and named theorem calls.

## Mathematical interfaces

| Layer | Interface | Role in the route | Ownership |
| --- | --- | --- | --- |
| Native | `finite_set`, `finite_set_size`, `cart`, `power_set`, `N`, `N+` | Carriers and cardinal arithmetic | Litex builtin surface |
| Imported structure | `MILAlternative::chap2_struct::Group` | First-class group operations and laws | MIL alternative Chapter 2 |
| Imported relation | `MILAlternative::chap2_struct::divides` | Expresses `p^n | |G|` | MIL alternative Chapter 2 |
| Chapter 9 | `finite_function_space_count` | Exact finite function-space count | Canonical MIL |
| Chapter 9 | `finite_p_group_fixed_point_congruence` | Fixed-point count modulo `p` | Canonical MIL |
| Chapter 9 | `cauchy_prime_subgroup_exists_auto` | Prime-order subgroup from divisibility | Canonical MIL |
| Chapter 9 | `normalizer_quotient_has_prime_subgroup` | Prime-order `K <= N_G(H)/H` | Canonical MIL |
| Chapter 9 | `sylow_quotient_preimage_closed` | Pullback is a subgroup | Canonical MIL |
| Chapter 9 | `sylow_quotient_preimage_cardinality` | Pullback is finite and has size `|K||H|` | Canonical MIL |
| Chapter 9 | `p_power_subgroup_successor` | Order `p^k` to order `p^(k+1)` | Canonical MIL |
| Chapter 9 | `p_power_subgroup_exists` | First Sylow theorem by exponent induction | Canonical MIL |
| Showcase | `quotient_preimage_cardinality_checkpoint` | Reader-facing exact theorem selection | This module |
| Showcase | `quotient_preimage_prime_power_checkpoint` | Demonstrates committed-block reuse and the successor arithmetic | This module |
| Showcase | `first_sylow_checkpoint` | Reader-facing endpoint | This module |

## Operational artifacts

| Artifact | Contract |
| --- | --- |
| `frame_01_failed.lit.txt` | The right theorem with an incomplete argument contract inside outermost `try:`. |
| `frame_02_accepted.lit.txt` | The corrected current block; same public theorem, exact stronger interface. |
| `frame_03_reuse.lit.txt` | Depends on the declaration committed by the previous successful frame. |
| `frame_04_endpoint.lit.txt` | Connects the lesson to the canonical First Sylow endpoint. |
| `session_evidence.json` | Compact exact projection plus hashes of the recorded persistent-session JSONL. |
| `strict_audit.json` | Exact decisive projection of the dependency-closure startup failure. |
| `proof_journal.json` | Recoverable staging record and concise diagnosis. |
| `replay_session.py` | Length-delimited session client; it never rewrites mathematical source. |
| `main.lit` | Contiguous accepted prefix with all outer `try:` wrappers removed. |

## Boundary decisions

- The complete Chapter 9 proof is cited, not copied.
- The showcase adds reader-facing checkpoints, not a second group-theory
  library.
- A direct theorem call is preferred to reconstructing the coordinate
  bijection locally once the canonical interface exists.
- Session evidence and final runner evidence have different roles and are both
  required.
- The ordinary file gate is relative to configured imports; the separate
  strict closure audit currently stops at explicit imported trust debt.
- No direct trust is introduced by this module. Trust elsewhere in the larger
  imported MIL package is disclosed in the README and is outside the selected
  theorem route.
