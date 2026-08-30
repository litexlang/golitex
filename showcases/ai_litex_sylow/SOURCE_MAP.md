# First Sylow Source Map

The canonical source is
`scripts/mathematics_in_litex/textbook/chapter09-groups-and-rings.lit`.
Line numbers below identify the declarations in the version used to record
this showcase; declaration names are the stable lookup key.

| Lines | Declaration | Mathematical role |
| ---: | --- | --- |
| 2680–2751 | `finite_function_space_count_insert_step`, `finite_function_space_count_empty`, `finite_function_space_count` | Exact `|B^A|` for finite carriers |
| 3526 | `finite_p_group_fixed_point_congruence` | Fixed-point congruence for finite p-group actions |
| 3679–3744 | `cyclic_prime_group_laws`, `cyclic_indices_have_prime_size` | Concrete cyclic group of order `p` |
| 4516 | `cauchy_product_one_tuple_count` | Counts the product-one tuple carrier |
| 5874–5910 | `cauchy_prime_subgroup_exists`, `cauchy_prime_subgroup_exists_auto` | Cauchy's theorem in subgroup form |
| 6231–6690 | coset action, fixed-coset bijection, normalizer quotient count | Turns fixed points into quotient divisibility |
| 6709 | `normalizer_quotient_has_prime_subgroup` | Produces `K <= N_G(H)/H` with `|K| = p` |
| 6837–6919 | `sylow_quotient_preimage_closed`, `sylow_quotient_preimage_finite` | Pulls `K` back to a finite subgroup of `G` |
| 6922–6989 | `sylow_preimage_forward_pair_mem`, `sylow_preimage_backward_mem` | Establishes the two coordinate-map carriers |
| 6991–7078 | `sylow_quotient_preimage_cardinality` | Builds both maps, proves both inverse laws, and derives `|P| = |K||H|` |
| 7083–7103 | `p_power_subgroup_successor` | Uses `|K| = p` and `|H| = p^k` to obtain `p^(k+1)` |
| 7105–7116 | `prime_power_divisor_predecessor` | Supplies the divisibility premise for induction |
| 7120–7208 | `p_power_subgroup_exists_at`, `p_power_subgroup_exists` | First Sylow theorem by induction on the exponent |

## The deep-node correspondence

The showcase theorem `quotient_preimage_cardinality_checkpoint` deliberately
has the same premises and conclusions as the canonical cardinality interface.
Its failed frame calls `sylow_quotient_preimage_cardinality` without its `K`
argument. Its accepted frame supplies the exact four-argument contract.

The next showcase theorem calls the committed checkpoint and performs exactly
the arithmetic chain at the heart of `p_power_subgroup_successor`. The final
checkpoint cites `p_power_subgroup_exists`, so the runnable lesson connects
the deep node back to the endpoint of the complete dependency DAG.
