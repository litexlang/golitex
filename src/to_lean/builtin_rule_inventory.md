# To-Lean Builtin Rule Inventory

Generated from production Rust source by
[`generate_builtin_inventory.py`](generate_builtin_inventory.py).
Do not hand-edit the table; update the generator's mapping policy and regenerate.

## Scope and counting contract

The inventory contains **658 label-bearing builtin success sites**:
**631 builtin-rule sites** and **27 builtin-strategy sites**.
The lower-level source contains 462 direct success-constructor calls; expanding
their forwarding helpers exposes the label-bearing sites below. The repository's
informal 'about 500 rules' estimate is therefore closest to the 559
distinct static labels, while 658 is the exhaustive source-site count used here.
Forwarding helpers such as a constructor receiving `reason.to_string()` are
collapsed into their outer label-bearing callers. This is why the count is a
semantic call-site count rather than a raw constructor grep. A dynamic site
appears once with its source expression even when it can render several labels
at runtime.

Of these sites, 583 have a static string label and 75 use
a dynamic label expression. 46 evaluation/computation-like sites
are explicitly marked `not_this_round`. The classification is intentionally
conservative and source-derived; it does not claim one Rust site equals one
mathematical theorem schema.

A Lean mapping is recorded only when the current backend actually emits and the
Lean kernel checks that tactic or lemma. `none` means no checked mapping exists
yet, not that Lean lacks the mathematics.

Regenerate or audit drift with:

```text
python3 src/to_lean/generate_builtin_inventory.py --write
python3 src/to_lean/generate_builtin_inventory.py --check
```

## Summary

| Metric | Count |
| --- | ---: |
| Total label-bearing sites | 658 |
| Direct success-constructor calls | 462 |
| Builtin rules | 631 |
| Builtin strategies | 27 |
| Static labels | 583 |
| Distinct static labels | 559 |
| Dynamic label expressions | 75 |
| Evaluation/computation (`not_this_round`) | 46 |
| Checked Lean mappings currently implemented | 26 |
| Forwarding sink functions discovered | 21 |

## Rule sites

| ID | Kind | Label or dynamic expression | Source | Family | Checked Lean mapping | Status |
| --- | --- | --- | --- | --- | --- | --- |
| B0001 | rule | real matrix operator has the requested matrix type | `src/execute/by_stmt/thm_by_stmt.rs:563` | execution bridge | none | `pending` |
| B0002 | rule | trusted file load | `src/execute/exec_fact_stmt.rs:51` | execution bridge | none | `not_this_round` |
| B0003 | rule | prime by trial-division definition | `src/verify/verify_atomic_fact_by_definition.rs:59` | atomic fact by definition | none | `pending` |
| B0004 | rule | subset by definition (forall x in left: x in right) | `src/verify/verify_atomic_fact_by_definition.rs:120` | atomic fact by definition | none | `pending` |
| B0005 | rule | superset by definition (forall x in right: x in left) | `src/verify/verify_atomic_fact_by_definition.rs:156` | atomic fact by definition | none | `pending` |
| B0006 | rule | replay-safe structural equality | `src/verify/verify_builtin_rule.rs:63` | builtin rule | none | `pending` |
| B0007 | rule | number comparison | `src/verify/verify_builtin_rule.rs:153` | builtin rule | none | `pending` |
| B0008 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rule.rs:179` | builtin rule | none | `pending` |
| B0009 | rule | abs: x <= abs(x) and -x <= abs(x) | `src/verify/verify_builtin_rules/abs_order_builtin.rs:235` | abs order | none | `pending` |
| B0010 | rule | abs: -abs(x) <= x | `src/verify/verify_builtin_rules/abs_order_builtin.rs:249` | abs order | none | `pending` |
| B0011 | rule | abs: finite sum triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:333` | abs order | none | `pending` |
| B0012 | rule | abs: finite-set sum triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:396` | abs order | none | `pending` |
| B0013 | rule | abs: 0 < abs(x) from x != 0 | `src/verify/verify_builtin_rules/abs_order_builtin.rs:429` | abs order | none | `pending` |
| B0014 | rule | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/abs_order_builtin.rs:480` | abs order | none | `pending` |
| B0015 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:518` | abs order | none | `pending` |
| B0016 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:541` | abs order | none | `pending` |
| B0017 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:561` | abs order | none | `pending` |
| B0018 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:579` | abs order | none | `pending` |
| B0019 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:607` | abs order | none | `pending` |
| B0020 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:636` | abs order | none | `pending` |
| B0021 | rule | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:661` | abs order | none | `pending` |
| B0022 | rule | abs: triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:734` | abs order | none | `pending` |
| B0023 | rule | abs: weak reverse triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:762` | abs order | none | `pending` |
| B0024 | rule | dynamic: reason | `src/verify/verify_builtin_rules/complex_builtin.rs:18` | complex | none | `pending` |
| B0025 | rule | dynamic: reason | `src/verify/verify_builtin_rules/complex_builtin.rs:25` | complex | none | `pending` |
| B0026 | rule | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:37` | complex | none | `pending` |
| B0027 | rule | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:47` | complex | none | `pending` |
| B0028 | rule | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:66` | complex | none | `pending` |
| B0029 | rule | complex modulus zero implies zero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:93` | complex | none | `pending` |
| B0030 | rule | complex reconstruction from real and imaginary coordinates | `src/verify/verify_builtin_rules/complex_builtin.rs:110` | complex | none | `pending` |
| B0031 | rule | complex reconstruction from real and imaginary coordinates | `src/verify/verify_builtin_rules/complex_builtin.rs:125` | complex | none | `pending` |
| B0032 | rule | complex extensionality by re and img | `src/verify/verify_builtin_rules/complex_builtin.rs:158` | complex | none | `pending` |
| B0033 | rule | native imaginary unit is nonzero | `src/verify/verify_builtin_rules/complex_builtin.rs:175` | complex | none | `pending` |
| B0034 | rule | complex modulus is a nonnegative real | `src/verify/verify_builtin_rules/complex_builtin.rs:197` | complex | none | `pending` |
| B0035 | rule | complex modulus triangle inequality | `src/verify/verify_builtin_rules/complex_builtin.rs:204` | complex | none | `pending` |
| B0036 | rule | complex modulus reverse triangle inequality | `src/verify/verify_builtin_rules/complex_builtin.rs:211` | complex | none | `pending` |
| B0037 | rule | complex modulus is positive for a nonzero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:230` | complex | none | `pending` |
| B0038 | rule | complex modulus is nonzero for a nonzero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:265` | complex | none | `pending` |
| B0039 | rule | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:531` | complex | none | `pending` |
| B0040 | rule | they are the same | `src/verify/verify_builtin_rules/equality_dispatch.rs:17` | equality dispatch | none | `pending` |
| B0041 | rule | gcd divides each argument | `src/verify/verify_builtin_rules/equality_dispatch.rs:30` | equality dispatch | none | `pending` |
| B0042 | rule | a product modulo either factor is zero | `src/verify/verify_builtin_rules/equality_dispatch.rs:43` | equality dispatch | none | `pending` |
| B0043 | rule | calculation and rational expression simplification | `src/verify/verify_builtin_rules/equality_dispatch.rs:320` | equality dispatch | `norm_num` / `ring` / `field_simp; ring` | `implemented` |
| B0044 | rule | calculation and rational expression simplification | `src/verify/verify_builtin_rules/equality_dispatch.rs:331` | equality dispatch | `norm_num` / `ring` / `field_simp; ring` | `implemented` |
| B0045 | rule | tuple reconstruction from known Cartesian-product membership | `src/verify/verify_builtin_rules/equality_dispatch.rs:1121` | equality dispatch | none | `pending` |
| B0046 | rule | union_commutative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1142` | equality dispatch | none | `pending` |
| B0047 | rule | union_associative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1154` | equality dispatch | none | `pending` |
| B0048 | rule | union_idempotent | `src/verify/verify_builtin_rules/equality_dispatch.rs:1165` | equality dispatch | none | `pending` |
| B0049 | rule | union_empty_identity | `src/verify/verify_builtin_rules/equality_dispatch.rs:1178` | equality dispatch | none | `pending` |
| B0050 | rule | intersect_commutative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1198` | equality dispatch | none | `pending` |
| B0051 | rule | intersect_associative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1211` | equality dispatch | none | `pending` |
| B0052 | rule | intersect_union_distributive | `src/verify/verify_builtin_rules/equality_dispatch.rs:1224` | equality dispatch | none | `pending` |
| B0053 | rule | set_diff_as_union_of_asymmetric_differences | `src/verify/verify_builtin_rules/equality_dispatch.rs:1247` | equality dispatch | none | `pending` |
| B0054 | rule | set_minus_union_de_morgan | `src/verify/verify_builtin_rules/equality_dispatch.rs:1260` | equality dispatch | none | `pending` |
| B0055 | rule | set_minus_intersect_de_morgan | `src/verify/verify_builtin_rules/equality_dispatch.rs:1273` | equality dispatch | none | `pending` |
| B0056 | rule | set_minus_recovers_subset_from_relative_complement | `src/verify/verify_builtin_rules/equality_dispatch.rs:1291` | equality dispatch | none | `pending` |
| B0057 | rule | cart_finite_set_size_product | `src/verify/verify_builtin_rules/equality_dispatch.rs:1315` | equality dispatch | none | `pending` |
| B0058 | rule | finite_set_size_set_minus | `src/verify/verify_builtin_rules/equality_dispatch.rs:1354` | equality dispatch | none | `pending` |
| B0059 | rule | finite_set_size_union_inclusion_exclusion | `src/verify/verify_builtin_rules/equality_dispatch.rs:1388` | equality dispatch | none | `pending` |
| B0060 | rule | finite_set_size_partition_by_intersection_and_difference | `src/verify/verify_builtin_rules/equality_dispatch.rs:1422` | equality dispatch | none | `pending` |
| B0061 | rule | finite_set_size_symmetric_difference | `src/verify/verify_builtin_rules/equality_dispatch.rs:1456` | equality dispatch | none | `pending` |
| B0062 | rule | finite_set_size_set_minus_finite_subset | `src/verify/verify_builtin_rules/equality_dispatch.rs:1502` | equality dispatch | none | `pending` |
| B0063 | rule | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/equality_dispatch.rs:1554` | equality dispatch | none | `pending` |
| B0064 | rule | power_set_finite_set_size_two_pow_finite_set_size_base | `src/verify/verify_builtin_rules/equality_dispatch.rs:1585` | equality dispatch | none | `pending` |
| B0065 | rule | intersect_from_subset | `src/verify/verify_builtin_rules/equality_dispatch.rs:2139` | equality dispatch | none | `pending` |
| B0066 | rule | intersect_literal_set_filter | `src/verify/verify_builtin_rules/equality_dispatch.rs:2203` | equality dispatch | none | `not_this_round` |
| B0067 | rule | equality: a = c - b from known a + b = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2253` | equality dispatch | none | `pending` |
| B0068 | rule | equality: a = c - b from known b + a = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2272` | equality dispatch | none | `pending` |
| B0069 | rule | tuple equality from dimension and projections | `src/verify/verify_builtin_rules/equality_dispatch.rs:2335` | equality dispatch | none | `pending` |
| B0070 | rule | tuple equality from symbolic dimension and coordinates | `src/verify/verify_builtin_rules/equality_dispatch.rs:2443` | equality dispatch | none | `pending` |
| B0071 | rule | cart equality from dimension and projections | `src/verify/verify_builtin_rules/equality_dispatch.rs:2518` | equality dispatch | none | `pending` |
| B0072 | rule | integer interval emptiness by number comparison | `src/verify/verify_builtin_rules/equality_dispatch.rs:2624` | equality dispatch | none | `pending` |
| B0073 | rule | empty_set_equality_from_not_nonempty | `src/verify/verify_builtin_rules/equality_dispatch.rs:2638` | equality dispatch | none | `pending` |
| B0074 | rule | finite_set_size_zero_implies_empty_set | `src/verify/verify_builtin_rules/equality_dispatch.rs:2668` | equality dispatch | none | `pending` |
| B0075 | rule | equality from a >= b and b >= a | `src/verify/verify_builtin_rules/equality_dispatch.rs:2739` | equality dispatch | none | `pending` |
| B0076 | rule | division elimination: from a / b = c and b != 0, prove a = c * b | `src/verify/verify_builtin_rules/equality_dispatch.rs:2800` | equality dispatch | none | `pending` |
| B0077 | rule | division introduction: from a = b * c and b != 0, prove a / b = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2876` | equality dispatch | none | `pending` |
| B0078 | rule | general_cart equals its canonical set-builder definition | `src/verify/verify_builtin_rules/equality_dispatch.rs:2949` | equality dispatch | none | `pending` |
| B0079 | rule | dynamic: rule | `src/verify/verify_builtin_rules/equality_dispatch.rs:3130` | equality dispatch | none | `pending` |
| B0080 | rule | dynamic: rule | `src/verify/verify_builtin_rules/equality_dispatch.rs:3179` | equality dispatch | none | `pending` |
| B0081 | rule | dynamic: format!( "equality from registered antisymmetric prop '{}'", prop_name ) | `src/verify/verify_builtin_rules/equality_dispatch.rs:3228` | equality dispatch | none | `pending` |
| B0082 | rule | matrix positive power base case: A '^ 1 = A | `src/verify/verify_builtin_rules/equality_function.rs:26` | equality function | none | `pending` |
| B0083 | rule | matrix positive power recursion: A '^(k + 1) = (A '^ k) '* A | `src/verify/verify_builtin_rules/equality_function.rs:67` | equality function | none | `pending` |
| B0084 | rule | abs: abs(x) = x from 0 <= x | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:84` | numeric equality | none | `pending` |
| B0085 | rule | abs: abs(x) = -x from x <= 0 | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:129` | numeric equality | none | `pending` |
| B0086 | rule | abs: abs(x * y) = abs(x) * abs(y) | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:161` | numeric equality | none | `pending` |
| B0087 | rule | abs: x^n = abs(x)^n for even integer n | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:214` | numeric equality | none | `pending` |
| B0088 | rule | abs: x = 0 from abs(x) = 0 | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:241` | numeric equality | none | `pending` |
| B0089 | rule | equality: 0 = x - y with x = y (known or builtin) | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:53` | numeric equality | none | `pending` |
| B0090 | rule | equality: b = 0 from a * b = 0 and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:143` | numeric equality | none | `pending` |
| B0091 | rule | equality: a = 0 from a * b = 0 and b != 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:170` | numeric equality | none | `pending` |
| B0092 | rule | equality: 0 = a^n from a = 0, n positive integer literal | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:232` | numeric equality | none | `not_this_round` |
| B0093 | rule | equality: 0 % m = 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:266` | numeric equality | none | `pending` |
| B0094 | rule | equality: x % 1 = 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:299` | numeric equality | none | `pending` |
| B0095 | rule | equality: 1 % k = 1 for k >= 2 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:349` | numeric equality | none | `pending` |
| B0096 | rule | equality: (a - a % b) % b = 0 for a in Z and b in N+ | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:413` | numeric equality | none | `pending` |
| B0097 | rule | equality: Euclidean remainder uniqueness from a = m * q + r and 0 <= r < m | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:497` | numeric equality | none | `pending` |
| B0098 | rule | equality: finite-set product over empty set is one | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:39` | numeric equality | none | `pending` |
| B0099 | rule | equality: finite-set product over displayed set expands elementwise | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:90` | numeric equality | none | `pending` |
| B0100 | rule | equality: finite-set product after inserting a fresh element | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:183` | numeric equality | none | `pending` |
| B0101 | rule | equality: finite-set product after removing a member | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:275` | numeric equality | none | `pending` |
| B0102 | rule | equality: finite-set product over closed integer range equals range product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:337` | numeric equality | none | `pending` |
| B0103 | rule | equality: finite-set product of a constant factor | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:391` | numeric equality | none | `pending` |
| B0104 | rule | equality: finite-set products from known fn_eq_in | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:459` | numeric equality | none | `pending` |
| B0105 | rule | equality: finite-set products from pointwise equality on the finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:491` | numeric equality | none | `pending` |
| B0106 | rule | equality: finite-set product distributes over pointwise multiplication | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:572` | numeric equality | none | `pending` |
| B0107 | rule | equality: finite-set product substitution along a bijection | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:645` | numeric equality | none | `pending` |
| B0108 | rule | equality: finite-set sum over empty set is zero | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:40` | numeric equality | none | `pending` |
| B0109 | rule | equality: finite-set sum over displayed set expands elementwise | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:101` | numeric equality | none | `pending` |
| B0110 | rule | equality: finite-set sum over closed integer range equals range sum | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:194` | numeric equality | none | `pending` |
| B0111 | rule | equality: finite-set sum of the literal zero function is zero | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:238` | numeric equality | none | `not_this_round` |
| B0112 | rule | equality: finite-set sum of a constant summand | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:265` | numeric equality | none | `pending` |
| B0113 | rule | equality: finite-set sums from pointwise equality on the finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:320` | numeric equality | none | `pending` |
| B0114 | rule | equality: finite-set sum substitution along a uniquely-covered index set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:408` | numeric equality | none | `pending` |
| B0115 | rule | equality: finite-set sum over a disjoint union | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:493` | numeric equality | none | `pending` |
| B0116 | rule | equality: finite-set sum distributes over pointwise addition | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:574` | numeric equality | none | `pending` |
| B0117 | rule | equality: finite-set sum scalar multiplication | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:642` | numeric equality | none | `pending` |
| B0118 | rule | equality: double finite-set sum over Cartesian product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:694` | numeric equality | none | `pending` |
| B0119 | rule | equality: finite-set Fubini over Cartesian product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:742` | numeric equality | none | `pending` |
| B0120 | rule | equality: sums over bijective enumerations of the same finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:856` | numeric equality | none | `pending` |
| B0121 | rule | equality: a finite range sum of the literal zero function is zero | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:45` | numeric equality | none | `not_this_round` |
| B0122 | rule | equality: finite sums are congruent from pointwise equality on the shared integer range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:164` | numeric equality | none | `pending` |
| B0123 | rule | equality: sum additivity from pointwise equality on the integer index range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:245` | numeric equality | none | `pending` |
| B0124 | rule | equality: finite sum subtraction over a common additive carrier | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:355` | numeric equality | none | `pending` |
| B0125 | rule | equality: merge adjacent sum ranges with the same summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:522` | numeric equality | none | `pending` |
| B0126 | rule | equality: single-term sum equals the summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:568` | numeric equality | none | `pending` |
| B0127 | rule | equality: single-term product equals the factor | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:619` | numeric equality | none | `pending` |
| B0128 | rule | equality: sum through e equals sum through e-1 plus last summand f(e) | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:705` | numeric equality | none | `pending` |
| B0129 | rule | equality: product through e equals product through e-1 times last factor f(e) | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:791` | numeric equality | none | `pending` |
| B0130 | rule | equality: sum partitions closed range into adjacent sub-sums with the same summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:916` | numeric equality | none | `pending` |
| B0131 | rule | equality: product partitions closed range into adjacent sub-products with the same factor | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1018` | numeric equality | none | `pending` |
| B0132 | rule | equality: sum reindexing (integer shift) from pointwise equality on the range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1103` | numeric equality | none | `pending` |
| B0133 | rule | equality: sum of a constant summand over a closed integer range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1168` | numeric equality | none | `pending` |
| B0134 | rule | equality: finite sum scalar multiplication | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1251` | numeric equality | none | `pending` |
| B0135 | rule | equality: log(a, a^b) = b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:43` | numeric equality | none | `pending` |
| B0136 | rule | equality: log(a^b, c) = log(a, c) / b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:83` | numeric equality | none | `pending` |
| B0137 | rule | equality: log(a, x^b) = b * log(a, x) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:122` | numeric equality | none | `pending` |
| B0138 | rule | equality: log(a, x*y) = log(a, x) + log(a, y) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:163` | numeric equality | none | `pending` |
| B0139 | rule | equality: log(a, x/y) = log(a, x) - log(a, y) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:202` | numeric equality | none | `pending` |
| B0140 | rule | equality: log(a, 1/x) = -log(a, x) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:295` | numeric equality | none | `pending` |
| B0141 | rule | equality: log(a, b) = log(c, b) / log(c, a) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:370` | numeric equality | none | `pending` |
| B0142 | rule | equality: log(a, a) = 1 | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:409` | numeric equality | none | `pending` |
| B0143 | rule | equality: log(a, 1) = 0 | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:421` | numeric equality | none | `pending` |
| B0144 | rule | equality: log(a, b) = c from a^c = b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:437` | numeric equality | none | `pending` |
| B0145 | rule | equality: a^c = b from c = log(a, b) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:473` | numeric equality | none | `pending` |
| B0146 | rule | equality: nested mod with same modulus absorbs inner mod | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:58` | numeric equality | none | `pending` |
| B0147 | rule | equality: nested mod absorbs an inner modulus divisible by the outer modulus | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:148` | numeric equality | none | `pending` |
| B0148 | rule | equality: mod — peel outer nested % m to reuse known residue equality | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:211` | numeric equality | none | `pending` |
| B0149 | rule | equality: mod — peel outer nested % m to reuse known residue equality | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:242` | numeric equality | none | `pending` |
| B0150 | rule | equality: integer congruence — reduce matching + / - / * operands modulo m | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:305` | numeric equality | none | `pending` |
| B0151 | rule | equality: integer congruence — same modulus, residues for matching + / - / * | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:348` | numeric equality | none | `pending` |
| B0152 | rule | equality: (-n) % k = (k - n % k) % k for n in Z and k in N+ | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:435` | numeric equality | none | `pending` |
| B0153 | rule | equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N+ | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:553` | numeric equality | none | `pending` |
| B0154 | rule | equality: (-1)^(2*m+1) = -1 for m in N | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:90` | numeric equality | none | `pending` |
| B0155 | rule | equality: a^1 = a | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:127` | numeric equality | none | `pending` |
| B0156 | rule | equality: a^0 = 1 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:160` | numeric equality | none | `pending` |
| B0157 | rule | equality: 1^x = 1 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:193` | numeric equality | none | `pending` |
| B0158 | rule | equality: 0^x = 0 for x > 0 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:267` | numeric equality | none | `pending` |
| B0159 | rule | equality: a = 0 from a^n = 0 and n in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:53` | numeric equality | none | `pending` |
| B0160 | rule | equality: positive bases equal from equal nonzero integer powers | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:156` | numeric equality | none | `pending` |
| B0161 | rule | equality: abs(a^n) = abs(a)^n for n in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:227` | numeric equality | none | `pending` |
| B0162 | rule | equality: abs(a^n) = abs(a)^n for n in N over real bases | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:244` | numeric equality | none | `pending` |
| B0163 | rule | equality: abs(a^n) = abs(a)^n for n in Z and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:268` | numeric equality | none | `pending` |
| B0164 | rule | equality: a^(-n) = 1 / a^n for n in N+ and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:405` | numeric equality | none | `pending` |
| B0165 | rule | number in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:454` | numeric equality | none | `pending` |
| B0166 | rule | equality: x^(1/n) = z from x = z^n, n in N+, and z >= 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:488` | numeric equality | none | `pending` |
| B0167 | rule | equality: a^(m+n) = a^m * a^n for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:387` | numeric equality | none | `pending` |
| B0168 | rule | equality: (a^m)^n = a^(m*n) for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:613` | numeric equality | none | `pending` |
| B0169 | rule | equality: (a*b)^x = a^x * b^x for real x over positive real factors, n in N over complex bases, n in N+, or n in Z with nonzero bases | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:791` | numeric equality | none | `pending` |
| B0170 | rule | equality: reduce over an empty closed interval returns its seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:39` | numeric equality | none | `pending` |
| B0171 | rule | equality: literal reduce expands as an ascending left fold | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:105` | numeric equality | none | `not_this_round` |
| B0172 | rule | equality: nonempty reduce satisfies its last-step equation | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:187` | numeric equality | none | `pending` |
| B0173 | rule | equality: finite_set_reduce over the empty set returns its seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:230` | numeric equality | none | `pending` |
| B0174 | rule | equality: finite_set_reduce expands through a finite-set enumeration | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:301` | numeric equality | none | `pending` |
| B0175 | rule | equality: finite_set_reduce over a closed range uses its ascending enumeration | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:344` | numeric equality | none | `pending` |
| B0176 | rule | equality: finite_set_reduce after inserting a fresh element | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:421` | numeric equality | none | `pending` |
| B0177 | rule | equality: additive reduce with seed zero equals range sum | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:461` | numeric equality | none | `pending` |
| B0178 | rule | equality: multiplicative reduce with seed one equals range product | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:482` | numeric equality | none | `pending` |
| B0179 | rule | equality: additive finite_set_reduce with seed zero equals finite_set_sum | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:523` | numeric equality | none | `pending` |
| B0180 | rule | equality: multiplicative finite_set_reduce with seed one equals finite_set_product | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:543` | numeric equality | none | `pending` |
| B0181 | rule | equality: reduce congruence from pointwise equality on the closed range | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:603` | numeric equality | none | `pending` |
| B0182 | rule | equality: finite_set_reduce congruence from fn_eq_in on the finite set | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:640` | numeric equality | none | `pending` |
| B0183 | rule | equality: reduce substitution translates equally long empty intervals | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:732` | numeric equality | none | `pending` |
| B0184 | rule | equality: reduce substitution by an order-preserving interval translation | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:789` | numeric equality | none | `pending` |
| B0185 | rule | equality: nonempty reduce consumes its first value into the seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:882` | numeric equality | none | `pending` |
| B0186 | rule | equality: reduce partitions into adjacent ordered ranges | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:962` | numeric equality | none | `pending` |
| B0187 | rule | equality: finite_set_reduce over a disjoint union preserves the single seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:1062` | numeric equality | none | `pending` |
| B0188 | rule | equality: finite_set_reduce substitution along a bijection | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:1169` | numeric equality | none | `pending` |
| B0189 | rule | sqrt: (sqrt(x))^2 = x | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:34` | numeric equality | none | `pending` |
| B0190 | rule | sqrt: sqrt(0) = 0 and sqrt(1) = 1 | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:80` | numeric equality | none | `pending` |
| B0191 | rule | sqrt: sqrt(a^2) = a for a >= 0 | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:130` | numeric equality | none | `pending` |
| B0192 | rule | sqrt: sqrt(a * b) = sqrt(a) * sqrt(b) | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:200` | numeric equality | none | `pending` |
| B0193 | rule | sqrt: sqrt(a / b) = sqrt(a) / sqrt(b) | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:274` | numeric equality | none | `pending` |
| B0194 | rule | equality: a^2 + b^2 = 0 from a = 0 and b = 0 over R | `src/verify/verify_builtin_rules/equality_numeric/square_sums.rs:44` | numeric equality | none | `pending` |
| B0195 | rule | equality: a = 0 from a^2 + b^2 = 0 over R | `src/verify/verify_builtin_rules/equality_numeric/square_sums.rs:124` | numeric equality | none | `pending` |
| B0196 | rule | known-only equality: they are the same | `src/verify/verify_builtin_rules/equality_structural.rs:42` | equality structural | none | `pending` |
| B0197 | rule | known-only equality: same known equality class | `src/verify/verify_builtin_rules/equality_structural.rs:51` | equality structural | none | `pending` |
| B0198 | rule | calculation | `src/verify/verify_builtin_rules/equality_structural.rs:65` | equality structural | none | `not_this_round` |
| B0199 | rule | known-only equality: resolved objects match | `src/verify/verify_builtin_rules/equality_structural.rs:76` | equality structural | none | `pending` |
| B0200 | rule | they are the same | `src/verify/verify_builtin_rules/equality_structural.rs:516` | equality structural | none | `pending` |
| B0201 | rule | calculation | `src/verify/verify_builtin_rules/equality_structural.rs:532` | equality structural | none | `not_this_round` |
| B0202 | rule | tuple in cart: each component is in the corresponding cart factor | `src/verify/verify_builtin_rules/in_fact_builtin/cart_membership.rs:37` | membership | none | `pending` |
| B0203 | rule | cart membership from symbolic dimension and projections | `src/verify/verify_builtin_rules/in_fact_builtin/cart_membership.rs:108` | membership | none | `pending` |
| B0204 | rule | set-minus membership excludes the right operand | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:85` | membership | none | `pending` |
| B0205 | rule | native imaginary unit is in C | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:182` | membership | none | `pending` |
| B0206 | rule | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:207` | membership | none | `pending` |
| B0207 | rule | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:225` | membership | none | `pending` |
| B0208 | rule | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:243` | membership | none | `pending` |
| B0209 | rule | N: a^k from a in N and k in N | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:335` | membership | none | `pending` |
| B0210 | rule | absolute value of a known nonzero integer is a positive natural | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:406` | membership | none | `pending` |
| B0211 | rule | N+: a^k from a in N+ and k in N | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:428` | membership | none | `pending` |
| B0212 | rule | gcd of a non-all-zero integer pair is a positive integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:448` | membership | none | `pending` |
| B0213 | rule | lcm of two integers is a nonnegative integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:465` | membership | none | `pending` |
| B0214 | rule | floor and ceil return integers | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:476` | membership | none | `pending` |
| B0215 | rule | minimum and maximum of real arguments are real | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:484` | membership | none | `pending` |
| B0216 | rule | real exponential values are positive reals | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:495` | membership | none | `pending` |
| B0217 | rule | natural logarithm of a positive real is real | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:503` | membership | none | `pending` |
| B0218 | rule | the real sign function returns an integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:514` | membership | none | `pending` |
| B0219 | rule | factorial of a natural number is a positive integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:534` | membership | none | `pending` |
| B0220 | rule | Q+: 0 < x and x in Q | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:554` | membership | none | `pending` |
| B0221 | rule | R+: 0 < x and x in R | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:561` | membership | none | `pending` |
| B0222 | rule | finite_seq list: length equals n and each entry in co-domain | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:813` | membership | none | `pending` |
| B0223 | rule | matrix literal: shape matches matrix(...) and each entry in co-domain | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:854` | membership | none | `not_this_round` |
| B0224 | rule | dynamic: format!( "{name}: operation carrier {carrier} is contained in {}", in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:27` | membership | none | `pending` |
| B0225 | rule | refined integer carrier from known integer membership and strict sign | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:80` | membership | none | `pending` |
| B0226 | rule | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:111` | membership | none | `pending` |
| B0227 | rule | finite_set_sum: positive summand over a nonempty finite set | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:165` | membership | none | `pending` |
| B0228 | rule | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:177` | membership | none | `pending` |
| B0229 | rule | finite_set_product: positive factors give a positive finite product | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:202` | membership | none | `pending` |
| B0230 | rule | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:214` | membership | none | `pending` |
| B0231 | rule | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:238` | membership | none | `pending` |
| B0232 | rule | fn application in declared return set or standard numeric superset (well-defined under typing) | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:301` | membership | none | `pending` |
| B0233 | rule | N: a + b from a in N and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:339` | membership | none | `pending` |
| B0234 | rule | N: n - 1 from n in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:376` | membership | none | `pending` |
| B0235 | rule | N: n - 1 from n in N and n > 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:393` | membership | none | `pending` |
| B0236 | rule | N: a - b from a,b in Z and b <= a | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:426` | membership | none | `pending` |
| B0237 | rule | N: a - b from a,b in Z and known nonnegative difference | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:448` | membership | none | `pending` |
| B0238 | rule | N: a * b from a in N and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:490` | membership | none | `pending` |
| B0239 | rule | R+: a^x from 0 < a and x in R | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:570` | membership | none | `pending` |
| B0240 | rule | N+: n - 1 from n in N+ and n > 1 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:617` | membership | none | `pending` |
| B0241 | rule | N+: a + b from a in N+ and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:656` | membership | none | `pending` |
| B0242 | rule | N+: a + b from a in N+ and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:673` | membership | none | `pending` |
| B0243 | rule | N+: a + b from a in N and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:696` | membership | none | `pending` |
| B0244 | rule | N+: a * b from a in N+ and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:734` | membership | none | `pending` |
| B0245 | rule | N+: x in N and x != 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:761` | membership | none | `pending` |
| B0246 | rule | N+: 0 < x and x in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:781` | membership | none | `pending` |
| B0247 | rule | N+: 0 < x and x in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:792` | membership | none | `pending` |
| B0248 | rule | N: x in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:852` | membership | none | `pending` |
| B0249 | rule | N: x in Z and x >= 0 or x > 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:877` | membership | none | `pending` |
| B0250 | rule | in closed_range: a <= i and i <= b | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:917` | membership | none | `pending` |
| B0251 | rule | in range: a <= i and i < b | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:949` | membership | none | `pending` |
| B0252 | rule | in real interval: x in R and endpoint bounds | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:999` | membership | none | `pending` |
| B0253 | rule | in half-infinite real interval: x in R and endpoint bound | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1048` | membership | none | `pending` |
| B0254 | rule | complex scalar arithmetic is closed in C | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1218` | membership | none | `pending` |
| B0255 | rule | real arithmetic has real operands and result | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1268` | membership | none | `pending` |
| B0256 | rule | integer expression closure under +, -, and * | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1341` | membership | none | `pending` |
| B0257 | rule | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1386` | membership | none | `pending` |
| B0258 | rule | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1456` | membership | none | `pending` |
| B0259 | rule | Z closure: arithmetic operands in Z; pow base in Z and exponent in N, or base in N+ and exponent in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1621` | membership | none | `pending` |
| B0260 | rule | Q closure: +-*/ operands in Q; pow base in Q and exponent in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1679` | membership | none | `pending` |
| B0261 | rule | negation maps a positive scalar into the matching negative carrier | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1731` | membership | none | `pending` |
| B0262 | rule | mul_opposite_signs_product_in_negative_reals | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1766` | membership | none | `pending` |
| B0263 | rule | mul_opposite_signs_product_in_negative_rationals | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1785` | membership | none | `pending` |
| B0264 | rule | mul_opposite_signs_product_in_negative_integers | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1808` | membership | none | `pending` |
| B0265 | rule | number in C | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:49` | membership | none | `not_this_round` |
| B0266 | rule | number in C* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:52` | membership | none | `not_this_round` |
| B0267 | rule | number in R | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:57` | membership | none | `not_this_round` |
| B0268 | rule | number in R+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:60` | membership | none | `not_this_round` |
| B0269 | rule | number in R- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:67` | membership | none | `not_this_round` |
| B0270 | rule | number in R* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:74` | membership | none | `not_this_round` |
| B0271 | rule | number in Q | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:79` | membership | none | `not_this_round` |
| B0272 | rule | number in Q+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:82` | membership | none | `not_this_round` |
| B0273 | rule | number in Q- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:89` | membership | none | `not_this_round` |
| B0274 | rule | number in Q* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:96` | membership | none | `not_this_round` |
| B0275 | rule | number in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:103` | membership | none | `not_this_round` |
| B0276 | rule | number in Z- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:110` | membership | none | `not_this_round` |
| B0277 | rule | number in Z* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:117` | membership | none | `not_this_round` |
| B0278 | rule | number in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:124` | membership | none | `not_this_round` |
| B0279 | rule | number in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:131` | membership | none | `not_this_round` |
| B0280 | rule | number not in C* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:148` | membership | none | `not_this_round` |
| B0281 | rule | number not in R+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:155` | membership | none | `not_this_round` |
| B0282 | rule | number not in R- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:162` | membership | none | `not_this_round` |
| B0283 | rule | number not in R* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:169` | membership | none | `not_this_round` |
| B0284 | rule | number not in Q+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:176` | membership | none | `not_this_round` |
| B0285 | rule | number not in Q- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:183` | membership | none | `not_this_round` |
| B0286 | rule | number not in Q* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:190` | membership | none | `not_this_round` |
| B0287 | rule | number not in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:197` | membership | none | `not_this_round` |
| B0288 | rule | number not in Z- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:204` | membership | none | `not_this_round` |
| B0289 | rule | number not in Z* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:211` | membership | none | `not_this_round` |
| B0290 | rule | number not in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:218` | membership | none | `not_this_round` |
| B0291 | rule | number not in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:225` | membership | none | `not_this_round` |
| B0292 | rule | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/operator_signature.rs:95` | membership | none | `pending` |
| B0293 | rule | set-builder membership transport through one unfolded definition | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:64` | membership | none | `pending` |
| B0294 | rule | set-builder membership transport from a known universal named-set membership | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:161` | membership | none | `pending` |
| B0295 | rule | universal set-builder membership eliminates to its defining fact | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:263` | membership | none | `pending` |
| B0296 | rule | set-builder membership eliminates to its instantiated defining fact | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:342` | membership | none | `pending` |
| B0297 | rule | dynamic: format!("union membership: member of the {side_name} side") | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:376` | membership | none | `pending` |
| B0298 | rule | intersection membership: member of both sides | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:422` | membership | none | `pending` |
| B0299 | rule | dynamic: format!("intersection non-membership: non-member of the {side_name} side") | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:453` | membership | none | `pending` |
| B0300 | rule | set-minus membership: member of left side and non-member of right side | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:499` | membership | none | `pending` |
| B0301 | rule | big_union membership: an element of a member set is in the family union | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:523` | membership | none | `pending` |
| B0302 | rule | big_union membership: an element of a member set is in the family union | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:558` | membership | none | `pending` |
| B0303 | rule | replacement membership: a relation witness is in the replacement set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:611` | membership | none | `pending` |
| B0304 | rule | replacement membership: a relation witness is in the replacement set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:644` | membership | none | `pending` |
| B0305 | rule | fn_range membership: a well-defined function application is in the function range | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:831` | membership | none | `pending` |
| B0306 | rule | structural subset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:870` | membership | none | `pending` |
| B0307 | rule | fn_range power_set membership: function range is contained in the codomain | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:882` | membership | none | `pending` |
| B0308 | rule | structural subset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:917` | membership | none | `pending` |
| B0309 | rule | power_set membership: a subset of the base set is an element of the power set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:929` | membership | none | `pending` |
| B0310 | rule | general_cart membership: function into big_union(family) with pointwise factor membership | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:974` | membership | none | `pending` |
| B0311 | rule | set builder membership: element is in the base set and satisfies all defining facts | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1041` | membership | none | `pending` |
| B0312 | rule | membership in a set-valued definition: unfold one function or template definition to a set builder | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1103` | membership | none | `pending` |
| B0313 | rule | dependent struct constructor: each literal tuple field has its instantiated carrier | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1149` | membership | none | `not_this_round` |
| B0314 | rule | struct membership: element is in the named structure carrier and satisfies struct equivalent facts | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1206` | membership | none | `pending` |
| B0315 | rule | finite_set_size of a finite set is a natural number | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1226` | membership | none | `pending` |
| B0316 | rule | dynamic: rule_name.to_string() | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1255` | membership | none | `pending` |
| B0317 | rule | finite-set extremum: member of a standard numeric superset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1283` | membership | none | `pending` |
| B0318 | rule | membership through a known direct set inclusion | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1467` | membership | none | `pending` |
| B0319 | rule | selected literal tuple component has a real carrier | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:52` | membership | none | `not_this_round` |
| B0320 | rule | literal tuple projection inherits the selected component carrier | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:65` | membership | none | `not_this_round` |
| B0321 | rule | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:94` | membership | none | `pending` |
| B0322 | rule | subset reflexivity | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:102` | membership | none | `pending` |
| B0323 | rule | set_builder in power_set: param_set subset of base implies builder defines a subset of base | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:118` | membership | none | `pending` |
| B0324 | rule | list_set in power_set: each element is in the base set | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:153` | membership | none | `pending` |
| B0325 | rule | dynamic: format!( "{} equals one element in list_set {}", in_fact.element, in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:179` | membership | none | `pending` |
| B0326 | rule | dynamic: format!( "{} is not equal to every element in list_set {}", not_in_fact.element, not_in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:218` | membership | none | `pending` |
| B0327 | rule | fn membership: stored fn signature matches RHS | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:338` | membership | none | `pending` |
| B0328 | rule | fn membership: stored fn signature matches RHS (alpha-renamed parameters) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:360` | membership | none | `pending` |
| B0329 | rule | anonymous function: signature (params, dom, co-domain) matches 'fn' set | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:389` | membership | none | `pending` |
| B0330 | rule | anonymous function: signature matches 'fn' set (alpha-renamed parameters) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:412` | membership | none | `pending` |
| B0331 | rule | anonymous function: signature matches 'fn' set through propositionally equal parameter sets | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:432` | membership | none | `pending` |
| B0332 | rule | dynamic: format!( "finite sequence literal application is in {}", target_set_obj ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:503` | membership | none | `not_this_round` |
| B0333 | rule | dynamic: format!( "cart projection list_set elements are all in {}", target_set_obj ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:563` | membership | none | `pending` |
| B0334 | rule | dynamic: format!( "{} in {} implies in {} (standard subset relation)", in_fact.element, standard_subset_set_obj, target_set_obj ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:597` | membership | none | `pending` |
| B0335 | rule | listed-set member inherits a carrier shared by every listed element | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:667` | membership | none | `pending` |
| B0336 | rule | numeric division not in Z: resolved numerator % denominator != 0 | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:698` | membership | none | `pending` |
| B0337 | rule | finite codomain of a surjection from a finite set | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:38` | mapping properties | none | `pending` |
| B0338 | rule | finite injection has range cardinality equal to its source | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:93` | mapping properties | none | `pending` |
| B0339 | rule | finite bijection preserves cardinality | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:164` | mapping properties | none | `pending` |
| B0340 | rule | finite surjection bounds codomain cardinality by source cardinality | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:215` | mapping properties | none | `pending` |
| B0341 | rule | literal/range finite-set structure | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:279` | mapping properties | none | `not_this_round` |
| B0342 | rule | native exp/ln inverse or canonical-base identity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:16` | native exp sign factorial | none | `pending` |
| B0343 | rule | injectivity of native exp | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:41` | native exp sign factorial | none | `pending` |
| B0344 | rule | injectivity of native ln | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:68` | native exp sign factorial | none | `pending` |
| B0345 | rule | sign is zero only at zero | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:99` | native exp sign factorial | none | `pending` |
| B0346 | rule | sign is nonzero exactly for nonzero arguments | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:142` | native exp sign factorial | none | `pending` |
| B0347 | rule | native exp/ln algebra identity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:161` | native exp sign factorial | none | `pending` |
| B0348 | rule | sign value selected from the argument order at zero | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:199` | native exp sign factorial | none | `pending` |
| B0349 | rule | sign times absolute value restores the argument | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:217` | native exp sign factorial | none | `pending` |
| B0350 | rule | native sign oddness or multiplicativity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:240` | native exp sign factorial | none | `pending` |
| B0351 | rule | factorial successor recurrence | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:258` | native exp sign factorial | none | `pending` |
| B0352 | rule | earlier factorial divides later factorial | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:300` | native exp sign factorial | none | `pending` |
| B0353 | rule | native exp/sign/factorial characteristic order bound | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:340` | native exp sign factorial | none | `pending` |
| B0354 | rule | native factorial monotonicity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:405` | native exp sign factorial | none | `pending` |
| B0355 | rule | native sign preserves weak order | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:439` | native exp sign factorial | none | `pending` |
| B0356 | rule | dynamic: format!("native exp/ln reflects {order_kind} order") | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:587` | native exp sign factorial | none | `pending` |
| B0357 | rule | dynamic: format!("native {function_name} preserves {order_kind} order") | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:629` | native exp sign factorial | none | `pending` |
| B0358 | rule | dynamic: format!("{name} fixes integer inputs") | `src/verify/verify_builtin_rules/native_integer_extrema.rs:34` | native integer extrema | none | `pending` |
| B0359 | rule | native floor/ceil negation duality | `src/verify/verify_builtin_rules/native_integer_extrema.rs:55` | native integer extrema | none | `pending` |
| B0360 | rule | native floor/ceil integer translation | `src/verify/verify_builtin_rules/native_integer_extrema.rs:76` | native integer extrema | none | `pending` |
| B0361 | rule | dynamic: format!("{name} selects the ordered argument: {premise_left} <= {premise_right}") | `src/verify/verify_builtin_rules/native_integer_extrema.rs:125` | native integer extrema | none | `pending` |
| B0362 | rule | native rounding/extremum characteristic order bound | `src/verify/verify_builtin_rules/native_integer_extrema.rs:166` | native integer extrema | none | `pending` |
| B0363 | rule | native lcm is bounded by every positive common multiple | `src/verify/verify_builtin_rules/native_integer_extrema.rs:220` | native integer extrema | none | `pending` |
| B0364 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/native_integer_extrema.rs:306` | native integer extrema | none | `pending` |
| B0365 | rule | native min/max lattice identity | `src/verify/verify_builtin_rules/native_integer_extrema.rs:328` | native integer extrema | none | `pending` |
| B0366 | rule | lcm times gcd is the absolute product | `src/verify/verify_builtin_rules/native_integer_extrema.rs:350` | native integer extrema | none | `pending` |
| B0367 | rule | native lcm symmetry, zero law, or divisibility | `src/verify/verify_builtin_rules/native_integer_extrema.rs:372` | native integer extrema | none | `pending` |
| B0368 | rule | Every object is a set. | `src/verify/verify_builtin_rules/non_equational_dispatch.rs:52` | non equational dispatch | none | `pending` |
| B0369 | rule | list_set_different_length | `src/verify/verify_builtin_rules/not_equal_builtin.rs:42` | not equal | none | `pending` |
| B0370 | rule | native real constant distinctness | `src/verify/verify_builtin_rules/not_equal_builtin.rs:186` | not equal | none | `pending` |
| B0371 | rule | well-defined exp/factorial values are strictly positive | `src/verify/verify_builtin_rules/not_equal_builtin.rs:209` | not equal | none | `pending` |
| B0372 | rule | not_equal_numeric_resolved_or_equal_class_calculation | `src/verify/verify_builtin_rules/not_equal_builtin.rs:231` | not equal | none | `not_this_round` |
| B0373 | rule | not_equal_empty_set_from_nonempty | `src/verify/verify_builtin_rules/not_equal_builtin.rs:299` | not equal | none | `pending` |
| B0374 | rule | not_equal_from_known_strict_order | `src/verify/verify_builtin_rules/not_equal_builtin.rs:335` | not equal | none | `pending` |
| B0375 | rule | not_equal_from_known_positive_lower_bound | `src/verify/verify_builtin_rules/not_equal_builtin.rs:407` | not equal | none | `pending` |
| B0376 | rule | not_equal_from_membership_contradiction | `src/verify/verify_builtin_rules/not_equal_builtin.rs:448` | not equal | none | `pending` |
| B0377 | rule | abs_not_equal_zero_from_arg_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:491` | not equal | none | `pending` |
| B0378 | rule | sqrt(x) != 0 from x > 0 | `src/verify/verify_builtin_rules/not_equal_builtin.rs:533` | not equal | none | `pending` |
| B0379 | rule | sub_not_equal_zero_from_operand_not_equal | `src/verify/verify_builtin_rules/not_equal_builtin.rs:581` | not equal | none | `pending` |
| B0380 | rule | add_not_equal_zero_from_operand_not_equal_negation | `src/verify/verify_builtin_rules/not_equal_builtin.rs:642` | not equal | none | `pending` |
| B0381 | rule | operand_not_equal_from_sub_not_equal_zero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:684` | not equal | none | `pending` |
| B0382 | rule | operand_not_equal_negation_from_add_not_equal_zero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:752` | not equal | none | `pending` |
| B0383 | rule | n != 0 from n $in N and 1 <= n | `src/verify/verify_builtin_rules/not_equal_builtin.rs:790` | not equal | none | `pending` |
| B0384 | rule | n != 0 from n $in N and 1 <= n | `src/verify/verify_builtin_rules/not_equal_builtin.rs:802` | not equal | none | `pending` |
| B0385 | rule | not_equal_pow_from_base_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:879` | not equal | none | `pending` |
| B0386 | rule | not_equal_pow_from_positive_base_carrier | `src/verify/verify_builtin_rules/not_equal_builtin.rs:899` | not equal | none | `pending` |
| B0387 | rule | div_not_equal_zero_from_numerator_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:965` | not equal | `div_ne_zero` / `Ne.symm` | `implemented` |
| B0388 | rule | div_not_equal_zero_from_numerator_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:975` | not equal | none | `pending` |
| B0389 | rule | product_nonzero_component: a * b != 0 gives a != 0 and b != 0 | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1068` | not equal | none | `pending` |
| B0390 | rule | square_sum_not_equal_zero_from_nonzero_component_or | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1130` | not equal | none | `pending` |
| B0391 | rule | square_sum_not_equal_zero_from_left_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1144` | not equal | none | `pending` |
| B0392 | rule | square_sum_not_equal_zero_from_right_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1158` | not equal | none | `pending` |
| B0393 | rule | dynamic: rule_label.to_string() | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1483` | not equal | none | `pending` |
| B0394 | rule | every positive common divisor is at most the gcd | `src/verify/verify_builtin_rules/number_compare.rs:73` | number compare | none | `pending` |
| B0395 | rule | less_equal_fact_equal | `src/verify/verify_builtin_rules/number_compare.rs:311` | number compare | none | `pending` |
| B0396 | rule | less_equal_fact_from_known_equality | `src/verify/verify_builtin_rules/number_compare.rs:325` | number compare | none | `pending` |
| B0397 | rule | less_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:342` | number compare | `linarith only` | `implemented` |
| B0398 | rule | greater_equal_fact_equal | `src/verify/verify_builtin_rules/number_compare.rs:356` | number compare | none | `pending` |
| B0399 | rule | greater_equal_fact_from_known_equality | `src/verify/verify_builtin_rules/number_compare.rs:370` | number compare | none | `pending` |
| B0400 | rule | greater_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:389` | number compare | `linarith only` | `implemented` |
| B0401 | rule | native mathematical constant positivity bound | `src/verify/verify_builtin_rules/number_compare.rs:502` | number compare | none | `pending` |
| B0402 | rule | n >= 0 from n $in N | `src/verify/verify_builtin_rules/number_compare.rs:752` | number compare | none | `pending` |
| B0403 | rule | n >= 1 from n $in N+ | `src/verify/verify_builtin_rules/number_compare.rs:800` | number compare | none | `pending` |
| B0404 | rule | finite_nonempty_set_size_at_least_one | `src/verify/verify_builtin_rules/number_compare.rs:862` | number compare | none | `pending` |
| B0405 | rule | finite set cardinality is nonnegative | `src/verify/verify_builtin_rules/number_compare.rs:897` | number compare | none | `pending` |
| B0406 | rule | finite_set_size_subset_le | `src/verify/verify_builtin_rules/number_compare.rs:946` | number compare | none | `pending` |
| B0407 | rule | finite_set_size_subset_le | `src/verify/verify_builtin_rules/number_compare.rs:993` | number compare | none | `pending` |
| B0408 | rule | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1060` | number compare | none | `pending` |
| B0409 | rule | 1 <= n from n $in N and n != 0 | `src/verify/verify_builtin_rules/number_compare.rs:1128` | number compare | none | `pending` |
| B0410 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1202` | number compare | none | `pending` |
| B0411 | rule | 1 <= n from n $in Z and 0 < n | `src/verify/verify_builtin_rules/number_compare.rs:1256` | number compare | none | `pending` |
| B0412 | rule | less_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:1297` | number compare | `linarith only` | `implemented` |
| B0413 | rule | weaken numeric lower bound from known lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1309` | number compare | none | `pending` |
| B0414 | rule | integer weak lower bound from strict predecessor lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1328` | number compare | none | `pending` |
| B0415 | rule | weaken numeric strict lower bound from known lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1362` | number compare | none | `pending` |
| B0416 | rule | weaken numeric upper bound from known upper bound | `src/verify/verify_builtin_rules/number_compare.rs:1459` | number compare | none | `pending` |
| B0417 | rule | 0 <= abs(x) for x in R | `src/verify/verify_builtin_rules/number_compare.rs:1529` | number compare | none | `pending` |
| B0418 | rule | sqrt: 0 <= sqrt(x) from 0 <= x | `src/verify/verify_builtin_rules/number_compare.rs:1568` | number compare | none | `pending` |
| B0419 | rule | sqrt: 0 < sqrt(x) from 0 < x | `src/verify/verify_builtin_rules/number_compare.rs:1606` | number compare | none | `pending` |
| B0420 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1685` | number compare | none | `pending` |
| B0421 | rule | dynamic: msg.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1703` | number compare | none | `pending` |
| B0422 | rule | order_from_known_negated_complement | `src/verify/verify_builtin_rules/number_compare.rs:1948` | number compare | none | `pending` |
| B0423 | rule | log order: base > 1 preserves strict order | `src/verify/verify_builtin_rules/number_compare.rs:2022` | number compare | none | `pending` |
| B0424 | rule | log order: 0 < base < 1 reverses strict order | `src/verify/verify_builtin_rules/number_compare.rs:2038` | number compare | none | `pending` |
| B0425 | rule | log sign: 0 < log(a, x) from 1 < a and 1 < x | `src/verify/verify_builtin_rules/number_compare.rs:2067` | number compare | none | `pending` |
| B0426 | rule | log sign: log(a, x) < 0 from 1 < a and 0 < x < 1 | `src/verify/verify_builtin_rules/number_compare.rs:2103` | number compare | none | `pending` |
| B0427 | rule | negated_order_from_known_equivalent_order | `src/verify/verify_builtin_rules/number_compare.rs:2178` | number compare | none | `pending` |
| B0428 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2222` | number compare | none | `pending` |
| B0429 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2249` | number compare | none | `pending` |
| B0430 | rule | 0 <= u - v from v <= u | `src/verify/verify_builtin_rules/number_compare.rs:2281` | number compare | `linarith only` | `implemented` |
| B0431 | rule | 0 < u - v from v < u | `src/verify/verify_builtin_rules/number_compare.rs:2307` | number compare | `linarith only` | `implemented` |
| B0432 | rule | 0 <= a + b from known atomic facts 0 <= a and 0 <= b | `src/verify/verify_builtin_rules/number_compare.rs:2368` | number compare | `linarith only` | `implemented` |
| B0433 | rule | 0 < a + b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2417` | number compare | `linarith only` | `implemented` |
| B0434 | rule | 0 < a + b from (0 < a and 0 <= b) | `src/verify/verify_builtin_rules/number_compare.rs:2453` | number compare | `linarith only` | `implemented` |
| B0435 | rule | 0 < a + b from (0 <= a and 0 < b) | `src/verify/verify_builtin_rules/number_compare.rs:2487` | number compare | `linarith only` | `implemented` |
| B0436 | rule | dynamic: msg | `src/verify/verify_builtin_rules/number_compare.rs:2549` | number compare | none | `pending` |
| B0437 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2607` | number compare | none | `pending` |
| B0438 | rule | 0 < a^b from 0 < a and b in R | `src/verify/verify_builtin_rules/number_compare.rs:2652` | number compare | none | `pending` |
| B0439 | rule | 0 <= a^b from 0 < a and b in R | `src/verify/verify_builtin_rules/number_compare.rs:2698` | number compare | none | `pending` |
| B0440 | rule | 0 <= a^n from 0 <= a and n in N+ | `src/verify/verify_builtin_rules/number_compare.rs:2745` | number compare | none | `pending` |
| B0441 | rule | dynamic: msg | `src/verify/verify_builtin_rules/number_compare.rs:2804` | number compare | none | `pending` |
| B0442 | rule | 0 <= a * b from 0 <= a and 0 <= b | `src/verify/verify_builtin_rules/number_compare.rs:2856` | number compare | `mul_nonneg` | `implemented` |
| B0443 | rule | 0 < a * b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2909` | number compare | `mul_pos` | `implemented` |
| B0444 | rule | 0 <= a / b from 0 <= a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2962` | number compare | `div_nonneg` + `le_of_lt` | `implemented` |
| B0445 | rule | 0 < a / b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:3015` | number compare | `div_pos` | `implemented` |
| B0446 | rule | a^n <= b^n from 0 <= a, a <= b, and positive integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:318` | order algebra | none | `pending` |
| B0447 | rule | a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:428` | order algebra | none | `pending` |
| B0448 | rule | a <= b from positive bases and exponent, and a^q <= b^q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:474` | order algebra | none | `pending` |
| B0449 | rule | a^n <= b^n from a <= b and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:517` | order algebra | none | `pending` |
| B0450 | rule | a^n <= b^n from 0 < b <= a and negative integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:567` | order algebra | none | `pending` |
| B0451 | rule | a^k <= b^k from abs(a) <= abs(b) and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:608` | order algebra | none | `pending` |
| B0452 | rule | a^k < b^k from abs(a) < abs(b) and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:648` | order algebra | none | `pending` |
| B0453 | rule | abs(x) <= abs(y) from x^k <= y^k and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:707` | order algebra | none | `pending` |
| B0454 | rule | a^q < b^q from 0 < a, 0 < b, a < b, 0 < q, and q in R or Q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:768` | order algebra | none | `pending` |
| B0455 | rule | a < b from positive bases and exponent, and a^q < b^q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:811` | order algebra | none | `pending` |
| B0456 | rule | a^n < b^n from a < b and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:854` | order algebra | none | `pending` |
| B0457 | rule | a^n <= 0 from a <= 0 and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:887` | order algebra | none | `pending` |
| B0458 | rule | a^n < 0 from a < 0 and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:920` | order algebra | none | `pending` |
| B0459 | rule | a^n < b^n from 0 <= a, a < b, and positive integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:972` | order algebra | none | `pending` |
| B0460 | rule | x1 * x2 <= y1 * y2 from 0 <= factors and componentwise <= | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1096` | order algebra | none | `pending` |
| B0461 | rule | a * b <= 0 from a <= 0 and 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1128` | order algebra | none | `pending` |
| B0462 | rule | 0 <= a * b from a,b having the same weak sign | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1168` | order algebra | none | `pending` |
| B0463 | rule | a * b < 0 from opposite strict signs | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1201` | order algebra | none | `pending` |
| B0464 | rule | 0 < a * b from same strict signs | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1248` | order algebra | none | `pending` |
| B0465 | rule | finite sum monotonicity from pointwise order on the index range | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1352` | order algebra | none | `pending` |
| B0466 | rule | finite-set sum monotonicity from pointwise order on the finite set | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1414` | order algebra | none | `pending` |
| B0467 | rule | finite-set sum: non-negative summand is at most the total | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1484` | order algebra | none | `pending` |
| B0468 | rule | a / c <= b / c from 0 < c and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1547` | order algebra | none | `pending` |
| B0469 | rule | b / c <= a / c from c < 0 and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1571` | order algebra | none | `pending` |
| B0470 | rule | u + a <= u + b from a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1666` | order algebra | `linarith only` | `implemented` |
| B0471 | rule | a - c <= b from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1691` | order algebra | `linarith only` | `implemented` |
| B0472 | rule | a - c <= b from a <= b + c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1710` | order algebra | none | `pending` |
| B0473 | rule | a <= a + b from 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1733` | order algebra | `linarith only` | `implemented` |
| B0474 | rule | a <= b + c from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1753` | order algebra | none | `pending` |
| B0475 | rule | a <= b + c from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1768` | order algebra | none | `pending` |
| B0476 | rule | a <= b - c from a + c <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1786` | order algebra | none | `pending` |
| B0477 | rule | a <= x - n from a + n <= x | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1803` | order algebra | none | `pending` |
| B0478 | rule | a - n <= a for n >= 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1819` | order algebra | none | `pending` |
| B0479 | rule | a + b <= 0 from a <= 0 and b <= 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1840` | order algebra | none | `pending` |
| B0480 | rule | a <= b * a from 0 <= a and 1 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1898` | order algebra | none | `pending` |
| B0481 | rule | k * a <= k * b from 0 <= k and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1920` | order algebra | none | `pending` |
| B0482 | rule | k * a <= k * b from k <= 0 and b <= a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1920` | order algebra | none | `pending` |
| B0483 | rule | a * k <= b * k from 0 <= k and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1934` | order algebra | none | `pending` |
| B0484 | rule | a * k <= b * k from k <= 0 and b <= a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1934` | order algebra | none | `pending` |
| B0485 | rule | a + c <= b + d from a <= b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1971` | order algebra | `linarith only` | `implemented` |
| B0486 | rule | a - d <= b - c from a <= b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2006` | order algebra | none | `pending` |
| B0487 | rule | a <= b / c from 0 < c and (c * a <= b or a * c <= b) | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2062` | order algebra | none | `pending` |
| B0488 | rule | a <= b * c from 0 < c and a / c <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2112` | order algebra | none | `pending` |
| B0489 | rule | a / c < b / c from 0 < c and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2154` | order algebra | none | `pending` |
| B0490 | rule | b / c < a / c from c < 0 and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2178` | order algebra | none | `pending` |
| B0491 | rule | u + a < u + b from a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2245` | order algebra | `linarith only` | `implemented` |
| B0492 | rule | a - d < b - c from a < b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2277` | order algebra | none | `pending` |
| B0493 | rule | a - d < b - c from a <= b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2303` | order algebra | none | `pending` |
| B0494 | rule | abs(x - n) < abs(x) for positive x and nonnegative x - n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2328` | order algebra | none | `pending` |
| B0495 | rule | a - c < b from a < b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2353` | order algebra | none | `pending` |
| B0496 | rule | a - c < b from a <= b and 0 < c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2372` | order algebra | none | `pending` |
| B0497 | rule | a - c < b from a < b + c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2388` | order algebra | none | `pending` |
| B0498 | rule | a < a + b from 0 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2411` | order algebra | none | `pending` |
| B0499 | rule | a < b + c from a < b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2428` | order algebra | none | `pending` |
| B0500 | rule | a < b + c from a < c and 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2443` | order algebra | none | `pending` |
| B0501 | rule | a < b - c from a + c < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2461` | order algebra | none | `pending` |
| B0502 | rule | a - n < a for n > 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2475` | order algebra | none | `pending` |
| B0503 | rule | a / b < a from 0 < a and 1 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2500` | order algebra | none | `pending` |
| B0504 | rule | a + b < 0 from one negative term and one nonpositive term | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2530` | order algebra | none | `pending` |
| B0505 | rule | a < b * a from 0 < a and 1 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2590` | order algebra | none | `pending` |
| B0506 | rule | k * a < k * b from 0 < k and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2601` | order algebra | none | `pending` |
| B0507 | rule | k * a < k * b from k < 0 and b < a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2601` | order algebra | none | `pending` |
| B0508 | rule | a * k < b * k from 0 < k and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2615` | order algebra | none | `pending` |
| B0509 | rule | a * k < b * k from k < 0 and b < a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2615` | order algebra | none | `pending` |
| B0510 | rule | a + c < b + d from a < b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2647` | order algebra | `linarith only` | `implemented` |
| B0511 | rule | a + c < b + d from a < b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2673` | order algebra | `linarith only` | `implemented` |
| B0512 | rule | a + c < b + d from a <= b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2699` | order algebra | `linarith only` | `implemented` |
| B0513 | rule | positive even integer is greater than one | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:162` | order semantics | none | `pending` |
| B0514 | rule | order: transitivity through a shared ordered numeric middle term | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:244` | order semantics | none | `pending` |
| B0515 | rule | finite_set_max: every member is at most the maximum | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:281` | order semantics | none | `pending` |
| B0516 | rule | finite_set_max: every member is at most a known-equal maximum | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:310` | order semantics | none | `pending` |
| B0517 | rule | finite_set_min: the minimum is at most every member | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:331` | order semantics | none | `pending` |
| B0518 | rule | finite_set_min: a known-equal minimum is at most every member | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:360` | order semantics | none | `pending` |
| B0519 | rule | membership by concrete finite-set structure | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:388` | order semantics | none | `pending` |
| B0520 | rule | integer difference: a < b gives b - a >= 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:472` | order semantics | none | `pending` |
| B0521 | rule | integer adjacency: a < b + 1 gives a <= b | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:500` | order semantics | none | `pending` |
| B0522 | rule | integer successor: a < b gives a + 1 <= b | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:524` | order semantics | none | `pending` |
| B0523 | rule | integer predecessor: a < b gives a <= b - 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:548` | order semantics | none | `pending` |
| B0524 | rule | integer singleton interval: n <= x < n + 1 gives x = n | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:591` | order semantics | none | `pending` |
| B0525 | rule | integer successor singleton interval: n < x <= n + 1 gives x = n + 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:625` | order semantics | none | `pending` |
| B0526 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:680` | order semantics | none | `pending` |
| B0527 | rule | deterministic primality computation for u64 | `src/verify/verify_builtin_rules/prime_builtin.rs:23` | prime | none | `not_this_round` |
| B0528 | rule | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/set_relation_duality.rs:34` | set relation duality | none | `pending` |
| B0529 | rule | union subset from both operand subsets | `src/verify/verify_builtin_rules/set_relation_duality.rs:64` | set relation duality | none | `pending` |
| B0530 | rule | literal finite-set subset from member facts | `src/verify/verify_builtin_rules/set_relation_duality.rs:95` | set relation duality | none | `not_this_round` |
| B0531 | rule | Cartesian-product subset from componentwise subsets | `src/verify/verify_builtin_rules/set_relation_duality.rs:131` | set relation duality | none | `pending` |
| B0532 | rule | standard_set_subset | `src/verify/verify_builtin_rules/set_relation_duality.rs:148` | set relation duality | none | `pending` |
| B0533 | rule | integer range is contained in its standard numeric carrier | `src/verify/verify_builtin_rules/set_relation_duality.rs:192` | set relation duality | none | `pending` |
| B0534 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:206` | set relation duality | none | `pending` |
| B0535 | rule | real_interval_subset_R | `src/verify/verify_builtin_rules/set_relation_duality.rs:221` | set relation duality | none | `pending` |
| B0536 | rule | structural subset | `src/verify/verify_builtin_rules/set_relation_duality.rs:244` | set relation duality | none | `pending` |
| B0537 | rule | fn_range_subset_codomain | `src/verify/verify_builtin_rules/set_relation_duality.rs:255` | set relation duality | none | `pending` |
| B0538 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:276` | set relation duality | none | `pending` |
| B0539 | rule | standard_set_superset | `src/verify/verify_builtin_rules/set_relation_duality.rs:300` | set relation duality | none | `pending` |
| B0540 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:317` | set relation duality | none | `pending` |
| B0541 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:335` | set relation duality | none | `pending` |
| B0542 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:364` | set relation duality | none | `pending` |
| B0543 | rule | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:393` | set relation duality | none | `pending` |
| B0544 | rule | dynamic: reason | `src/verify/verify_builtin_rules/trigonometry.rs:155` | trigonometry | none | `pending` |
| B0545 | rule | dynamic: format!( "trigonometry layer {}: {} derived from the unit-circle identity", TrigLemma::Bounds.level(), TrigLemma::Bounds.name() ) | `src/verify/verify_builtin_rules/trigonometry.rs:197` | trigonometry | none | `pending` |
| B0546 | rule | trigonometry: -1 <= sin/cos <= 1 from the unit-circle square bound | `src/verify/verify_builtin_rules/trigonometry.rs:225` | trigonometry | none | `pending` |
| B0547 | rule | dynamic: format!("trigonometry: {reason}") | `src/verify/verify_builtin_rules/trigonometry.rs:561` | trigonometry | none | `pending` |
| B0548 | rule | trigonometry: sine/cosine is nonzero on a canonical sign interval | `src/verify/verify_builtin_rules/trigonometry.rs:669` | trigonometry | none | `pending` |
| B0549 | rule | trigonometry: pi shift changes only sign, preserving non-zero | `src/verify/verify_builtin_rules/trigonometry.rs:689` | trigonometry | none | `pending` |
| B0550 | rule | trigonometry: non-zero transfer through canonical expansion | `src/verify/verify_builtin_rules/trigonometry.rs:712` | trigonometry | none | `pending` |
| B0551 | rule | trigonometry core: tan/cot quotient definition | `src/verify/verify_builtin_rules/trigonometry.rs:1072` | trigonometry | none | `pending` |
| B0552 | rule | trigonometry core: sin(x)^2 + cos(x)^2 = 1 | `src/verify/verify_builtin_rules/trigonometry.rs:1092` | trigonometry | none | `pending` |
| B0553 | rule | trigonometry core: sine addition formula | `src/verify/verify_builtin_rules/trigonometry.rs:1194` | trigonometry | none | `pending` |
| B0554 | rule | nonempty_set_from_not_equal_empty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:22` | type predicates | none | `pending` |
| B0555 | rule | standard_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:41` | type predicates | existential witness `0` (`R` shape) | `implemented` |
| B0556 | rule | list_set_nonempty_has_member_in_syntax | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:53` | type predicates | none | `pending` |
| B0557 | rule | power_set_is_nonempty_because_empty_set_is_subset | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:65` | type predicates | none | `pending` |
| B0558 | rule | closed_range_nonempty_when_start_le_end | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:87` | type predicates | none | `pending` |
| B0559 | rule | range_nonempty_when_start_lt_end | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:109` | type predicates | none | `pending` |
| B0560 | rule | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:154` | type predicates | none | `pending` |
| B0561 | rule | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:180` | type predicates | none | `pending` |
| B0562 | rule | union_is_nonempty_set_when_left_side_is_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:200` | type predicates | none | `pending` |
| B0563 | rule | union_is_nonempty_set_when_right_side_is_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:218` | type predicates | none | `pending` |
| B0564 | rule | dynamic: format!( "sets '{}' in '{}' are nonempty sets", cart.args .iter() .map(\|arg\| arg.as_ref().to_string()) .collect::<Vec<String>>() .join(", "), cart.to_string() ) | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:246` | type predicates | none | `pending` |
| B0565 | rule | fn_set_is_nonempty_when_ret_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:272` | type predicates | none | `pending` |
| B0566 | rule | fn_set_is_nonempty_when_ret_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:293` | type predicates | none | `pending` |
| B0567 | rule | finite_seq_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:315` | type predicates | none | `pending` |
| B0568 | rule | seq_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:336` | type predicates | none | `pending` |
| B0569 | rule | matrix_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:357` | type predicates | none | `pending` |
| B0570 | rule | nonempty_set_from_equal_structural_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:387` | type predicates | none | `pending` |
| B0571 | rule | nonempty_finite_set_from_positive_finite_set_size | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:432` | type predicates | none | `pending` |
| B0572 | rule | list_set_finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:454` | type predicates | none | `pending` |
| B0573 | rule | closed_range_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:462` | type predicates | none | `pending` |
| B0574 | rule | range_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:470` | type predicates | none | `pending` |
| B0575 | rule | set-builder over a finite base is finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:491` | type predicates | none | `pending` |
| B0576 | rule | fn_range_is_finite_set_when_domain_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:520` | type predicates | none | `pending` |
| B0577 | rule | union_is_finite_set_when_both_sides_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:556` | type predicates | none | `pending` |
| B0578 | rule | intersect_is_finite_set_when_both_sides_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:589` | type predicates | none | `pending` |
| B0579 | rule | set_minus_is_finite_set_when_left_side_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:611` | type predicates | none | `pending` |
| B0580 | rule | set_diff_is_finite_set_when_both_sides_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:644` | type predicates | none | `pending` |
| B0581 | rule | power_set_is_finite_set_when_base_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:666` | type predicates | none | `pending` |
| B0582 | rule | cart_is_finite_set_when_all_factors_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:693` | type predicates | none | `pending` |
| B0583 | rule | set_minus_is_infinite_when_left_side_is_infinite_and_right_side_is_finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:750` | type predicates | none | `pending` |
| B0584 | rule | any 'cart' object is a cart | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:768` | type predicates | none | `pending` |
| B0585 | rule | any 'cart_dim' object is a cart_dim | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:791` | type predicates | none | `pending` |
| B0586 | rule | it is a known tuple | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:806` | type predicates | none | `pending` |
| B0587 | rule | list_set_empty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:828` | type predicates | none | `pending` |
| B0588 | rule | finite_set_size_zero_is_not_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:848` | type predicates | none | `pending` |
| B0589 | rule | not_nonempty_set_from_equal_empty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:864` | type predicates | none | `pending` |
| B0590 | rule | closed_range_empty_when_end_lt_start | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:885` | type predicates | none | `pending` |
| B0591 | rule | range_empty_when_end_le_start | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:906` | type predicates | none | `pending` |
| B0592 | rule | dynamic: label.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:947` | type predicates | none | `pending` |
| B0593 | strategy | finite-set product congruence strategy: prove pointwise factor equality | `src/verify/verify_builtin_strategies/equality.rs:68` | builtin strategy | none | `pending` |
| B0594 | strategy | finite-extremum equality strategy: prove both weak-order directions | `src/verify/verify_builtin_strategies/equality.rs:119` | builtin strategy | none | `pending` |
| B0595 | strategy | mod-congruence strategy: reduce immediate binary operands modulo m | `src/verify/verify_builtin_strategies/equality.rs:203` | builtin strategy | none | `pending` |
| B0596 | strategy | numeric-carrier strategy: cardinality of a structurally finite set | `src/verify/verify_builtin_strategies/numeric_carrier.rs:34` | builtin strategy | none | `pending` |
| B0597 | strategy | numeric-carrier strategy: finite extremum source is real-valued | `src/verify/verify_builtin_strategies/numeric_carrier.rs:50` | builtin strategy | none | `pending` |
| B0598 | strategy | dynamic: format!( "numeric-carrier strategy: base carrier and sign conditions for {target}" ) | `src/verify/verify_builtin_strategies/numeric_carrier.rs:65` | builtin strategy | none | `pending` |
| B0599 | strategy | dynamic: format!("numeric-carrier strategy: structural closure in {target}") | `src/verify/verify_builtin_strategies/numeric_carrier.rs:92` | builtin strategy | none | `pending` |
| B0600 | strategy | numeric-carrier strategy: structural closure in N+ | `src/verify/verify_builtin_strategies/numeric_carrier.rs:346` | builtin strategy | none | `pending` |
| B0601 | strategy | additive sign strategy: normalized order goal | `src/verify/verify_builtin_strategies/numeric_sign.rs:21` | builtin strategy | none | `pending` |
| B0602 | strategy | dynamic: strategy_label | `src/verify/verify_builtin_strategies/numeric_sign.rs:35` | builtin strategy | recursive typed arithmetic evidence (`linarith only`) | `implemented` |
| B0603 | strategy | dynamic: strategy_label | `src/verify/verify_builtin_strategies/numeric_sign.rs:41` | builtin strategy | none | `pending` |
| B0604 | strategy | additive sign strategy: nonnegative summands | `src/verify/verify_builtin_strategies/numeric_sign.rs:71` | builtin strategy | none | `pending` |
| B0605 | strategy | additive sign strategy: one positive and one nonnegative summand | `src/verify/verify_builtin_strategies/numeric_sign.rs:89` | builtin strategy | none | `pending` |
| B0606 | strategy | set-membership strategy: constructor membership decomposition | `src/verify/verify_builtin_strategies/set_membership.rs:122` | builtin strategy | none | `pending` |
| B0607 | strategy | set-builder membership strategy: unfold one set definition and verify its atomic obligations | `src/verify/verify_builtin_strategies/set_membership.rs:259` | builtin strategy | none | `pending` |
| B0608 | strategy | set-containment strategy: constructor containment decomposition | `src/verify/verify_builtin_strategies/set_membership.rs:324` | builtin strategy | none | `pending` |
| B0609 | strategy | dynamic: reason.to_string() | `src/verify/verify_builtin_strategies/type_predicates.rs:110` | builtin strategy | none | `pending` |
| B0610 | strategy | nonempty-set strategy: closed integer range has ordered endpoints | `src/verify/verify_builtin_strategies/type_predicates.rs:153` | builtin strategy | none | `pending` |
| B0611 | strategy | nonempty-set strategy: half-open integer range has strictly ordered endpoints | `src/verify/verify_builtin_strategies/type_predicates.rs:176` | builtin strategy | none | `pending` |
| B0612 | strategy | dynamic: reason.to_string() | `src/verify/verify_builtin_strategies/type_predicates.rs:215` | builtin strategy | none | `pending` |
| B0613 | strategy | nonempty-set strategy: a union has a nonempty side | `src/verify/verify_builtin_strategies/type_predicates.rs:229` | builtin strategy | none | `pending` |
| B0614 | strategy | nonempty-set strategy: all Cartesian factors are nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:252` | builtin strategy | none | `pending` |
| B0615 | strategy | nonempty-set strategy: function codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:260` | builtin strategy | none | `pending` |
| B0616 | strategy | nonempty-set strategy: anonymous-function codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:265` | builtin strategy | none | `pending` |
| B0617 | strategy | nonempty-set strategy: finite-sequence codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:270` | builtin strategy | none | `pending` |
| B0618 | strategy | nonempty-set strategy: sequence codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:275` | builtin strategy | none | `pending` |
| B0619 | strategy | nonempty-set strategy: matrix entry set is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:280` | builtin strategy | none | `pending` |
| B0620 | rule | dynamic: same_shape_and_equal_args_reason(&equal_fact.left, &equal_fact.right) | `src/verify/verify_equality.rs:45` | equality | none | `pending` |
| B0621 | rule | builtin rules | `src/verify/verify_equality.rs:472` | equality | none | `pending` |
| B0622 | rule | dynamic: same_shape_and_equal_args_reason(left_obj, right_obj) | `src/verify/verify_equality.rs:505` | equality | none | `pending` |
| B0623 | rule | exist: real-line comparison witness | `src/verify/verify_exist_fact.rs:581` | exist fact | none | `pending` |
| B0624 | rule | exist: member of a nonempty set | `src/verify/verify_exist_fact.rs:600` | exist fact | none | `pending` |
| B0625 | rule | dynamic: if exist_fact.is_exist_unique() { "exist!: unique rational reduced fraction with positive denominator" .to_string() } else { "exist: rational reduced fraction with positive denominator".to_string() } | `src/verify/verify_exist_fact.rs:621` | exist fact | none | `pending` |
| B0626 | rule | exist: rational representation with positive integer denominator | `src/verify/verify_exist_fact.rs:651` | exist fact | none | `pending` |
| B0627 | rule | exist: rational integer ratio representation | `src/verify/verify_exist_fact.rs:676` | exist fact | none | `pending` |
| B0628 | rule | exist!: unique Euclidean quotient for an integer and positive divisor | `src/verify/verify_exist_fact.rs:703` | exist fact | none | `pending` |
| B0629 | rule | exist: zero remainder gives an integer multiple of a nonzero modulus | `src/verify/verify_exist_fact.rs:759` | exist fact | none | `pending` |
| B0630 | rule | exist: Archimedean reciprocal bound | `src/verify/verify_exist_fact.rs:790` | exist fact | none | `pending` |
| B0631 | rule | exist: rational density in the real line | `src/verify/verify_exist_fact.rs:817` | exist fact | none | `pending` |
| B0632 | rule | exist: real density by the midpoint principle | `src/verify/verify_exist_fact.rs:845` | exist fact | none | `pending` |
| B0633 | rule | dynamic: rule.to_string() | `src/verify/verify_exist_fact.rs:886` | exist fact | none | `pending` |
| B0634 | rule | finite nonempty natural set has a greatest member | `src/verify/verify_exist_fact.rs:1042` | exist fact | none | `pending` |
| B0635 | rule | fn_eq_in: pointwise equality on the given set (forall x in S, f(x)=g(x)) | `src/verify/verify_fn_equal_in_builtin.rs:56` | fn equal in | none | `pending` |
| B0636 | rule | fn_eq: exact known pointwise forall over alpha-equivalent function carriers | `src/verify/verify_fn_equal_in_builtin.rs:108` | fn equal in | none | `pending` |
| B0637 | rule | fn_eq: mutual function-space membership and pointwise equality (forall+dom) | `src/verify/verify_fn_equal_in_builtin.rs:167` | fn equal in | none | `pending` |
| B0638 | rule | dynamic: format!( "anonymous fn satisfies a declared return set through an equal {}", representative_kind ) | `src/verify/verify_fn_membership_by_definition.rs:65` | fn membership by definition | none | `pending` |
| B0639 | rule | indexed result inherits its carrier from a symbolic Cartesian projection | `src/verify/verify_fn_membership_by_definition.rs:156` | fn membership by definition | none | `pending` |
| B0640 | rule | fn membership: same input domain and pointwise values lie in the target return set | `src/verify/verify_fn_membership_by_definition.rs:204` | fn membership by definition | none | `pending` |
| B0641 | rule | fnset equality: mutual implication of param sets, dom facts, and ret set | `src/verify/verify_fn_set_equality_builtin_rule.rs:34` | fn set equality builtin rule | none | `pending` |
| B0642 | rule | forall over empty parameter set | `src/verify/verify_forall_fact.rs:197` | forall fact | none | `pending` |
| B0643 | rule | forall iff: then=>iff and iff=>then verified | `src/verify/verify_forall_fact_with_iff.rs:38` | forall fact with iff | none | `pending` |
| B0644 | rule | dynamic: format!( "{} by its builtin function-property definition", fact.predicate ) | `src/verify/verify_function_properties_builtin.rs:26` | function properties | none | `pending` |
| B0645 | rule | restricted builtin premise: each conjunct verified | `src/verify/verify_helper.rs:198` | helper | none | `pending` |
| B0646 | rule | restricted builtin premise: one branch verified | `src/verify/verify_helper.rs:236` | helper | none | `pending` |
| B0647 | rule | registered reflexive prop | `src/verify/verify_non_equational_atomic_fact.rs:131` | non equational atomic fact | none | `pending` |
| B0648 | rule | dynamic: reason.to_string() | `src/verify/verify_or_fact.rs:456` | or fact | none | `pending` |
| B0649 | rule | or: complementary atomic facts | `src/verify/verify_or_fact.rs:475` | or fact | none | `pending` |
| B0650 | rule | or: complementary order relations (strict vs non-strict) on the same real terms | `src/verify/verify_or_fact.rs:494` | or fact | none | `pending` |
| B0651 | rule | or: equality plus strict order covers a known weak order | `src/verify/verify_or_fact.rs:515` | or fact | none | `pending` |
| B0652 | rule | or: abs(x) is x or -x | `src/verify/verify_or_fact.rs:529` | or fact | none | `pending` |
| B0653 | rule | or: complete residue classes modulo a positive integer | `src/verify/verify_or_fact.rs:542` | or fact | none | `pending` |
| B0654 | rule | dynamic: format!( "or: classical implication packaging; '{}' follows under '{}'", conclusion, assumed_opposite ) | `src/verify/verify_or_fact.rs:641` | or fact | none | `pending` |
| B0655 | rule | or: integer lower bound split into finite successors and strict tail | `src/verify/verify_or_fact.rs:688` | or fact | none | `pending` |
| B0656 | rule | zero_product_split: a * b = 0 gives a = 0 or b = 0 | `src/verify/verify_or_fact.rs:747` | or fact | none | `pending` |
| B0657 | rule | or: square sum nonzero implies one component nonzero | `src/verify/verify_or_fact.rs:811` | or fact | none | `pending` |
| B0658 | rule | dynamic: format!( "{} by its builtin proper-set-relation definition", atomic_fact.key() ) | `src/verify/verify_proper_set_relations_builtin.rs:25` | proper set relations | none | `pending` |
