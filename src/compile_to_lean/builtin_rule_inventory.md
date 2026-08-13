# Litex-to-Lean Builtin Rule Inventory

Generated from production Rust source by
[`generate_builtin_inventory.py`](generate_builtin_inventory.py).
Do not hand-edit the table; update the generator's mapping policy and regenerate.

## Scope and counting contract

The inventory contains **666 label-bearing builtin success sites**:
**638 builtin-rule sites** and **28 builtin-strategy sites**.
The lower-level source contains 473 direct success-constructor calls; expanding
their forwarding helpers exposes the label-bearing sites below. The repository's
informal 'about 500 rules' estimate is therefore closest to the 563
distinct static labels, while 666 is the exhaustive source-site count used here.
Forwarding helpers such as a constructor receiving `reason.to_string()` are
collapsed into their outer label-bearing callers. This is why the count is a
semantic call-site count rather than a raw constructor grep. A dynamic site
appears once with its source expression even when it can render several labels
at runtime.

`Mechanism class` describes the executable proof shape independently of
the diagnostic label. The classification is deliberately conservative:
unaudited or mixed branches remain `legacy_custom`.

Of these sites, 591 have a static string label and 75 use
a dynamic label expression. 47 evaluation/computation-like sites
are explicitly marked `not_this_round`. The classification is intentionally
conservative and source-derived; it does not claim one Rust site equals one
mathematical theorem schema.

A Lean mapping is recorded only when the universal-`LitexObject` backend
currently emits and the Lean kernel checks that theorem call. `partial` means
the source site recognizes more cases than the current target theorem; `none`
means no checked mapping exists yet. The deleted native-carrier adapter catalog
does not count as implementation. This table inventories source sites, not
mathematical theorem schemas.

Regenerate or audit drift with:

```text
python3 src/compile_to_lean/generate_builtin_inventory.py --write
python3 src/compile_to_lean/generate_builtin_inventory.py --check
```

## Summary

| Metric | Count |
| --- | ---: |
| Total label-bearing sites | 666 |
| Direct success-constructor calls | 473 |
| Builtin rules | 638 |
| Builtin strategies | 28 |
| Static labels | 591 |
| Distinct static labels | 563 |
| Dynamic label expressions | 75 |
| Evaluation/computation (`not_this_round`) | 47 |
| Checked Lean mappings currently implemented | 1 |
| Partially mapped Lean source sites | 6 |
| Forwarding sink functions discovered | 21 |
| Mechanism: `local_schema` | 43 |
| Mechanism: `reflection` | 46 |
| Mechanism: `transform` | 2 |
| Mechanism: `strategy` | 28 |
| Mechanism: `definition` | 17 |
| Mechanism: `quantified` | 12 |
| Mechanism: `legacy_custom` | 518 |

## Rule sites

| ID | Kind | Mechanism class | Label or dynamic expression | Source | Family | Checked Lean mapping | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| B0001 | rule | `legacy_custom` | real matrix operator has the requested matrix type | `src/execute/by_stmt/thm_by_stmt.rs:827` | execution bridge | none | `pending` |
| B0002 | rule | `legacy_custom` | trusted file load | `src/execute/exec_fact_stmt.rs:57` | execution bridge | none | `not_this_round` |
| B0003 | rule | `local_schema` | dynamic: format!( "existential projection from prop definition '{}'", definition.name ) | `src/execute/exec_obtain_obj.rs:357` | execution bridge | none | `pending` |
| B0004 | rule | `local_schema` | dynamic: format!("local builtin {}", rule.id().as_str()) | `src/verify/local_builtin_catalog/verify.rs:81` | verify | none | `pending` |
| B0005 | rule | `definition` | prime by trial-division definition | `src/verify/verify_atomic_fact_by_definition.rs:59` | atomic fact by definition | none | `pending` |
| B0006 | rule | `definition` | coprime by natural gcd-one definition | `src/verify/verify_atomic_fact_by_definition.rs:88` | atomic fact by definition | none | `pending` |
| B0007 | rule | `definition` | subset by definition (forall x in left: x in right) | `src/verify/verify_atomic_fact_by_definition.rs:158` | atomic fact by definition | none | `pending` |
| B0008 | rule | `definition` | superset by definition (forall x in right: x in left) | `src/verify/verify_atomic_fact_by_definition.rs:194` | atomic fact by definition | none | `pending` |
| B0009 | rule | `legacy_custom` | replay-safe structural equality | `src/verify/verify_builtin_rule.rs:52` | builtin rule | none | `pending` |
| B0010 | rule | `legacy_custom` | replay-safe structural equality | `src/verify/verify_builtin_rule.rs:100` | builtin rule | none | `pending` |
| B0011 | rule | `local_schema` | number comparison | `src/verify/verify_builtin_rule.rs:190` | builtin rule | none | `pending` |
| B0012 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rule.rs:219` | builtin rule | none | `pending` |
| B0013 | rule | `legacy_custom` | abs: x <= abs(x) and -x <= abs(x) | `src/verify/verify_builtin_rules/abs_order_builtin.rs:235` | abs order | none | `pending` |
| B0014 | rule | `legacy_custom` | abs: -abs(x) <= x | `src/verify/verify_builtin_rules/abs_order_builtin.rs:249` | abs order | none | `pending` |
| B0015 | rule | `legacy_custom` | abs: finite sum triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:333` | abs order | none | `pending` |
| B0016 | rule | `legacy_custom` | abs: finite-set sum triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:396` | abs order | none | `pending` |
| B0017 | rule | `local_schema` | abs: 0 < abs(x) from x != 0 | `src/verify/verify_builtin_rules/abs_order_builtin.rs:429` | abs order | none | `pending` |
| B0018 | rule | `legacy_custom` | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/abs_order_builtin.rs:481` | abs order | none | `pending` |
| B0019 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:519` | abs order | none | `pending` |
| B0020 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:542` | abs order | none | `pending` |
| B0021 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:562` | abs order | none | `pending` |
| B0022 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:580` | abs order | none | `pending` |
| B0023 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:608` | abs order | none | `pending` |
| B0024 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:637` | abs order | none | `pending` |
| B0025 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/abs_order_builtin.rs:662` | abs order | none | `pending` |
| B0026 | rule | `legacy_custom` | abs: triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:735` | abs order | none | `pending` |
| B0027 | rule | `legacy_custom` | abs: weak reverse triangle inequality | `src/verify/verify_builtin_rules/abs_order_builtin.rs:763` | abs order | none | `pending` |
| B0028 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/complex_builtin.rs:18` | complex | none | `pending` |
| B0029 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/complex_builtin.rs:25` | complex | none | `pending` |
| B0030 | rule | `legacy_custom` | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:37` | complex | none | `pending` |
| B0031 | rule | `legacy_custom` | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:47` | complex | none | `pending` |
| B0032 | rule | `legacy_custom` | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:66` | complex | none | `pending` |
| B0033 | rule | `legacy_custom` | complex modulus zero implies zero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:93` | complex | none | `pending` |
| B0034 | rule | `legacy_custom` | complex reconstruction from real and imaginary coordinates | `src/verify/verify_builtin_rules/complex_builtin.rs:110` | complex | none | `pending` |
| B0035 | rule | `legacy_custom` | complex reconstruction from real and imaginary coordinates | `src/verify/verify_builtin_rules/complex_builtin.rs:125` | complex | none | `pending` |
| B0036 | rule | `legacy_custom` | complex extensionality by re and img | `src/verify/verify_builtin_rules/complex_builtin.rs:158` | complex | none | `pending` |
| B0037 | rule | `legacy_custom` | native imaginary unit is nonzero | `src/verify/verify_builtin_rules/complex_builtin.rs:175` | complex | none | `pending` |
| B0038 | rule | `legacy_custom` | complex modulus is a nonnegative real | `src/verify/verify_builtin_rules/complex_builtin.rs:197` | complex | none | `pending` |
| B0039 | rule | `legacy_custom` | complex modulus triangle inequality | `src/verify/verify_builtin_rules/complex_builtin.rs:204` | complex | none | `pending` |
| B0040 | rule | `legacy_custom` | complex modulus reverse triangle inequality | `src/verify/verify_builtin_rules/complex_builtin.rs:211` | complex | none | `pending` |
| B0041 | rule | `legacy_custom` | complex modulus is positive for a nonzero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:230` | complex | none | `pending` |
| B0042 | rule | `legacy_custom` | complex modulus is nonzero for a nonzero argument | `src/verify/verify_builtin_rules/complex_builtin.rs:265` | complex | none | `pending` |
| B0043 | rule | `legacy_custom` | dynamic: &reason | `src/verify/verify_builtin_rules/complex_builtin.rs:531` | complex | none | `pending` |
| B0044 | rule | `reflection` | deterministic natural coprimality computation | `src/verify/verify_builtin_rules/coprime_builtin.rs:42` | coprime | none | `not_this_round` |
| B0045 | rule | `legacy_custom` | they are the same | `src/verify/verify_builtin_rules/equality_dispatch.rs:16` | equality dispatch | none | `pending` |
| B0046 | rule | `legacy_custom` | gcd divides each argument | `src/verify/verify_builtin_rules/equality_dispatch.rs:29` | equality dispatch | none | `pending` |
| B0047 | rule | `legacy_custom` | a product modulo either factor is zero | `src/verify/verify_builtin_rules/equality_dispatch.rs:42` | equality dispatch | none | `pending` |
| B0048 | rule | `reflection` | calculation and rational expression simplification | `src/verify/verify_builtin_rules/equality_dispatch.rs:312` | equality dispatch | none | `not_this_round` |
| B0049 | rule | `reflection` | calculation and rational expression simplification | `src/verify/verify_builtin_rules/equality_dispatch.rs:323` | equality dispatch | none | `not_this_round` |
| B0050 | rule | `legacy_custom` | tuple reconstruction from known Cartesian-product membership | `src/verify/verify_builtin_rules/equality_dispatch.rs:1104` | equality dispatch | none | `pending` |
| B0051 | rule | `legacy_custom` | union_commutative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1125` | equality dispatch | none | `pending` |
| B0052 | rule | `legacy_custom` | union_associative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1138` | equality dispatch | none | `pending` |
| B0053 | rule | `legacy_custom` | union_idempotent | `src/verify/verify_builtin_rules/equality_dispatch.rs:1150` | equality dispatch | none | `pending` |
| B0054 | rule | `legacy_custom` | union_empty_identity | `src/verify/verify_builtin_rules/equality_dispatch.rs:1164` | equality dispatch | none | `pending` |
| B0055 | rule | `legacy_custom` | intersect_commutative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1185` | equality dispatch | none | `pending` |
| B0056 | rule | `legacy_custom` | intersect_associative | `src/verify/verify_builtin_rules/equality_dispatch.rs:1199` | equality dispatch | none | `pending` |
| B0057 | rule | `legacy_custom` | intersect_union_distributive | `src/verify/verify_builtin_rules/equality_dispatch.rs:1213` | equality dispatch | none | `pending` |
| B0058 | rule | `legacy_custom` | set_minus_union_de_morgan | `src/verify/verify_builtin_rules/equality_dispatch.rs:1237` | equality dispatch | none | `pending` |
| B0059 | rule | `legacy_custom` | set_minus_intersect_de_morgan | `src/verify/verify_builtin_rules/equality_dispatch.rs:1251` | equality dispatch | none | `pending` |
| B0060 | rule | `legacy_custom` | set_minus_recovers_subset_from_relative_complement | `src/verify/verify_builtin_rules/equality_dispatch.rs:1270` | equality dispatch | none | `pending` |
| B0061 | rule | `legacy_custom` | cart_finite_set_size_product | `src/verify/verify_builtin_rules/equality_dispatch.rs:1294` | equality dispatch | none | `pending` |
| B0062 | rule | `legacy_custom` | finite_set_size_set_minus | `src/verify/verify_builtin_rules/equality_dispatch.rs:1334` | equality dispatch | none | `pending` |
| B0063 | rule | `legacy_custom` | finite_set_size_union_inclusion_exclusion | `src/verify/verify_builtin_rules/equality_dispatch.rs:1368` | equality dispatch | none | `pending` |
| B0064 | rule | `legacy_custom` | finite_set_size_partition_by_intersection_and_difference | `src/verify/verify_builtin_rules/equality_dispatch.rs:1402` | equality dispatch | none | `pending` |
| B0065 | rule | `legacy_custom` | finite_set_size_set_minus_finite_subset | `src/verify/verify_builtin_rules/equality_dispatch.rs:1448` | equality dispatch | none | `pending` |
| B0066 | rule | `legacy_custom` | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/equality_dispatch.rs:1500` | equality dispatch | none | `pending` |
| B0067 | rule | `legacy_custom` | power_set_finite_set_size_two_pow_finite_set_size_base | `src/verify/verify_builtin_rules/equality_dispatch.rs:1531` | equality dispatch | none | `pending` |
| B0068 | rule | `legacy_custom` | intersect_from_subset | `src/verify/verify_builtin_rules/equality_dispatch.rs:2038` | equality dispatch | none | `pending` |
| B0069 | rule | `reflection` | intersect_literal_set_filter | `src/verify/verify_builtin_rules/equality_dispatch.rs:2102` | equality dispatch | none | `not_this_round` |
| B0070 | rule | `legacy_custom` | equality: a = c - b from known a + b = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2152` | equality dispatch | none | `pending` |
| B0071 | rule | `legacy_custom` | equality: a = c - b from known b + a = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2171` | equality dispatch | none | `pending` |
| B0072 | rule | `legacy_custom` | tuple equality from dimension and projections | `src/verify/verify_builtin_rules/equality_dispatch.rs:2234` | equality dispatch | none | `pending` |
| B0073 | rule | `legacy_custom` | tuple equality from symbolic dimension and coordinates | `src/verify/verify_builtin_rules/equality_dispatch.rs:2342` | equality dispatch | none | `pending` |
| B0074 | rule | `legacy_custom` | cart equality from dimension and projections | `src/verify/verify_builtin_rules/equality_dispatch.rs:2417` | equality dispatch | none | `pending` |
| B0075 | rule | `legacy_custom` | integer interval emptiness by number comparison | `src/verify/verify_builtin_rules/equality_dispatch.rs:2523` | equality dispatch | none | `pending` |
| B0076 | rule | `legacy_custom` | empty_set_equality_from_not_nonempty | `src/verify/verify_builtin_rules/equality_dispatch.rs:2537` | equality dispatch | none | `pending` |
| B0077 | rule | `legacy_custom` | finite_set_size_zero_implies_empty_set | `src/verify/verify_builtin_rules/equality_dispatch.rs:2567` | equality dispatch | none | `pending` |
| B0078 | rule | `legacy_custom` | equality from a >= b and b >= a | `src/verify/verify_builtin_rules/equality_dispatch.rs:2638` | equality dispatch | none | `pending` |
| B0079 | rule | `legacy_custom` | division elimination: from a / b = c and b != 0, prove a = c * b | `src/verify/verify_builtin_rules/equality_dispatch.rs:2699` | equality dispatch | none | `pending` |
| B0080 | rule | `legacy_custom` | division introduction: from a = b * c and b != 0, prove a / b = c | `src/verify/verify_builtin_rules/equality_dispatch.rs:2775` | equality dispatch | none | `pending` |
| B0081 | rule | `legacy_custom` | dynamic: rule | `src/verify/verify_builtin_rules/equality_dispatch.rs:2882` | equality dispatch | none | `pending` |
| B0082 | rule | `definition` | dynamic: rule | `src/verify/verify_builtin_rules/equality_dispatch.rs:2931` | equality dispatch | none | `pending` |
| B0083 | rule | `transform` | dynamic: format!( "equality from registered antisymmetric prop '{}'", prop_name ) | `src/verify/verify_builtin_rules/equality_dispatch.rs:2980` | equality dispatch | none | `pending` |
| B0084 | rule | `definition` | matrix positive power base case: A '^ 1 = A | `src/verify/verify_builtin_rules/equality_function.rs:26` | equality function | none | `pending` |
| B0085 | rule | `definition` | matrix positive power recursion: A '^(k + 1) = (A '^ k) '* A | `src/verify/verify_builtin_rules/equality_function.rs:67` | equality function | none | `pending` |
| B0086 | rule | `local_schema` | abs: abs(x) = x from 0 <= x | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:84` | numeric equality | none | `pending` |
| B0087 | rule | `local_schema` | abs: abs(x) = -x from x <= 0 | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:130` | numeric equality | none | `pending` |
| B0088 | rule | `local_schema` | abs: abs(x * y) = abs(x) * abs(y) | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:164` | numeric equality | none | `pending` |
| B0089 | rule | `legacy_custom` | abs: x^n = abs(x)^n for even integer n | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:219` | numeric equality | none | `pending` |
| B0090 | rule | `legacy_custom` | abs: x = 0 from abs(x) = 0 | `src/verify/verify_builtin_rules/equality_numeric/absolute_value.rs:246` | numeric equality | none | `pending` |
| B0091 | rule | `legacy_custom` | equality: 0 = x - y with x = y (known or builtin) | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:53` | numeric equality | none | `pending` |
| B0092 | rule | `legacy_custom` | equality: b = 0 from a * b = 0 and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:143` | numeric equality | none | `pending` |
| B0093 | rule | `legacy_custom` | equality: a = 0 from a * b = 0 and b != 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:170` | numeric equality | none | `pending` |
| B0094 | rule | `reflection` | equality: 0 = a^n from a = 0, n positive integer literal | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:232` | numeric equality | none | `not_this_round` |
| B0095 | rule | `legacy_custom` | equality: 0 % m = 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:266` | numeric equality | none | `pending` |
| B0096 | rule | `legacy_custom` | equality: x % 1 = 0 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:299` | numeric equality | none | `pending` |
| B0097 | rule | `legacy_custom` | equality: 1 % k = 1 for k >= 2 | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:349` | numeric equality | none | `pending` |
| B0098 | rule | `legacy_custom` | equality: (a - a % b) % b = 0 for a in Z and b in N+ | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:413` | numeric equality | none | `pending` |
| B0099 | rule | `legacy_custom` | equality: Euclidean remainder uniqueness from a = m * q + r and 0 <= r < m | `src/verify/verify_builtin_rules/equality_numeric/elementary.rs:497` | numeric equality | none | `pending` |
| B0100 | rule | `legacy_custom` | equality: finite-set product over empty set is one | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:39` | numeric equality | none | `pending` |
| B0101 | rule | `legacy_custom` | equality: finite-set product over displayed set expands elementwise | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:90` | numeric equality | none | `pending` |
| B0102 | rule | `legacy_custom` | equality: finite-set product after inserting a fresh element | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:183` | numeric equality | none | `pending` |
| B0103 | rule | `legacy_custom` | equality: finite-set product after removing a member | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:275` | numeric equality | none | `pending` |
| B0104 | rule | `legacy_custom` | equality: finite-set product over closed integer range equals range product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:337` | numeric equality | none | `pending` |
| B0105 | rule | `legacy_custom` | equality: finite-set product of a constant factor | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:391` | numeric equality | none | `pending` |
| B0106 | rule | `quantified` | equality: finite-set products from known fn_eq_in | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:459` | numeric equality | none | `pending` |
| B0107 | rule | `quantified` | equality: finite-set products from pointwise equality on the finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:491` | numeric equality | none | `pending` |
| B0108 | rule | `legacy_custom` | equality: finite-set product distributes over pointwise multiplication | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:572` | numeric equality | none | `pending` |
| B0109 | rule | `legacy_custom` | equality: finite-set product substitution along a bijection | `src/verify/verify_builtin_rules/equality_numeric/finite_set_product.rs:645` | numeric equality | none | `pending` |
| B0110 | rule | `legacy_custom` | equality: finite-set sum over empty set is zero | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:40` | numeric equality | none | `pending` |
| B0111 | rule | `legacy_custom` | equality: finite-set sum over displayed set expands elementwise | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:101` | numeric equality | none | `pending` |
| B0112 | rule | `legacy_custom` | equality: finite-set sum over closed integer range equals range sum | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:194` | numeric equality | none | `pending` |
| B0113 | rule | `reflection` | equality: finite-set sum of the literal zero function is zero | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:238` | numeric equality | none | `not_this_round` |
| B0114 | rule | `legacy_custom` | equality: finite-set sum of a constant summand | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:265` | numeric equality | none | `pending` |
| B0115 | rule | `quantified` | equality: finite-set sums from pointwise equality on the finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:320` | numeric equality | none | `pending` |
| B0116 | rule | `legacy_custom` | equality: finite-set sum substitution along a uniquely-covered index set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:408` | numeric equality | none | `pending` |
| B0117 | rule | `legacy_custom` | equality: finite-set sum over a disjoint union | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:493` | numeric equality | none | `pending` |
| B0118 | rule | `legacy_custom` | equality: finite-set sum distributes over pointwise addition | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:574` | numeric equality | none | `pending` |
| B0119 | rule | `legacy_custom` | equality: finite-set sum scalar multiplication | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:642` | numeric equality | none | `pending` |
| B0120 | rule | `legacy_custom` | equality: double finite-set sum over Cartesian product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:694` | numeric equality | none | `pending` |
| B0121 | rule | `legacy_custom` | equality: finite-set Fubini over Cartesian product | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:742` | numeric equality | none | `pending` |
| B0122 | rule | `legacy_custom` | equality: sums over bijective enumerations of the same finite set | `src/verify/verify_builtin_rules/equality_numeric/finite_set_sum.rs:856` | numeric equality | none | `pending` |
| B0123 | rule | `reflection` | equality: a finite range sum of the literal zero function is zero | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:45` | numeric equality | none | `not_this_round` |
| B0124 | rule | `quantified` | equality: finite sums are congruent from pointwise equality on the shared integer range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:164` | numeric equality | none | `pending` |
| B0125 | rule | `legacy_custom` | equality: sum additivity from pointwise equality on the integer index range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:245` | numeric equality | none | `pending` |
| B0126 | rule | `legacy_custom` | equality: finite sum subtraction over a common additive carrier | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:355` | numeric equality | none | `pending` |
| B0127 | rule | `legacy_custom` | equality: merge adjacent sum ranges with the same summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:522` | numeric equality | none | `pending` |
| B0128 | rule | `legacy_custom` | equality: single-term sum equals the summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:568` | numeric equality | none | `pending` |
| B0129 | rule | `legacy_custom` | equality: single-term product equals the factor | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:619` | numeric equality | none | `pending` |
| B0130 | rule | `legacy_custom` | equality: sum through e equals sum through e-1 plus last summand f(e) | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:705` | numeric equality | none | `pending` |
| B0131 | rule | `legacy_custom` | equality: product through e equals product through e-1 times last factor f(e) | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:791` | numeric equality | none | `pending` |
| B0132 | rule | `legacy_custom` | equality: sum partitions closed range into adjacent sub-sums with the same summand | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:916` | numeric equality | none | `pending` |
| B0133 | rule | `legacy_custom` | equality: product partitions closed range into adjacent sub-products with the same factor | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1018` | numeric equality | none | `pending` |
| B0134 | rule | `legacy_custom` | equality: sum reindexing (integer shift) from pointwise equality on the range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1103` | numeric equality | none | `pending` |
| B0135 | rule | `legacy_custom` | equality: sum of a constant summand over a closed integer range | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1168` | numeric equality | none | `pending` |
| B0136 | rule | `legacy_custom` | equality: finite sum scalar multiplication | `src/verify/verify_builtin_rules/equality_numeric/iterated_ranges.rs:1251` | numeric equality | none | `pending` |
| B0137 | rule | `legacy_custom` | equality: log(a, a^b) = b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:43` | numeric equality | none | `pending` |
| B0138 | rule | `legacy_custom` | equality: log(a^b, c) = log(a, c) / b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:83` | numeric equality | none | `pending` |
| B0139 | rule | `legacy_custom` | equality: log(a, x^b) = b * log(a, x) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:122` | numeric equality | none | `pending` |
| B0140 | rule | `legacy_custom` | equality: log(a, x*y) = log(a, x) + log(a, y) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:163` | numeric equality | none | `pending` |
| B0141 | rule | `legacy_custom` | equality: log(a, x/y) = log(a, x) - log(a, y) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:202` | numeric equality | none | `pending` |
| B0142 | rule | `legacy_custom` | equality: log(a, 1/x) = -log(a, x) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:295` | numeric equality | none | `pending` |
| B0143 | rule | `legacy_custom` | equality: log(a, b) = log(c, b) / log(c, a) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:370` | numeric equality | none | `pending` |
| B0144 | rule | `legacy_custom` | equality: log(a, a) = 1 | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:409` | numeric equality | none | `pending` |
| B0145 | rule | `legacy_custom` | equality: log(a, 1) = 0 | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:421` | numeric equality | none | `pending` |
| B0146 | rule | `legacy_custom` | equality: log(a, b) = c from a^c = b | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:437` | numeric equality | none | `pending` |
| B0147 | rule | `legacy_custom` | equality: a^c = b from c = log(a, b) | `src/verify/verify_builtin_rules/equality_numeric/logarithms.rs:473` | numeric equality | none | `pending` |
| B0148 | rule | `legacy_custom` | equality: nested mod with same modulus absorbs inner mod | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:58` | numeric equality | none | `pending` |
| B0149 | rule | `legacy_custom` | equality: nested mod absorbs an inner modulus divisible by the outer modulus | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:148` | numeric equality | none | `pending` |
| B0150 | rule | `legacy_custom` | equality: mod — peel outer nested % m to reuse known residue equality | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:211` | numeric equality | none | `pending` |
| B0151 | rule | `legacy_custom` | equality: mod — peel outer nested % m to reuse known residue equality | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:242` | numeric equality | none | `pending` |
| B0152 | rule | `legacy_custom` | equality: integer congruence — reduce matching + / - / * operands modulo m | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:305` | numeric equality | none | `pending` |
| B0153 | rule | `legacy_custom` | equality: integer congruence — same modulus, residues for matching + / - / * | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:348` | numeric equality | none | `pending` |
| B0154 | rule | `legacy_custom` | equality: (-n) % k = (k - n % k) % k for n in Z and k in N+ | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:435` | numeric equality | none | `pending` |
| B0155 | rule | `legacy_custom` | equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N+ | `src/verify/verify_builtin_rules/equality_numeric/modulo.rs:553` | numeric equality | none | `pending` |
| B0156 | rule | `legacy_custom` | equality: (-1)^(2*m+1) = -1 for m in N | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:90` | numeric equality | none | `pending` |
| B0157 | rule | `legacy_custom` | equality: a^1 = a | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:127` | numeric equality | none | `pending` |
| B0158 | rule | `legacy_custom` | equality: a^0 = 1 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:160` | numeric equality | none | `pending` |
| B0159 | rule | `legacy_custom` | equality: 1^x = 1 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:193` | numeric equality | none | `pending` |
| B0160 | rule | `legacy_custom` | equality: 0^x = 0 for x > 0 | `src/verify/verify_builtin_rules/equality_numeric/power_identities.rs:267` | numeric equality | none | `pending` |
| B0161 | rule | `legacy_custom` | equality: a = 0 from a^n = 0 and n in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:53` | numeric equality | none | `pending` |
| B0162 | rule | `legacy_custom` | equality: positive bases equal from equal nonzero integer powers | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:156` | numeric equality | none | `pending` |
| B0163 | rule | `legacy_custom` | equality: abs(a^n) = abs(a)^n for n in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:227` | numeric equality | none | `pending` |
| B0164 | rule | `legacy_custom` | equality: abs(a^n) = abs(a)^n for n in N over real bases | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:244` | numeric equality | none | `pending` |
| B0165 | rule | `legacy_custom` | equality: abs(a^n) = abs(a)^n for n in Z and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:268` | numeric equality | none | `pending` |
| B0166 | rule | `legacy_custom` | equality: a^(-n) = 1 / a^n for n in N+ and a != 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:405` | numeric equality | none | `pending` |
| B0167 | rule | `legacy_custom` | number in N+ | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:454` | numeric equality | none | `pending` |
| B0168 | rule | `legacy_custom` | equality: x^(1/n) = z from x = z^n, n in N+, and z >= 0 | `src/verify/verify_builtin_rules/equality_numeric/power_inverses.rs:488` | numeric equality | none | `pending` |
| B0169 | rule | `legacy_custom` | equality: a^(m+n) = a^m * a^n for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:387` | numeric equality | none | `pending` |
| B0170 | rule | `legacy_custom` | equality: (a^m)^n = a^(m*n) for real exponents over positive real bases, natural exponents over complex bases, positive integer exponents, or integer exponents with nonzero base | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:613` | numeric equality | none | `pending` |
| B0171 | rule | `legacy_custom` | equality: (a*b)^x = a^x * b^x for real x over positive real factors, n in N over complex bases, n in N+, or n in Z with nonzero bases | `src/verify/verify_builtin_rules/equality_numeric/power_rules.rs:791` | numeric equality | none | `pending` |
| B0172 | rule | `legacy_custom` | equality: reduce over an empty closed interval returns its seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:39` | numeric equality | none | `pending` |
| B0173 | rule | `reflection` | equality: literal reduce expands as an ascending left fold | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:105` | numeric equality | none | `not_this_round` |
| B0174 | rule | `legacy_custom` | equality: nonempty reduce satisfies its last-step equation | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:187` | numeric equality | none | `pending` |
| B0175 | rule | `legacy_custom` | equality: finite_set_reduce over the empty set returns its seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:230` | numeric equality | none | `pending` |
| B0176 | rule | `legacy_custom` | equality: finite_set_reduce expands through a finite-set enumeration | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:301` | numeric equality | none | `pending` |
| B0177 | rule | `legacy_custom` | equality: finite_set_reduce over a closed range uses its ascending enumeration | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:344` | numeric equality | none | `pending` |
| B0178 | rule | `legacy_custom` | equality: finite_set_reduce after inserting a fresh element | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:421` | numeric equality | none | `pending` |
| B0179 | rule | `legacy_custom` | equality: additive reduce with seed zero equals range sum | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:461` | numeric equality | none | `pending` |
| B0180 | rule | `legacy_custom` | equality: multiplicative reduce with seed one equals range product | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:482` | numeric equality | none | `pending` |
| B0181 | rule | `legacy_custom` | equality: additive finite_set_reduce with seed zero equals finite_set_sum | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:523` | numeric equality | none | `pending` |
| B0182 | rule | `legacy_custom` | equality: multiplicative finite_set_reduce with seed one equals finite_set_product | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:543` | numeric equality | none | `pending` |
| B0183 | rule | `quantified` | equality: reduce congruence from pointwise equality on the closed range | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:603` | numeric equality | none | `pending` |
| B0184 | rule | `quantified` | equality: finite_set_reduce congruence from fn_eq_in on the finite set | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:640` | numeric equality | none | `pending` |
| B0185 | rule | `legacy_custom` | equality: reduce substitution translates equally long empty intervals | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:732` | numeric equality | none | `pending` |
| B0186 | rule | `legacy_custom` | equality: reduce substitution by an order-preserving interval translation | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:789` | numeric equality | none | `pending` |
| B0187 | rule | `legacy_custom` | equality: nonempty reduce consumes its first value into the seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:882` | numeric equality | none | `pending` |
| B0188 | rule | `legacy_custom` | equality: reduce partitions into adjacent ordered ranges | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:962` | numeric equality | none | `pending` |
| B0189 | rule | `legacy_custom` | equality: finite_set_reduce over a disjoint union preserves the single seed | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:1062` | numeric equality | none | `pending` |
| B0190 | rule | `legacy_custom` | equality: finite_set_reduce substitution along a bijection | `src/verify/verify_builtin_rules/equality_numeric/reduce.rs:1169` | numeric equality | none | `pending` |
| B0191 | rule | `legacy_custom` | sqrt: (sqrt(x))^2 = x | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:34` | numeric equality | none | `pending` |
| B0192 | rule | `legacy_custom` | sqrt: sqrt(0) = 0 and sqrt(1) = 1 | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:80` | numeric equality | none | `pending` |
| B0193 | rule | `legacy_custom` | sqrt: sqrt(a^2) = a for a >= 0 | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:130` | numeric equality | none | `pending` |
| B0194 | rule | `legacy_custom` | sqrt: sqrt(a * b) = sqrt(a) * sqrt(b) | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:200` | numeric equality | none | `pending` |
| B0195 | rule | `legacy_custom` | sqrt: sqrt(a / b) = sqrt(a) / sqrt(b) | `src/verify/verify_builtin_rules/equality_numeric/square_root.rs:274` | numeric equality | none | `pending` |
| B0196 | rule | `legacy_custom` | equality: a^2 + b^2 = 0 from a = 0 and b = 0 over R | `src/verify/verify_builtin_rules/equality_numeric/square_sums.rs:44` | numeric equality | none | `pending` |
| B0197 | rule | `legacy_custom` | equality: a = 0 from a^2 + b^2 = 0 over R | `src/verify/verify_builtin_rules/equality_numeric/square_sums.rs:124` | numeric equality | none | `pending` |
| B0198 | rule | `legacy_custom` | known-only equality: they are the same | `src/verify/verify_builtin_rules/equality_structural.rs:42` | equality structural | none | `pending` |
| B0199 | rule | `legacy_custom` | known-only equality: same known equality class | `src/verify/verify_builtin_rules/equality_structural.rs:51` | equality structural | none | `pending` |
| B0200 | rule | `reflection` | calculation | `src/verify/verify_builtin_rules/equality_structural.rs:65` | equality structural | none | `not_this_round` |
| B0201 | rule | `legacy_custom` | known-only equality: resolved objects match | `src/verify/verify_builtin_rules/equality_structural.rs:76` | equality structural | none | `pending` |
| B0202 | rule | `legacy_custom` | they are the same | `src/verify/verify_builtin_rules/equality_structural.rs:513` | equality structural | none | `pending` |
| B0203 | rule | `reflection` | calculation | `src/verify/verify_builtin_rules/equality_structural.rs:529` | equality structural | none | `not_this_round` |
| B0204 | rule | `legacy_custom` | tuple in cart: each component is in the corresponding cart factor | `src/verify/verify_builtin_rules/in_fact_builtin/cart_membership.rs:37` | membership | none | `pending` |
| B0205 | rule | `legacy_custom` | cart membership from symbolic dimension and projections | `src/verify/verify_builtin_rules/in_fact_builtin/cart_membership.rs:108` | membership | none | `pending` |
| B0206 | rule | `legacy_custom` | set-minus membership excludes the right operand | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:85` | membership | none | `pending` |
| B0207 | rule | `legacy_custom` | native imaginary unit is in C | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:206` | membership | none | `pending` |
| B0208 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:231` | membership | none | `pending` |
| B0209 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:249` | membership | none | `pending` |
| B0210 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:267` | membership | none | `pending` |
| B0211 | rule | `legacy_custom` | N: a^k from a in N and k in N | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:359` | membership | none | `pending` |
| B0212 | rule | `legacy_custom` | absolute value of a known nonzero integer is a positive natural | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:430` | membership | none | `pending` |
| B0213 | rule | `legacy_custom` | N+: a^k from a in N+ and k in N | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:452` | membership | none | `pending` |
| B0214 | rule | `legacy_custom` | gcd of a non-all-zero integer pair is a positive integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:472` | membership | none | `pending` |
| B0215 | rule | `legacy_custom` | lcm of two integers is a nonnegative integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:489` | membership | none | `pending` |
| B0216 | rule | `legacy_custom` | floor and ceil return integers | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:500` | membership | none | `pending` |
| B0217 | rule | `legacy_custom` | minimum and maximum of real arguments are real | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:508` | membership | none | `pending` |
| B0218 | rule | `legacy_custom` | real exponential values are positive reals | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:519` | membership | none | `pending` |
| B0219 | rule | `legacy_custom` | natural logarithm of a positive real is real | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:527` | membership | none | `pending` |
| B0220 | rule | `legacy_custom` | the real sign function returns an integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:538` | membership | none | `pending` |
| B0221 | rule | `legacy_custom` | factorial of a natural number is a positive integer | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:558` | membership | none | `pending` |
| B0222 | rule | `legacy_custom` | Q+: 0 < x and x in Q | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:578` | membership | none | `pending` |
| B0223 | rule | `legacy_custom` | R+: 0 < x and x in R | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:585` | membership | none | `pending` |
| B0224 | rule | `legacy_custom` | finite_seq list: length equals n and each entry in co-domain | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:837` | membership | none | `pending` |
| B0225 | rule | `reflection` | matrix literal: shape matches matrix(...) and each entry in co-domain | `src/verify/verify_builtin_rules/in_fact_builtin/dispatch.rs:878` | membership | none | `not_this_round` |
| B0226 | rule | `legacy_custom` | dynamic: format!( "{name}: operation carrier {carrier} is contained in {}", in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:27` | membership | none | `pending` |
| B0227 | rule | `legacy_custom` | refined integer carrier from known integer membership and strict sign | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:80` | membership | none | `pending` |
| B0228 | rule | `legacy_custom` | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:111` | membership | none | `pending` |
| B0229 | rule | `legacy_custom` | finite_set_sum: positive summand over a nonempty finite set | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:165` | membership | none | `pending` |
| B0230 | rule | `legacy_custom` | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:177` | membership | none | `pending` |
| B0231 | rule | `legacy_custom` | finite_set_product: positive factors give a positive finite product | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:202` | membership | none | `pending` |
| B0232 | rule | `legacy_custom` | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:214` | membership | none | `pending` |
| B0233 | rule | `legacy_custom` | dynamic: reason.as_str() | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:238` | membership | none | `pending` |
| B0234 | rule | `local_schema` | fn application in its exact instantiated declared return set | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:321` | membership | none | `pending` |
| B0235 | rule | `legacy_custom` | fn application in declared return set or standard numeric superset (well-defined under typing) | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:337` | membership | none | `pending` |
| B0236 | rule | `legacy_custom` | N: a + b from a in N and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:375` | membership | none | `pending` |
| B0237 | rule | `legacy_custom` | N: n - 1 from n in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:412` | membership | none | `pending` |
| B0238 | rule | `legacy_custom` | N: n - 1 from n in N and n > 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:429` | membership | none | `pending` |
| B0239 | rule | `legacy_custom` | N: a - b from a,b in Z and b <= a | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:462` | membership | none | `pending` |
| B0240 | rule | `legacy_custom` | N: a - b from a,b in Z and known nonnegative difference | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:484` | membership | none | `pending` |
| B0241 | rule | `legacy_custom` | N: a * b from a in N and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:526` | membership | none | `pending` |
| B0242 | rule | `legacy_custom` | R+: a^x from 0 < a and x in R | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:606` | membership | none | `pending` |
| B0243 | rule | `legacy_custom` | N+: n - 1 from n in N+ and n > 1 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:653` | membership | none | `pending` |
| B0244 | rule | `legacy_custom` | N+: a + b from a in N+ and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:692` | membership | none | `pending` |
| B0245 | rule | `legacy_custom` | N+: a + b from a in N+ and b in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:709` | membership | none | `pending` |
| B0246 | rule | `legacy_custom` | N+: a + b from a in N and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:732` | membership | none | `pending` |
| B0247 | rule | `legacy_custom` | N+: a * b from a in N+ and b in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:770` | membership | none | `pending` |
| B0248 | rule | `legacy_custom` | N+: x in N and x != 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:797` | membership | none | `pending` |
| B0249 | rule | `legacy_custom` | N+: 0 < x and x in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:817` | membership | none | `pending` |
| B0250 | rule | `legacy_custom` | N+: 0 < x and x in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:828` | membership | none | `pending` |
| B0251 | rule | `legacy_custom` | N: x in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:888` | membership | none | `pending` |
| B0252 | rule | `legacy_custom` | N: x in Z and x >= 0 or x > 0 | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:913` | membership | none | `pending` |
| B0253 | rule | `legacy_custom` | in closed_range: a <= i and i <= b | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:953` | membership | none | `pending` |
| B0254 | rule | `legacy_custom` | in range: a <= i and i < b | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:985` | membership | none | `pending` |
| B0255 | rule | `legacy_custom` | in real interval: x in R and endpoint bounds | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1035` | membership | none | `pending` |
| B0256 | rule | `legacy_custom` | in half-infinite real interval: x in R and endpoint bound | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1084` | membership | none | `pending` |
| B0257 | rule | `legacy_custom` | complex scalar arithmetic is closed in C | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1254` | membership | none | `pending` |
| B0258 | rule | `local_schema` | real arithmetic has real operands and result | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1318` | membership | `Litex.BuiltinRules.realAddClosure/realSubClosure/realMulClosure/realDivClosure`; power and other operators remain unsupported | `partial` |
| B0259 | rule | `legacy_custom` | real arithmetic has real operands and result | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1326` | membership | none | `pending` |
| B0260 | rule | `local_schema` | integer expression closure under +, -, and * | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1409` | membership | none | `pending` |
| B0261 | rule | `legacy_custom` | finite_set_size of a known finite set is a natural number | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1433` | membership | none | `pending` |
| B0262 | rule | `legacy_custom` | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1460` | membership | none | `pending` |
| B0263 | rule | `legacy_custom` | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1530` | membership | none | `pending` |
| B0264 | rule | `local_schema` | Z closure: binary integer arithmetic | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1707` | membership | none | `pending` |
| B0265 | rule | `legacy_custom` | Z closure: arithmetic operands in Z; pow base in Z and exponent in N, or base in N+ and exponent in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1718` | membership | none | `pending` |
| B0266 | rule | `legacy_custom` | Q closure: +-*/ operands in Q; pow base in Q and exponent in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1776` | membership | none | `pending` |
| B0267 | rule | `legacy_custom` | negation maps a positive scalar into the matching negative carrier | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1828` | membership | none | `pending` |
| B0268 | rule | `legacy_custom` | mul_opposite_signs_product_in_negative_reals | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1863` | membership | none | `pending` |
| B0269 | rule | `legacy_custom` | mul_opposite_signs_product_in_negative_rationals | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1882` | membership | none | `pending` |
| B0270 | rule | `legacy_custom` | mul_opposite_signs_product_in_negative_integers | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_membership.rs:1905` | membership | none | `pending` |
| B0271 | rule | `reflection` | number in C | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:49` | membership | `Litex.BuiltinRules.numeralInC` for natural numeral targets only | `partial` |
| B0272 | rule | `reflection` | number in C* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:52` | membership | none | `not_this_round` |
| B0273 | rule | `reflection` | number in R | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:57` | membership | `Litex.BuiltinRules.numeralInR` for natural numeral targets only | `partial` |
| B0274 | rule | `reflection` | number in R+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:60` | membership | none | `not_this_round` |
| B0275 | rule | `reflection` | number in R- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:67` | membership | none | `not_this_round` |
| B0276 | rule | `reflection` | number in R* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:74` | membership | none | `not_this_round` |
| B0277 | rule | `reflection` | number in Q | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:79` | membership | `Litex.BuiltinRules.numeralInQ` for natural numeral targets only | `partial` |
| B0278 | rule | `reflection` | number in Q+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:82` | membership | none | `not_this_round` |
| B0279 | rule | `reflection` | number in Q- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:89` | membership | none | `not_this_round` |
| B0280 | rule | `reflection` | number in Q* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:96` | membership | none | `not_this_round` |
| B0281 | rule | `reflection` | number in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:103` | membership | `Litex.BuiltinRules.numeralInZ` for natural numeral targets only | `partial` |
| B0282 | rule | `reflection` | number in Z- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:110` | membership | none | `not_this_round` |
| B0283 | rule | `reflection` | number in Z* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:117` | membership | none | `not_this_round` |
| B0284 | rule | `reflection` | number in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:124` | membership | `Litex.BuiltinRules.numeralInN` for natural numeral targets only | `partial` |
| B0285 | rule | `reflection` | number in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:131` | membership | none | `not_this_round` |
| B0286 | rule | `reflection` | number not in C* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:148` | membership | none | `not_this_round` |
| B0287 | rule | `reflection` | number not in R+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:155` | membership | none | `not_this_round` |
| B0288 | rule | `reflection` | number not in R- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:162` | membership | none | `not_this_round` |
| B0289 | rule | `reflection` | number not in R* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:169` | membership | none | `not_this_round` |
| B0290 | rule | `reflection` | number not in Q+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:176` | membership | none | `not_this_round` |
| B0291 | rule | `reflection` | number not in Q- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:183` | membership | none | `not_this_round` |
| B0292 | rule | `reflection` | number not in Q* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:190` | membership | none | `not_this_round` |
| B0293 | rule | `reflection` | number not in Z | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:197` | membership | none | `not_this_round` |
| B0294 | rule | `reflection` | number not in Z- | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:204` | membership | none | `not_this_round` |
| B0295 | rule | `reflection` | number not in Z* | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:211` | membership | none | `not_this_round` |
| B0296 | rule | `reflection` | number not in N | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:218` | membership | none | `not_this_round` |
| B0297 | rule | `reflection` | number not in N+ | `src/verify/verify_builtin_rules/in_fact_builtin/numeric_values.rs:225` | membership | none | `not_this_round` |
| B0298 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/in_fact_builtin/operator_signature.rs:95` | membership | none | `pending` |
| B0299 | rule | `definition` | set-builder membership transport through one unfolded definition | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:66` | membership | none | `pending` |
| B0300 | rule | `definition` | set-builder membership transport from a known universal named-set membership | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:163` | membership | none | `pending` |
| B0301 | rule | `legacy_custom` | universal set-builder membership eliminates to its defining fact | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:265` | membership | none | `pending` |
| B0302 | rule | `legacy_custom` | set-builder membership eliminates to its instantiated defining fact | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:344` | membership | none | `pending` |
| B0303 | rule | `local_schema` | dynamic: format!("union membership: member of the {side_name} side") | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:378` | membership | none | `pending` |
| B0304 | rule | `local_schema` | intersection membership: member of both sides | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:429` | membership | none | `pending` |
| B0305 | rule | `local_schema` | dynamic: format!("intersection non-membership: non-member of the {side_name} side") | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:461` | membership | none | `pending` |
| B0306 | rule | `local_schema` | set-minus membership: member of left side and non-member of right side | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:512` | membership | none | `pending` |
| B0307 | rule | `legacy_custom` | big_union membership: an element of a member set is in the family union | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:537` | membership | none | `pending` |
| B0308 | rule | `legacy_custom` | big_union membership: an element of a member set is in the family union | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:572` | membership | none | `pending` |
| B0309 | rule | `quantified` | replacement membership: a relation witness is in the replacement set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:625` | membership | none | `pending` |
| B0310 | rule | `quantified` | replacement membership: a relation witness is in the replacement set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:658` | membership | none | `pending` |
| B0311 | rule | `legacy_custom` | fn_range membership: a well-defined function application is in the function range | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:845` | membership | none | `pending` |
| B0312 | rule | `legacy_custom` | structural subset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:884` | membership | none | `pending` |
| B0313 | rule | `legacy_custom` | fn_range power_set membership: function range is contained in the codomain | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:896` | membership | none | `pending` |
| B0314 | rule | `legacy_custom` | structural subset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:931` | membership | none | `pending` |
| B0315 | rule | `legacy_custom` | power_set membership: a subset of the base set is an element of the power set | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:943` | membership | none | `pending` |
| B0316 | rule | `legacy_custom` | general_cart membership: function into big_union(family) with pointwise factor membership | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:988` | membership | none | `pending` |
| B0317 | rule | `legacy_custom` | set builder membership: element is in the base set and satisfies all defining facts | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1055` | membership | none | `pending` |
| B0318 | rule | `legacy_custom` | membership in a set-valued definition: unfold one function or template definition to a set builder | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1116` | membership | none | `pending` |
| B0319 | rule | `reflection` | dependent struct constructor: each literal tuple field has its instantiated carrier | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1162` | membership | none | `not_this_round` |
| B0320 | rule | `legacy_custom` | struct membership: element is in the named structure carrier and satisfies struct equivalent facts | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1217` | membership | none | `pending` |
| B0321 | rule | `legacy_custom` | finite_set_size of a finite set is a natural number | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1238` | membership | none | `pending` |
| B0322 | rule | `legacy_custom` | dynamic: rule_name.to_string() | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1269` | membership | none | `pending` |
| B0323 | rule | `legacy_custom` | finite-set extremum: member of a standard numeric superset | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1297` | membership | none | `pending` |
| B0324 | rule | `legacy_custom` | membership through a known direct set inclusion | `src/verify/verify_builtin_rules/in_fact_builtin/set_membership.rs:1474` | membership | none | `pending` |
| B0325 | rule | `reflection` | selected literal tuple component has a real carrier | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:52` | membership | none | `not_this_round` |
| B0326 | rule | `reflection` | literal tuple projection inherits the selected component carrier | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:65` | membership | none | `not_this_round` |
| B0327 | rule | `legacy_custom` | standard_set_subset | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:92` | membership | none | `pending` |
| B0328 | rule | `legacy_custom` | subset reflexivity | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:100` | membership | none | `pending` |
| B0329 | rule | `legacy_custom` | set_builder in power_set: param_set subset of base implies builder defines a subset of base | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:116` | membership | none | `pending` |
| B0330 | rule | `legacy_custom` | list_set in power_set: each element is in the base set | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:151` | membership | none | `pending` |
| B0331 | rule | `legacy_custom` | dynamic: format!( "{} equals one element in list_set {}", in_fact.element, in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:177` | membership | none | `pending` |
| B0332 | rule | `legacy_custom` | dynamic: format!( "{} is not equal to every element in list_set {}", not_in_fact.element, not_in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:216` | membership | none | `pending` |
| B0333 | rule | `definition` | fn membership: stored fn signature matches RHS | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:240` | membership | none | `pending` |
| B0334 | rule | `definition` | fn membership: stored fn signature matches RHS (alpha-renamed parameters) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:262` | membership | none | `pending` |
| B0335 | rule | `legacy_custom` | anonymous function: signature (params, dom, co-domain) matches 'fn' set | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:301` | membership | none | `pending` |
| B0336 | rule | `legacy_custom` | anonymous function: signature matches 'fn' set (alpha-renamed parameters) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:324` | membership | none | `pending` |
| B0337 | rule | `legacy_custom` | anonymous function: signature matches 'fn' set through propositionally equal parameter sets | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:344` | membership | none | `pending` |
| B0338 | rule | `reflection` | dynamic: format!( "finite sequence literal application is in {}", target_set_obj ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:415` | membership | none | `not_this_round` |
| B0339 | rule | `legacy_custom` | dynamic: format!( "cart projection list_set elements are all in {}", target_set_obj ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:475` | membership | none | `pending` |
| B0340 | rule | `transform` | dynamic: format!( "{} in {} implies in {} (standard subset relation)", in_fact.element, source_set_obj, in_fact.set ) | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:512` | membership | none | `pending` |
| B0341 | rule | `legacy_custom` | listed-set member inherits a carrier shared by every listed element | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:583` | membership | none | `pending` |
| B0342 | rule | `legacy_custom` | numeric division not in Z: resolved numerator % denominator != 0 | `src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs:614` | membership | none | `pending` |
| B0343 | rule | `legacy_custom` | finite codomain of a surjection from a finite set | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:38` | mapping properties | none | `pending` |
| B0344 | rule | `legacy_custom` | finite injection has range cardinality equal to its source | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:93` | mapping properties | none | `pending` |
| B0345 | rule | `legacy_custom` | finite bijection preserves cardinality | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:164` | mapping properties | none | `pending` |
| B0346 | rule | `legacy_custom` | finite surjection bounds codomain cardinality by source cardinality | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:215` | mapping properties | none | `pending` |
| B0347 | rule | `reflection` | literal/range finite-set structure | `src/verify/verify_builtin_rules/mapping_properties_builtin.rs:279` | mapping properties | none | `not_this_round` |
| B0348 | rule | `legacy_custom` | native exp/ln inverse or canonical-base identity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:16` | native exp sign factorial | none | `pending` |
| B0349 | rule | `legacy_custom` | injectivity of native exp | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:41` | native exp sign factorial | none | `pending` |
| B0350 | rule | `legacy_custom` | injectivity of native ln | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:68` | native exp sign factorial | none | `pending` |
| B0351 | rule | `legacy_custom` | sign is zero only at zero | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:99` | native exp sign factorial | none | `pending` |
| B0352 | rule | `legacy_custom` | sign is nonzero exactly for nonzero arguments | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:142` | native exp sign factorial | none | `pending` |
| B0353 | rule | `legacy_custom` | native exp/ln algebra identity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:161` | native exp sign factorial | none | `pending` |
| B0354 | rule | `legacy_custom` | sign value selected from the argument order at zero | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:199` | native exp sign factorial | none | `pending` |
| B0355 | rule | `legacy_custom` | sign times absolute value restores the argument | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:217` | native exp sign factorial | none | `pending` |
| B0356 | rule | `legacy_custom` | native sign oddness or multiplicativity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:240` | native exp sign factorial | none | `pending` |
| B0357 | rule | `legacy_custom` | factorial successor recurrence | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:258` | native exp sign factorial | none | `pending` |
| B0358 | rule | `legacy_custom` | earlier factorial divides later factorial | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:300` | native exp sign factorial | none | `pending` |
| B0359 | rule | `legacy_custom` | native exp/sign/factorial characteristic order bound | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:340` | native exp sign factorial | none | `pending` |
| B0360 | rule | `legacy_custom` | native factorial monotonicity | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:405` | native exp sign factorial | none | `pending` |
| B0361 | rule | `legacy_custom` | native sign preserves weak order | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:439` | native exp sign factorial | none | `pending` |
| B0362 | rule | `legacy_custom` | dynamic: format!("native exp/ln reflects {order_kind} order") | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:587` | native exp sign factorial | none | `pending` |
| B0363 | rule | `legacy_custom` | dynamic: format!("native {function_name} preserves {order_kind} order") | `src/verify/verify_builtin_rules/native_exp_sign_factorial.rs:629` | native exp sign factorial | none | `pending` |
| B0364 | rule | `legacy_custom` | dynamic: format!("{name} fixes integer inputs") | `src/verify/verify_builtin_rules/native_integer_extrema.rs:34` | native integer extrema | none | `pending` |
| B0365 | rule | `legacy_custom` | native floor/ceil negation duality | `src/verify/verify_builtin_rules/native_integer_extrema.rs:55` | native integer extrema | none | `pending` |
| B0366 | rule | `legacy_custom` | native floor/ceil integer translation | `src/verify/verify_builtin_rules/native_integer_extrema.rs:76` | native integer extrema | none | `pending` |
| B0367 | rule | `legacy_custom` | dynamic: format!("{name} selects the ordered argument: {premise_left} <= {premise_right}") | `src/verify/verify_builtin_rules/native_integer_extrema.rs:125` | native integer extrema | none | `pending` |
| B0368 | rule | `legacy_custom` | native rounding/extremum characteristic order bound | `src/verify/verify_builtin_rules/native_integer_extrema.rs:166` | native integer extrema | none | `pending` |
| B0369 | rule | `legacy_custom` | native lcm is bounded by every positive common multiple | `src/verify/verify_builtin_rules/native_integer_extrema.rs:220` | native integer extrema | none | `pending` |
| B0370 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/native_integer_extrema.rs:306` | native integer extrema | none | `pending` |
| B0371 | rule | `legacy_custom` | native min/max lattice identity | `src/verify/verify_builtin_rules/native_integer_extrema.rs:328` | native integer extrema | none | `pending` |
| B0372 | rule | `legacy_custom` | lcm times gcd is the absolute product | `src/verify/verify_builtin_rules/native_integer_extrema.rs:350` | native integer extrema | none | `pending` |
| B0373 | rule | `legacy_custom` | native lcm symmetry, zero law, or divisibility | `src/verify/verify_builtin_rules/native_integer_extrema.rs:372` | native integer extrema | none | `pending` |
| B0374 | rule | `legacy_custom` | Every object is a set. | `src/verify/verify_builtin_rules/non_equational_dispatch.rs:52` | non equational dispatch | none | `pending` |
| B0375 | rule | `local_schema` | not-equality symmetry | `src/verify/verify_builtin_rules/not_equal_builtin.rs:50` | not equal | `Litex.BuiltinRules.notEqualSymmetry` | `implemented` |
| B0376 | rule | `legacy_custom` | list_set_different_length | `src/verify/verify_builtin_rules/not_equal_builtin.rs:63` | not equal | none | `pending` |
| B0377 | rule | `legacy_custom` | native real constant distinctness | `src/verify/verify_builtin_rules/not_equal_builtin.rs:207` | not equal | none | `pending` |
| B0378 | rule | `legacy_custom` | well-defined exp/factorial values are strictly positive | `src/verify/verify_builtin_rules/not_equal_builtin.rs:230` | not equal | none | `pending` |
| B0379 | rule | `reflection` | not_equal_numeric_resolved_or_equal_class_calculation | `src/verify/verify_builtin_rules/not_equal_builtin.rs:252` | not equal | none | `not_this_round` |
| B0380 | rule | `legacy_custom` | not_equal_empty_set_from_nonempty | `src/verify/verify_builtin_rules/not_equal_builtin.rs:320` | not equal | none | `pending` |
| B0381 | rule | `local_schema` | not_equal_from_known_strict_order | `src/verify/verify_builtin_rules/not_equal_builtin.rs:356` | not equal | none | `pending` |
| B0382 | rule | `legacy_custom` | not_equal_from_known_strict_order | `src/verify/verify_builtin_rules/not_equal_builtin.rs:366` | not equal | none | `pending` |
| B0383 | rule | `legacy_custom` | not_equal_from_known_positive_lower_bound | `src/verify/verify_builtin_rules/not_equal_builtin.rs:438` | not equal | none | `pending` |
| B0384 | rule | `legacy_custom` | not_equal_from_membership_contradiction | `src/verify/verify_builtin_rules/not_equal_builtin.rs:479` | not equal | none | `pending` |
| B0385 | rule | `legacy_custom` | abs_not_equal_zero_from_arg_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:522` | not equal | none | `pending` |
| B0386 | rule | `legacy_custom` | sqrt(x) != 0 from x > 0 | `src/verify/verify_builtin_rules/not_equal_builtin.rs:564` | not equal | none | `pending` |
| B0387 | rule | `legacy_custom` | sub_not_equal_zero_from_operand_not_equal | `src/verify/verify_builtin_rules/not_equal_builtin.rs:612` | not equal | none | `pending` |
| B0388 | rule | `legacy_custom` | add_not_equal_zero_from_operand_not_equal_negation | `src/verify/verify_builtin_rules/not_equal_builtin.rs:673` | not equal | none | `pending` |
| B0389 | rule | `legacy_custom` | operand_not_equal_from_sub_not_equal_zero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:715` | not equal | none | `pending` |
| B0390 | rule | `legacy_custom` | operand_not_equal_negation_from_add_not_equal_zero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:783` | not equal | none | `pending` |
| B0391 | rule | `legacy_custom` | n != 0 from n $in N and 1 <= n | `src/verify/verify_builtin_rules/not_equal_builtin.rs:821` | not equal | none | `pending` |
| B0392 | rule | `legacy_custom` | n != 0 from n $in N and 1 <= n | `src/verify/verify_builtin_rules/not_equal_builtin.rs:833` | not equal | none | `pending` |
| B0393 | rule | `legacy_custom` | not_equal_pow_from_base_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:910` | not equal | none | `pending` |
| B0394 | rule | `legacy_custom` | not_equal_pow_from_positive_base_carrier | `src/verify/verify_builtin_rules/not_equal_builtin.rs:930` | not equal | none | `pending` |
| B0395 | rule | `local_schema` | div_not_equal_zero_from_numerator_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:996` | not equal | none | `pending` |
| B0396 | rule | `legacy_custom` | div_not_equal_zero_from_numerator_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1006` | not equal | none | `pending` |
| B0397 | rule | `legacy_custom` | product_nonzero_component: a * b != 0 gives a != 0 and b != 0 | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1099` | not equal | none | `pending` |
| B0398 | rule | `legacy_custom` | square_sum_not_equal_zero_from_nonzero_component_or | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1161` | not equal | none | `pending` |
| B0399 | rule | `legacy_custom` | square_sum_not_equal_zero_from_left_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1175` | not equal | none | `pending` |
| B0400 | rule | `legacy_custom` | square_sum_not_equal_zero_from_right_nonzero | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1189` | not equal | none | `pending` |
| B0401 | rule | `legacy_custom` | dynamic: rule_label.to_string() | `src/verify/verify_builtin_rules/not_equal_builtin.rs:1514` | not equal | none | `pending` |
| B0402 | rule | `legacy_custom` | every positive common divisor is at most the gcd | `src/verify/verify_builtin_rules/number_compare.rs:73` | number compare | none | `pending` |
| B0403 | rule | `legacy_custom` | less_equal_fact_equal | `src/verify/verify_builtin_rules/number_compare.rs:311` | number compare | none | `pending` |
| B0404 | rule | `legacy_custom` | less_equal_fact_from_known_equality | `src/verify/verify_builtin_rules/number_compare.rs:325` | number compare | none | `pending` |
| B0405 | rule | `local_schema` | less_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:342` | number compare | none | `pending` |
| B0406 | rule | `legacy_custom` | greater_equal_fact_equal | `src/verify/verify_builtin_rules/number_compare.rs:356` | number compare | none | `pending` |
| B0407 | rule | `legacy_custom` | greater_equal_fact_from_known_equality | `src/verify/verify_builtin_rules/number_compare.rs:370` | number compare | none | `pending` |
| B0408 | rule | `local_schema` | greater_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:389` | number compare | none | `pending` |
| B0409 | rule | `legacy_custom` | native mathematical constant positivity bound | `src/verify/verify_builtin_rules/number_compare.rs:502` | number compare | none | `pending` |
| B0410 | rule | `legacy_custom` | n >= 0 from n $in N | `src/verify/verify_builtin_rules/number_compare.rs:752` | number compare | none | `pending` |
| B0411 | rule | `legacy_custom` | n >= 1 from n $in N+ | `src/verify/verify_builtin_rules/number_compare.rs:800` | number compare | none | `pending` |
| B0412 | rule | `legacy_custom` | finite_nonempty_set_size_at_least_one | `src/verify/verify_builtin_rules/number_compare.rs:862` | number compare | none | `pending` |
| B0413 | rule | `legacy_custom` | finite set cardinality is nonnegative | `src/verify/verify_builtin_rules/number_compare.rs:897` | number compare | none | `pending` |
| B0414 | rule | `legacy_custom` | finite_set_size_subset_le | `src/verify/verify_builtin_rules/number_compare.rs:946` | number compare | none | `pending` |
| B0415 | rule | `legacy_custom` | finite_set_size_subset_le | `src/verify/verify_builtin_rules/number_compare.rs:993` | number compare | none | `pending` |
| B0416 | rule | `legacy_custom` | finite_set_size_union_le_sum | `src/verify/verify_builtin_rules/number_compare.rs:1050` | number compare | none | `pending` |
| B0417 | rule | `legacy_custom` | 1 <= n from n $in N and n != 0 | `src/verify/verify_builtin_rules/number_compare.rs:1118` | number compare | none | `pending` |
| B0418 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1192` | number compare | none | `pending` |
| B0419 | rule | `legacy_custom` | 1 <= n from n $in Z and 0 < n | `src/verify/verify_builtin_rules/number_compare.rs:1246` | number compare | none | `pending` |
| B0420 | rule | `local_schema` | less_equal_fact_from_known_strict_order | `src/verify/verify_builtin_rules/number_compare.rs:1287` | number compare | none | `pending` |
| B0421 | rule | `legacy_custom` | weaken numeric lower bound from known lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1299` | number compare | none | `pending` |
| B0422 | rule | `legacy_custom` | integer weak lower bound from strict predecessor lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1318` | number compare | none | `pending` |
| B0423 | rule | `legacy_custom` | weaken numeric strict lower bound from known lower bound | `src/verify/verify_builtin_rules/number_compare.rs:1352` | number compare | none | `pending` |
| B0424 | rule | `legacy_custom` | weaken numeric upper bound from known upper bound | `src/verify/verify_builtin_rules/number_compare.rs:1449` | number compare | none | `pending` |
| B0425 | rule | `legacy_custom` | 0 <= abs(x) for x in R | `src/verify/verify_builtin_rules/number_compare.rs:1519` | number compare | none | `pending` |
| B0426 | rule | `legacy_custom` | sqrt: 0 <= sqrt(x) from 0 <= x | `src/verify/verify_builtin_rules/number_compare.rs:1558` | number compare | none | `pending` |
| B0427 | rule | `legacy_custom` | sqrt: 0 < sqrt(x) from 0 < x | `src/verify/verify_builtin_rules/number_compare.rs:1596` | number compare | none | `pending` |
| B0428 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1675` | number compare | none | `pending` |
| B0429 | rule | `legacy_custom` | dynamic: msg.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:1693` | number compare | none | `pending` |
| B0430 | rule | `legacy_custom` | order_from_known_negated_complement | `src/verify/verify_builtin_rules/number_compare.rs:1938` | number compare | none | `pending` |
| B0431 | rule | `legacy_custom` | log order: base > 1 preserves strict order | `src/verify/verify_builtin_rules/number_compare.rs:2012` | number compare | none | `pending` |
| B0432 | rule | `legacy_custom` | log order: 0 < base < 1 reverses strict order | `src/verify/verify_builtin_rules/number_compare.rs:2028` | number compare | none | `pending` |
| B0433 | rule | `legacy_custom` | log sign: 0 < log(a, x) from 1 < a and 1 < x | `src/verify/verify_builtin_rules/number_compare.rs:2057` | number compare | none | `pending` |
| B0434 | rule | `legacy_custom` | log sign: log(a, x) < 0 from 1 < a and 0 < x < 1 | `src/verify/verify_builtin_rules/number_compare.rs:2093` | number compare | none | `pending` |
| B0435 | rule | `legacy_custom` | negated_order_from_known_equivalent_order | `src/verify/verify_builtin_rules/number_compare.rs:2168` | number compare | none | `pending` |
| B0436 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2212` | number compare | none | `pending` |
| B0437 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2239` | number compare | none | `pending` |
| B0438 | rule | `local_schema` | 0 <= u - v from v <= u | `src/verify/verify_builtin_rules/number_compare.rs:2271` | number compare | none | `pending` |
| B0439 | rule | `local_schema` | 0 < u - v from v < u | `src/verify/verify_builtin_rules/number_compare.rs:2297` | number compare | none | `pending` |
| B0440 | rule | `local_schema` | 0 <= a + b from known atomic facts 0 <= a and 0 <= b | `src/verify/verify_builtin_rules/number_compare.rs:2358` | number compare | none | `pending` |
| B0441 | rule | `local_schema` | 0 < a + b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2407` | number compare | none | `pending` |
| B0442 | rule | `local_schema` | 0 < a + b from (0 < a and 0 <= b) | `src/verify/verify_builtin_rules/number_compare.rs:2443` | number compare | none | `pending` |
| B0443 | rule | `local_schema` | 0 < a + b from (0 <= a and 0 < b) | `src/verify/verify_builtin_rules/number_compare.rs:2477` | number compare | none | `pending` |
| B0444 | rule | `legacy_custom` | dynamic: msg | `src/verify/verify_builtin_rules/number_compare.rs:2539` | number compare | none | `pending` |
| B0445 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/number_compare.rs:2597` | number compare | none | `pending` |
| B0446 | rule | `legacy_custom` | 0 < a^b from 0 < a and b in R | `src/verify/verify_builtin_rules/number_compare.rs:2642` | number compare | none | `pending` |
| B0447 | rule | `legacy_custom` | 0 <= a^b from 0 < a and b in R | `src/verify/verify_builtin_rules/number_compare.rs:2688` | number compare | none | `pending` |
| B0448 | rule | `legacy_custom` | 0 <= a^n from 0 <= a and n in N+ | `src/verify/verify_builtin_rules/number_compare.rs:2735` | number compare | none | `pending` |
| B0449 | rule | `legacy_custom` | dynamic: msg | `src/verify/verify_builtin_rules/number_compare.rs:2794` | number compare | none | `pending` |
| B0450 | rule | `local_schema` | 0 <= a * b from 0 <= a and 0 <= b | `src/verify/verify_builtin_rules/number_compare.rs:2846` | number compare | none | `pending` |
| B0451 | rule | `local_schema` | 0 < a * b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2899` | number compare | none | `pending` |
| B0452 | rule | `local_schema` | 0 <= a / b from 0 <= a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:2952` | number compare | none | `pending` |
| B0453 | rule | `local_schema` | 0 < a / b from 0 < a and 0 < b | `src/verify/verify_builtin_rules/number_compare.rs:3005` | number compare | none | `pending` |
| B0454 | rule | `legacy_custom` | a^n <= b^n from 0 <= a, a <= b, and positive integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:318` | order algebra | none | `pending` |
| B0455 | rule | `legacy_custom` | a <= b from 0 <= a, 0 <= b, a^n <= b^n, and n in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:428` | order algebra | none | `pending` |
| B0456 | rule | `legacy_custom` | a <= b from positive bases and exponent, and a^q <= b^q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:474` | order algebra | none | `pending` |
| B0457 | rule | `legacy_custom` | a^n <= b^n from a <= b and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:517` | order algebra | none | `pending` |
| B0458 | rule | `legacy_custom` | a^n <= b^n from 0 < b <= a and negative integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:567` | order algebra | none | `pending` |
| B0459 | rule | `legacy_custom` | a^k <= b^k from abs(a) <= abs(b) and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:608` | order algebra | none | `pending` |
| B0460 | rule | `legacy_custom` | a^k < b^k from abs(a) < abs(b) and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:648` | order algebra | none | `pending` |
| B0461 | rule | `legacy_custom` | abs(x) <= abs(y) from x^k <= y^k and even k in N+ | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:707` | order algebra | none | `pending` |
| B0462 | rule | `legacy_custom` | a^q < b^q from 0 < a, 0 < b, a < b, 0 < q, and q in R or Q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:768` | order algebra | none | `pending` |
| B0463 | rule | `legacy_custom` | a < b from positive bases and exponent, and a^q < b^q | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:811` | order algebra | none | `pending` |
| B0464 | rule | `legacy_custom` | a^n < b^n from a < b and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:854` | order algebra | none | `pending` |
| B0465 | rule | `legacy_custom` | a^n <= 0 from a <= 0 and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:887` | order algebra | none | `pending` |
| B0466 | rule | `legacy_custom` | a^n < 0 from a < 0 and positive odd integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:920` | order algebra | none | `pending` |
| B0467 | rule | `legacy_custom` | a^n < b^n from 0 <= a, a < b, and positive integer n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:972` | order algebra | none | `pending` |
| B0468 | rule | `legacy_custom` | x1 * x2 <= y1 * y2 from 0 <= factors and componentwise <= | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1096` | order algebra | none | `pending` |
| B0469 | rule | `legacy_custom` | a * b <= 0 from a <= 0 and 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1128` | order algebra | none | `pending` |
| B0470 | rule | `legacy_custom` | 0 <= a * b from a,b having the same weak sign | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1168` | order algebra | none | `pending` |
| B0471 | rule | `legacy_custom` | a * b < 0 from opposite strict signs | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1201` | order algebra | none | `pending` |
| B0472 | rule | `legacy_custom` | 0 < a * b from same strict signs | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1248` | order algebra | none | `pending` |
| B0473 | rule | `quantified` | finite sum monotonicity from pointwise order on the index range | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1352` | order algebra | none | `pending` |
| B0474 | rule | `quantified` | finite-set sum monotonicity from pointwise order on the finite set | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1414` | order algebra | none | `pending` |
| B0475 | rule | `legacy_custom` | finite-set sum: non-negative summand is at most the total | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1484` | order algebra | none | `pending` |
| B0476 | rule | `legacy_custom` | a / c <= b / c from 0 < c and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1547` | order algebra | none | `pending` |
| B0477 | rule | `legacy_custom` | b / c <= a / c from c < 0 and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1571` | order algebra | none | `pending` |
| B0478 | rule | `local_schema` | u + a <= u + b from a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1666` | order algebra | none | `pending` |
| B0479 | rule | `local_schema` | a - c <= b from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1691` | order algebra | none | `pending` |
| B0480 | rule | `legacy_custom` | a - c <= b from a <= b + c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1710` | order algebra | none | `pending` |
| B0481 | rule | `local_schema` | a <= a + b from 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1733` | order algebra | none | `pending` |
| B0482 | rule | `legacy_custom` | a <= b + c from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1753` | order algebra | none | `pending` |
| B0483 | rule | `legacy_custom` | a <= b + c from a <= b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1768` | order algebra | none | `pending` |
| B0484 | rule | `legacy_custom` | a <= b - c from a + c <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1786` | order algebra | none | `pending` |
| B0485 | rule | `legacy_custom` | a <= x - n from a + n <= x | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1803` | order algebra | none | `pending` |
| B0486 | rule | `legacy_custom` | a - n <= a for n >= 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1819` | order algebra | none | `pending` |
| B0487 | rule | `legacy_custom` | a + b <= 0 from a <= 0 and b <= 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1840` | order algebra | none | `pending` |
| B0488 | rule | `legacy_custom` | a <= b * a from 0 <= a and 1 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1898` | order algebra | none | `pending` |
| B0489 | rule | `legacy_custom` | k * a <= k * b from 0 <= k and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1920` | order algebra | none | `pending` |
| B0490 | rule | `legacy_custom` | k * a <= k * b from k <= 0 and b <= a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1920` | order algebra | none | `pending` |
| B0491 | rule | `legacy_custom` | a * k <= b * k from 0 <= k and a <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1934` | order algebra | none | `pending` |
| B0492 | rule | `legacy_custom` | a * k <= b * k from k <= 0 and b <= a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1934` | order algebra | none | `pending` |
| B0493 | rule | `local_schema` | a + c <= b + d from a <= b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:1971` | order algebra | none | `pending` |
| B0494 | rule | `legacy_custom` | a - d <= b - c from a <= b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2006` | order algebra | none | `pending` |
| B0495 | rule | `legacy_custom` | a <= b / c from 0 < c and (c * a <= b or a * c <= b) | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2062` | order algebra | none | `pending` |
| B0496 | rule | `legacy_custom` | a <= b * c from 0 < c and a / c <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2112` | order algebra | none | `pending` |
| B0497 | rule | `legacy_custom` | a / c < b / c from 0 < c and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2154` | order algebra | none | `pending` |
| B0498 | rule | `legacy_custom` | b / c < a / c from c < 0 and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2178` | order algebra | none | `pending` |
| B0499 | rule | `local_schema` | u + a < u + b from a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2245` | order algebra | none | `pending` |
| B0500 | rule | `legacy_custom` | a - d < b - c from a < b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2277` | order algebra | none | `pending` |
| B0501 | rule | `legacy_custom` | a - d < b - c from a <= b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2303` | order algebra | none | `pending` |
| B0502 | rule | `legacy_custom` | abs(x - n) < abs(x) for positive x and nonnegative x - n | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2328` | order algebra | none | `pending` |
| B0503 | rule | `legacy_custom` | a - c < b from a < b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2353` | order algebra | none | `pending` |
| B0504 | rule | `legacy_custom` | a - c < b from a <= b and 0 < c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2372` | order algebra | none | `pending` |
| B0505 | rule | `legacy_custom` | a - c < b from a < b + c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2388` | order algebra | none | `pending` |
| B0506 | rule | `legacy_custom` | a < a + b from 0 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2411` | order algebra | none | `pending` |
| B0507 | rule | `legacy_custom` | a < b + c from a < b and 0 <= c | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2428` | order algebra | none | `pending` |
| B0508 | rule | `legacy_custom` | a < b + c from a < c and 0 <= b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2443` | order algebra | none | `pending` |
| B0509 | rule | `legacy_custom` | a < b - c from a + c < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2461` | order algebra | none | `pending` |
| B0510 | rule | `legacy_custom` | a - n < a for n > 0 | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2475` | order algebra | none | `pending` |
| B0511 | rule | `legacy_custom` | a / b < a from 0 < a and 1 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2500` | order algebra | none | `pending` |
| B0512 | rule | `legacy_custom` | a + b < 0 from one negative term and one nonpositive term | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2530` | order algebra | none | `pending` |
| B0513 | rule | `legacy_custom` | a < b * a from 0 < a and 1 < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2590` | order algebra | none | `pending` |
| B0514 | rule | `legacy_custom` | k * a < k * b from 0 < k and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2601` | order algebra | none | `pending` |
| B0515 | rule | `legacy_custom` | k * a < k * b from k < 0 and b < a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2601` | order algebra | none | `pending` |
| B0516 | rule | `legacy_custom` | a * k < b * k from 0 < k and a < b | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2615` | order algebra | none | `pending` |
| B0517 | rule | `legacy_custom` | a * k < b * k from k < 0 and b < a | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2615` | order algebra | none | `pending` |
| B0518 | rule | `local_schema` | a + c < b + d from a < b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2647` | order algebra | none | `pending` |
| B0519 | rule | `local_schema` | a + c < b + d from a < b and c <= d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2673` | order algebra | none | `pending` |
| B0520 | rule | `local_schema` | a + c < b + d from a <= b and c < d | `src/verify/verify_builtin_rules/order_algebra_builtin.rs:2699` | order algebra | none | `pending` |
| B0521 | rule | `legacy_custom` | positive even integer is greater than one | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:162` | order semantics | none | `pending` |
| B0522 | rule | `legacy_custom` | order: transitivity through a shared ordered numeric middle term | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:244` | order semantics | none | `pending` |
| B0523 | rule | `legacy_custom` | finite_set_max: every member is at most the maximum | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:281` | order semantics | none | `pending` |
| B0524 | rule | `legacy_custom` | finite_set_max: every member is at most a known-equal maximum | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:310` | order semantics | none | `pending` |
| B0525 | rule | `legacy_custom` | finite_set_min: the minimum is at most every member | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:331` | order semantics | none | `pending` |
| B0526 | rule | `legacy_custom` | finite_set_min: a known-equal minimum is at most every member | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:360` | order semantics | none | `pending` |
| B0527 | rule | `legacy_custom` | membership by concrete finite-set structure | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:388` | order semantics | none | `pending` |
| B0528 | rule | `legacy_custom` | integer difference: a < b gives b - a >= 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:472` | order semantics | none | `pending` |
| B0529 | rule | `legacy_custom` | integer adjacency: a < b + 1 gives a <= b | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:500` | order semantics | none | `pending` |
| B0530 | rule | `legacy_custom` | integer successor: a < b gives a + 1 <= b | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:524` | order semantics | none | `pending` |
| B0531 | rule | `legacy_custom` | integer predecessor: a < b gives a <= b - 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:548` | order semantics | none | `pending` |
| B0532 | rule | `legacy_custom` | integer singleton interval: n <= x < n + 1 gives x = n | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:591` | order semantics | none | `pending` |
| B0533 | rule | `legacy_custom` | integer successor singleton interval: n < x <= n + 1 gives x = n + 1 | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:625` | order semantics | none | `pending` |
| B0534 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/order_semantics_builtin.rs:680` | order semantics | none | `pending` |
| B0535 | rule | `reflection` | deterministic primality computation for u64 | `src/verify/verify_builtin_rules/prime_builtin.rs:23` | prime | none | `not_this_round` |
| B0536 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_builtin_rules/set_relation_duality.rs:34` | set relation duality | none | `pending` |
| B0537 | rule | `legacy_custom` | union subset from both operand subsets | `src/verify/verify_builtin_rules/set_relation_duality.rs:64` | set relation duality | none | `pending` |
| B0538 | rule | `reflection` | literal finite-set subset from member facts | `src/verify/verify_builtin_rules/set_relation_duality.rs:95` | set relation duality | none | `not_this_round` |
| B0539 | rule | `legacy_custom` | Cartesian-product subset from componentwise subsets | `src/verify/verify_builtin_rules/set_relation_duality.rs:131` | set relation duality | none | `pending` |
| B0540 | rule | `legacy_custom` | standard_set_subset | `src/verify/verify_builtin_rules/set_relation_duality.rs:148` | set relation duality | none | `pending` |
| B0541 | rule | `legacy_custom` | integer range is contained in its standard numeric carrier | `src/verify/verify_builtin_rules/set_relation_duality.rs:192` | set relation duality | none | `pending` |
| B0542 | rule | `legacy_custom` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:206` | set relation duality | none | `pending` |
| B0543 | rule | `legacy_custom` | real_interval_subset_R | `src/verify/verify_builtin_rules/set_relation_duality.rs:221` | set relation duality | none | `pending` |
| B0544 | rule | `legacy_custom` | structural subset | `src/verify/verify_builtin_rules/set_relation_duality.rs:244` | set relation duality | none | `pending` |
| B0545 | rule | `legacy_custom` | fn_range_subset_codomain | `src/verify/verify_builtin_rules/set_relation_duality.rs:255` | set relation duality | none | `pending` |
| B0546 | rule | `local_schema` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:276` | set relation duality | none | `pending` |
| B0547 | rule | `legacy_custom` | standard_set_superset | `src/verify/verify_builtin_rules/set_relation_duality.rs:303` | set relation duality | none | `pending` |
| B0548 | rule | `legacy_custom` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:320` | set relation duality | none | `pending` |
| B0549 | rule | `local_schema` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:338` | set relation duality | none | `pending` |
| B0550 | rule | `local_schema` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:370` | set relation duality | none | `pending` |
| B0551 | rule | `local_schema` | subset_superset_duality | `src/verify/verify_builtin_rules/set_relation_duality.rs:402` | set relation duality | none | `pending` |
| B0552 | rule | `legacy_custom` | dynamic: reason | `src/verify/verify_builtin_rules/trigonometry.rs:155` | trigonometry | none | `pending` |
| B0553 | rule | `legacy_custom` | dynamic: format!( "trigonometry layer {}: {} derived from the unit-circle identity", TrigLemma::Bounds.level(), TrigLemma::Bounds.name() ) | `src/verify/verify_builtin_rules/trigonometry.rs:197` | trigonometry | none | `pending` |
| B0554 | rule | `legacy_custom` | trigonometry: -1 <= sin/cos <= 1 from the unit-circle square bound | `src/verify/verify_builtin_rules/trigonometry.rs:225` | trigonometry | none | `pending` |
| B0555 | rule | `legacy_custom` | dynamic: format!("trigonometry: {reason}") | `src/verify/verify_builtin_rules/trigonometry.rs:561` | trigonometry | none | `pending` |
| B0556 | rule | `legacy_custom` | trigonometry: sine/cosine is nonzero on a canonical sign interval | `src/verify/verify_builtin_rules/trigonometry.rs:669` | trigonometry | none | `pending` |
| B0557 | rule | `legacy_custom` | trigonometry: pi shift changes only sign, preserving non-zero | `src/verify/verify_builtin_rules/trigonometry.rs:689` | trigonometry | none | `pending` |
| B0558 | rule | `legacy_custom` | trigonometry: non-zero transfer through canonical expansion | `src/verify/verify_builtin_rules/trigonometry.rs:712` | trigonometry | none | `pending` |
| B0559 | rule | `definition` | trigonometry core: tan/cot quotient definition | `src/verify/verify_builtin_rules/trigonometry.rs:1072` | trigonometry | none | `pending` |
| B0560 | rule | `legacy_custom` | trigonometry core: sin(x)^2 + cos(x)^2 = 1 | `src/verify/verify_builtin_rules/trigonometry.rs:1092` | trigonometry | none | `pending` |
| B0561 | rule | `legacy_custom` | trigonometry core: sine addition formula | `src/verify/verify_builtin_rules/trigonometry.rs:1194` | trigonometry | none | `pending` |
| B0562 | rule | `legacy_custom` | nonempty_set_from_not_equal_empty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:22` | type predicates | none | `pending` |
| B0563 | rule | `legacy_custom` | standard_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:41` | type predicates | none | `pending` |
| B0564 | rule | `legacy_custom` | list_set_nonempty_has_member_in_syntax | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:53` | type predicates | none | `pending` |
| B0565 | rule | `legacy_custom` | power_set_is_nonempty_because_empty_set_is_subset | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:65` | type predicates | none | `pending` |
| B0566 | rule | `legacy_custom` | closed_range_nonempty_when_start_le_end | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:87` | type predicates | none | `pending` |
| B0567 | rule | `legacy_custom` | range_nonempty_when_start_lt_end | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:109` | type predicates | none | `pending` |
| B0568 | rule | `legacy_custom` | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:154` | type predicates | none | `pending` |
| B0569 | rule | `legacy_custom` | dynamic: rule.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:180` | type predicates | none | `pending` |
| B0570 | rule | `legacy_custom` | union_is_nonempty_set_when_left_side_is_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:200` | type predicates | none | `pending` |
| B0571 | rule | `legacy_custom` | union_is_nonempty_set_when_right_side_is_nonempty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:218` | type predicates | none | `pending` |
| B0572 | rule | `legacy_custom` | dynamic: format!( "sets '{}' in '{}' are nonempty sets", cart.args .iter() .map(\|arg\| arg.as_ref().to_string()) .collect::<Vec<String>>() .join(", "), cart.to_string() ) | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:246` | type predicates | none | `pending` |
| B0573 | rule | `legacy_custom` | fn_set_is_nonempty_when_ret_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:272` | type predicates | none | `pending` |
| B0574 | rule | `legacy_custom` | fn_set_is_nonempty_when_ret_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:293` | type predicates | none | `pending` |
| B0575 | rule | `legacy_custom` | finite_seq_set_is_nonempty_when_length_is_zero | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:316` | type predicates | none | `pending` |
| B0576 | rule | `legacy_custom` | finite_seq_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:334` | type predicates | none | `pending` |
| B0577 | rule | `legacy_custom` | seq_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:355` | type predicates | none | `pending` |
| B0578 | rule | `legacy_custom` | matrix_set_is_nonempty_when_codomain_set_is_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:376` | type predicates | none | `pending` |
| B0579 | rule | `legacy_custom` | nonempty_set_from_equal_structural_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:406` | type predicates | none | `pending` |
| B0580 | rule | `legacy_custom` | nonempty_finite_set_from_positive_finite_set_size | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:451` | type predicates | none | `pending` |
| B0581 | rule | `legacy_custom` | list_set_finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:473` | type predicates | none | `pending` |
| B0582 | rule | `legacy_custom` | closed_range_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:481` | type predicates | none | `pending` |
| B0583 | rule | `legacy_custom` | range_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:489` | type predicates | none | `pending` |
| B0584 | rule | `legacy_custom` | set-builder over a finite base is finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:510` | type predicates | none | `pending` |
| B0585 | rule | `legacy_custom` | fn_range_is_finite_set_when_domain_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:539` | type predicates | none | `pending` |
| B0586 | rule | `legacy_custom` | union_is_finite_set_when_both_sides_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:575` | type predicates | none | `pending` |
| B0587 | rule | `legacy_custom` | intersect_is_finite_set_when_both_sides_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:608` | type predicates | none | `pending` |
| B0588 | rule | `legacy_custom` | set_minus_is_finite_set_when_left_side_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:630` | type predicates | none | `pending` |
| B0589 | rule | `legacy_custom` | power_set_is_finite_set_when_base_is_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:652` | type predicates | none | `pending` |
| B0590 | rule | `legacy_custom` | cart_is_finite_set_when_all_factors_are_finite_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:679` | type predicates | none | `pending` |
| B0591 | rule | `legacy_custom` | set_minus_is_infinite_when_left_side_is_infinite_and_right_side_is_finite | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:736` | type predicates | none | `pending` |
| B0592 | rule | `legacy_custom` | any 'cart' object is a cart | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:754` | type predicates | none | `pending` |
| B0593 | rule | `legacy_custom` | any 'cart_dim' object is a cart_dim | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:777` | type predicates | none | `pending` |
| B0594 | rule | `legacy_custom` | it is a known tuple | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:792` | type predicates | none | `pending` |
| B0595 | rule | `legacy_custom` | list_set_empty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:814` | type predicates | none | `pending` |
| B0596 | rule | `legacy_custom` | finite_set_size_zero_is_not_nonempty | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:834` | type predicates | none | `pending` |
| B0597 | rule | `legacy_custom` | not_nonempty_set_from_equal_empty_set | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:850` | type predicates | none | `pending` |
| B0598 | rule | `legacy_custom` | closed_range_empty_when_end_lt_start | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:871` | type predicates | none | `pending` |
| B0599 | rule | `legacy_custom` | range_empty_when_end_le_start | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:892` | type predicates | none | `pending` |
| B0600 | rule | `legacy_custom` | dynamic: label.to_string() | `src/verify/verify_builtin_rules/type_predicates_builtin.rs:933` | type predicates | none | `pending` |
| B0601 | strategy | `strategy` | finite-set product congruence strategy: prove pointwise factor equality | `src/verify/verify_builtin_strategies/equality.rs:68` | builtin strategy | none | `pending` |
| B0602 | strategy | `strategy` | finite-extremum equality strategy: prove both weak-order directions | `src/verify/verify_builtin_strategies/equality.rs:119` | builtin strategy | none | `pending` |
| B0603 | strategy | `strategy` | mod-congruence strategy: reduce immediate binary operands modulo m | `src/verify/verify_builtin_strategies/equality.rs:203` | builtin strategy | none | `pending` |
| B0604 | strategy | `strategy` | numeric-carrier strategy: cardinality of a structurally finite set | `src/verify/verify_builtin_strategies/numeric_carrier.rs:34` | builtin strategy | none | `pending` |
| B0605 | strategy | `strategy` | numeric-carrier strategy: finite extremum source is real-valued | `src/verify/verify_builtin_strategies/numeric_carrier.rs:50` | builtin strategy | none | `pending` |
| B0606 | strategy | `strategy` | dynamic: format!( "numeric-carrier strategy: base carrier and sign conditions for {target}" ) | `src/verify/verify_builtin_strategies/numeric_carrier.rs:65` | builtin strategy | none | `pending` |
| B0607 | strategy | `strategy` | dynamic: format!("numeric-carrier strategy: structural closure in {target}") | `src/verify/verify_builtin_strategies/numeric_carrier.rs:98` | builtin strategy | none | `pending` |
| B0608 | strategy | `strategy` | numeric-carrier strategy: structural closure in N+ | `src/verify/verify_builtin_strategies/numeric_carrier.rs:352` | builtin strategy | none | `pending` |
| B0609 | strategy | `strategy` | additive sign strategy: normalized order goal | `src/verify/verify_builtin_strategies/numeric_sign.rs:21` | builtin strategy | none | `pending` |
| B0610 | strategy | `strategy` | dynamic: strategy_label | `src/verify/verify_builtin_strategies/numeric_sign.rs:35` | builtin strategy | none | `pending` |
| B0611 | strategy | `strategy` | dynamic: strategy_label | `src/verify/verify_builtin_strategies/numeric_sign.rs:41` | builtin strategy | none | `pending` |
| B0612 | strategy | `strategy` | additive sign strategy: nonnegative summands | `src/verify/verify_builtin_strategies/numeric_sign.rs:71` | builtin strategy | none | `pending` |
| B0613 | strategy | `strategy` | additive sign strategy: one positive and one nonnegative summand | `src/verify/verify_builtin_strategies/numeric_sign.rs:89` | builtin strategy | none | `pending` |
| B0614 | strategy | `strategy` | set-membership strategy: constructor membership decomposition | `src/verify/verify_builtin_strategies/set_membership.rs:109` | builtin strategy | none | `pending` |
| B0615 | strategy | `strategy` | set-builder membership strategy: unfold one set definition and verify its atomic obligations | `src/verify/verify_builtin_strategies/set_membership.rs:250` | builtin strategy | none | `pending` |
| B0616 | strategy | `strategy` | set-builder membership strategy: unfold one set definition and verify its atomic obligations | `src/verify/verify_builtin_strategies/set_membership.rs:266` | builtin strategy | none | `pending` |
| B0617 | strategy | `strategy` | set-containment strategy: constructor containment decomposition | `src/verify/verify_builtin_strategies/set_membership.rs:327` | builtin strategy | none | `pending` |
| B0618 | strategy | `strategy` | dynamic: reason.to_string() | `src/verify/verify_builtin_strategies/type_predicates.rs:99` | builtin strategy | none | `pending` |
| B0619 | strategy | `strategy` | nonempty-set strategy: closed integer range has ordered endpoints | `src/verify/verify_builtin_strategies/type_predicates.rs:142` | builtin strategy | none | `pending` |
| B0620 | strategy | `strategy` | nonempty-set strategy: half-open integer range has strictly ordered endpoints | `src/verify/verify_builtin_strategies/type_predicates.rs:165` | builtin strategy | none | `pending` |
| B0621 | strategy | `strategy` | dynamic: reason.to_string() | `src/verify/verify_builtin_strategies/type_predicates.rs:204` | builtin strategy | none | `pending` |
| B0622 | strategy | `strategy` | nonempty-set strategy: a union has a nonempty side | `src/verify/verify_builtin_strategies/type_predicates.rs:218` | builtin strategy | none | `pending` |
| B0623 | strategy | `strategy` | nonempty-set strategy: all Cartesian factors are nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:241` | builtin strategy | none | `pending` |
| B0624 | strategy | `strategy` | nonempty-set strategy: function codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:249` | builtin strategy | none | `pending` |
| B0625 | strategy | `strategy` | nonempty-set strategy: anonymous-function codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:254` | builtin strategy | none | `pending` |
| B0626 | strategy | `strategy` | nonempty-set strategy: finite-sequence codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:259` | builtin strategy | none | `pending` |
| B0627 | strategy | `strategy` | nonempty-set strategy: sequence codomain is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:264` | builtin strategy | none | `pending` |
| B0628 | strategy | `strategy` | nonempty-set strategy: matrix entry set is nonempty | `src/verify/verify_builtin_strategies/type_predicates.rs:269` | builtin strategy | none | `pending` |
| B0629 | rule | `legacy_custom` | dynamic: same_shape_and_equal_args_reason(&equal_fact.left, &equal_fact.right) | `src/verify/verify_equality.rs:45` | equality | none | `pending` |
| B0630 | rule | `legacy_custom` | builtin rules | `src/verify/verify_equality.rs:560` | equality | none | `pending` |
| B0631 | rule | `legacy_custom` | dynamic: same_shape_and_equal_args_reason(left_obj, right_obj) | `src/verify/verify_equality.rs:593` | equality | none | `pending` |
| B0632 | rule | `legacy_custom` | exist: real-line comparison witness | `src/verify/verify_exist_fact.rs:461` | exist fact | none | `pending` |
| B0633 | rule | `legacy_custom` | exist: member of a nonempty set | `src/verify/verify_exist_fact.rs:480` | exist fact | none | `pending` |
| B0634 | rule | `legacy_custom` | exist: rational representation with positive integer denominator | `src/verify/verify_exist_fact.rs:505` | exist fact | none | `pending` |
| B0635 | rule | `legacy_custom` | exist: rational integer ratio representation | `src/verify/verify_exist_fact.rs:530` | exist fact | none | `pending` |
| B0636 | rule | `legacy_custom` | exist!: unique Euclidean quotient for an integer and positive divisor | `src/verify/verify_exist_fact.rs:557` | exist fact | none | `pending` |
| B0637 | rule | `legacy_custom` | exist: zero remainder gives an integer multiple of a nonzero modulus | `src/verify/verify_exist_fact.rs:613` | exist fact | none | `pending` |
| B0638 | rule | `legacy_custom` | exist: Archimedean reciprocal bound | `src/verify/verify_exist_fact.rs:644` | exist fact | none | `pending` |
| B0639 | rule | `legacy_custom` | exist: rational density in the real line | `src/verify/verify_exist_fact.rs:671` | exist fact | none | `pending` |
| B0640 | rule | `legacy_custom` | exist: real density by the midpoint principle | `src/verify/verify_exist_fact.rs:699` | exist fact | none | `pending` |
| B0641 | rule | `legacy_custom` | dynamic: rule.to_string() | `src/verify/verify_exist_fact.rs:740` | exist fact | none | `pending` |
| B0642 | rule | `legacy_custom` | finite nonempty natural set has a greatest member | `src/verify/verify_exist_fact.rs:896` | exist fact | none | `pending` |
| B0643 | rule | `legacy_custom` | fn_eq_in: pointwise equality on the given set (forall x in S, f(x)=g(x)) | `src/verify/verify_fn_equal_in_builtin.rs:56` | fn equal in | none | `pending` |
| B0644 | rule | `legacy_custom` | fn_eq: exact known pointwise forall over alpha-equivalent function carriers | `src/verify/verify_fn_equal_in_builtin.rs:108` | fn equal in | none | `pending` |
| B0645 | rule | `legacy_custom` | fn_eq: mutual function-space membership and pointwise equality (forall+dom) | `src/verify/verify_fn_equal_in_builtin.rs:167` | fn equal in | none | `pending` |
| B0646 | rule | `definition` | dynamic: format!( "anonymous fn satisfies a declared return set through an equal {}", representative_kind ) | `src/verify/verify_fn_membership_by_definition.rs:65` | fn membership by definition | none | `pending` |
| B0647 | rule | `definition` | indexed result inherits its carrier from a symbolic Cartesian projection | `src/verify/verify_fn_membership_by_definition.rs:156` | fn membership by definition | none | `pending` |
| B0648 | rule | `definition` | fn membership: same input domain and pointwise values lie in the target return set | `src/verify/verify_fn_membership_by_definition.rs:207` | fn membership by definition | none | `pending` |
| B0649 | rule | `legacy_custom` | fnset equality: mutual implication of param sets, dom facts, and ret set | `src/verify/verify_fn_set_equality_builtin_rule.rs:34` | fn set equality builtin rule | none | `pending` |
| B0650 | rule | `quantified` | forall over empty parameter set | `src/verify/verify_forall_fact.rs:197` | forall fact | none | `pending` |
| B0651 | rule | `quantified` | forall iff: then=>iff and iff=>then verified | `src/verify/verify_forall_fact_with_iff.rs:38` | forall fact with iff | none | `pending` |
| B0652 | rule | `definition` | dynamic: format!( "{} by its builtin function-property definition", fact.predicate ) | `src/verify/verify_function_properties_builtin.rs:26` | function properties | none | `pending` |
| B0653 | rule | `legacy_custom` | restricted builtin premise: each conjunct verified | `src/verify/verify_helper.rs:264` | helper | none | `pending` |
| B0654 | rule | `legacy_custom` | restricted builtin premise: one branch verified | `src/verify/verify_helper.rs:302` | helper | none | `pending` |
| B0655 | rule | `legacy_custom` | registered reflexive prop | `src/verify/verify_non_equational_atomic_fact.rs:145` | non equational atomic fact | none | `pending` |
| B0656 | rule | `legacy_custom` | dynamic: reason.to_string() | `src/verify/verify_or_fact.rs:456` | or fact | none | `pending` |
| B0657 | rule | `legacy_custom` | or: complementary atomic facts | `src/verify/verify_or_fact.rs:475` | or fact | none | `pending` |
| B0658 | rule | `legacy_custom` | or: complementary order relations (strict vs non-strict) on the same real terms | `src/verify/verify_or_fact.rs:494` | or fact | none | `pending` |
| B0659 | rule | `legacy_custom` | or: equality plus strict order covers a known weak order | `src/verify/verify_or_fact.rs:515` | or fact | none | `pending` |
| B0660 | rule | `legacy_custom` | or: abs(x) is x or -x | `src/verify/verify_or_fact.rs:529` | or fact | none | `pending` |
| B0661 | rule | `legacy_custom` | or: complete residue classes modulo a positive integer | `src/verify/verify_or_fact.rs:542` | or fact | none | `pending` |
| B0662 | rule | `legacy_custom` | dynamic: format!( "or: classical implication packaging; '{}' follows under '{}'", conclusion, assumed_opposite ) | `src/verify/verify_or_fact.rs:641` | or fact | none | `pending` |
| B0663 | rule | `legacy_custom` | or: integer lower bound split into finite successors and strict tail | `src/verify/verify_or_fact.rs:688` | or fact | none | `pending` |
| B0664 | rule | `legacy_custom` | zero_product_split: a * b = 0 gives a = 0 or b = 0 | `src/verify/verify_or_fact.rs:747` | or fact | none | `pending` |
| B0665 | rule | `legacy_custom` | or: square sum nonzero implies one component nonzero | `src/verify/verify_or_fact.rs:811` | or fact | none | `pending` |
| B0666 | rule | `definition` | dynamic: format!( "{} by its builtin proper-set-relation definition", atomic_fact.key() ) | `src/verify/verify_proper_set_relations_builtin.rs:25` | proper set relations | none | `pending` |
