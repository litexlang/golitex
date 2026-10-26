# Finite-set counting and inclusion-exclusion

The imported caller counts three overlapping sets, both with empty and with
nonempty triple intersection. It also checks symmetric differences, subset
differences, additivity versus disjointness, Cartesian products, powersets,
identical sets and empty factors. It uses the ordinary native cardinality
operation and the existing combinatorics module.

The compound finiteness facts are obtained from named source closure theorems
in two generic claims before the count expressions are used. This preserves
the full finite-set domains across imports without adding caller hypotheses.
Numerical observations retain explicit set and equality bridges.

Run `python3 examples/combinatorics/finite_sets/check.py`. It verifies source,
concrete caller, independent contracts, README excerpt, semantic rejection
controls, both installed layouts and full std/WiX payload equality. Check
artifacts can be saved with `--output-dir`. All proofs are strict; native
cardinality rules are reused. No general indexed inclusion-exclusion, binomial
coefficient construction, probability or global release coverage is claimed.
