# Topology Setting-Bundle Migration

The registered implementation is
[`main.lit`](./main.lit). The representative change is the composition
context: three topological spaces now reuse one setting interface instead of
copying its laws three times.

```litex
# Before:
# setting ContinuousCompositionSetting(A, B, CarrierC set, T_A ..., T_B ..., T_C ..., f ..., g ...):
#     {} $in T_A
#     A $in T_A
#     # ...the topology laws repeated for A, B, and CarrierC...

setting ContinuousCompositionSetting([TopologicalSpaceSetting(A, open_sets_A)], [TopologicalSpaceSetting(B, open_sets_B)], [TopologicalSpaceSetting(CarrierC, open_sets_C)], f fn(x A) B, g fn(y B) CarrierC):
    forall open_B open_sets_B:
        {x A: f(x) $in open_B} $in open_sets_A
    forall open_C open_sets_C:
        {y B: g(y) $in open_C} $in open_sets_B
```

The same source setting now defines the concrete predicates:

```litex
prop is_topology_on([TopologicalSpaceSetting])

prop is_continuous([TopologicalSpaceSetting(X, open_sets_X)], [TopologicalSpaceSetting(Y, open_sets_Y)], f fn(x X) Y):
    forall open_Y open_sets_Y:
        {x X: f(x) $in open_Y} $in open_sets_X
```

Boundary: this migration only consumes the existing setting-bundle syntax; it
does not add parser behavior or turn settings into constructed topology
objects.

Evidence:

```text
target/release/litex -compact -runner -f showcases/math_concepts_in_litex/topology/main.lit
```
