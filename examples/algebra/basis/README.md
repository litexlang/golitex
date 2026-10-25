# Shared independence, bases and coordinates

Run the focused gate from the repository root after a release build:

```bash
python3 examples/algebra/basis/check.py
```

[main.lit](main.lit) constructs the real scalar line and proves that the one-entry
unit list is independent and spanning. It calls the shared arbitrary-finite
representation theorem and guarded coordinate selector, then computes:

<!-- litex:skip-test -->
```litex
\Algebra::basis::basis_coordinates<R,real_field,R,scalars,1,unit_basis>(7)(1)=7
```

This excerpt uses the preceding instance, basis proof and coordinate-list
bridges in the actual file. Before this increment the general basis interfaces
were lecture-local and the explicit coordinate theorem was plane-specific.
The new coefficient uniqueness proof applies to any finite n, not just this
one-entry demonstration.

[zero_dimensional/main.lit](zero_dimensional/main.lit) proves that the empty list
is a basis of the singleton zero space and its coordinates are empty.
[contracts.lit](contracts.lit) checks all twelve imported theorem signatures
under their exact generic hypotheses; these are API checks, not twelve additional
mathematical results. The migrated [plane lecture](../../../showcases/linear_algebra/README.md)
continues to verify its concrete basis, dependence and coordinate developments.

Every negative passes its valid prefix and rejects only its last statement:

| Control | Boundary |
| --- | --- |
| no_basis_guard | Repeated directions cannot supply the required basis proof |
| empty_not_basis | The empty list is not a basis of the real scalar line |
| wrong_coordinate | The computed coordinate 7 cannot be changed to 8 |
| index_out_of_range | A one-entry coordinate list has no second coordinate |
| missing_representation | Coordinate uniqueness needs actual representation of the supplied vector |
| missing_independence | Equal combination values do not imply equal coefficients for dependent lists |
| removed_index_out_of_range | Removing entry 3 from a two-entry list fails its bound premise |

The checker also verifies the full migrated lecture, actual archive/shared-data
std layouts and complete source/WiX payload equality. No source trust, native
rule, arity/type overload or dimension selector is introduced. General basis
existence/exchange and length invariance remain future work. Exact interfaces
are documented in [std/algebra](../../../std/algebra/README.md) and their proof
roles in [math_collections.md](math_collections.md).
