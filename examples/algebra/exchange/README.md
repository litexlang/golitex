# Single-generator exchange

The real-plane model reuses the checked coordinate-field and vector-space
construction from the linear-algebra showcase. main.lit represents (1,1) by
coefficients (1,1) on (e1,e2), replaces e1 by (1,1), and proves equal spans by
the general imported exchange criterion. It also obtains an actual index and
replacement witness from the nonzero-member corollary.

contracts.lit calls all six exchange theorems over arbitrary supplied fields.
boundaries/main.lit permits a zero-valued singleton exchange with a nonzero
coefficient and checks empty-combination weighted closure. The replacement
relation requires k in closed_range(1,n), excluding empty and invalid updates.

Run python3 examples/algebra/exchange/check.py after a release build. Ten
controls reject only their final statement: concrete zero selected coefficient,
missing combination/replacement/subspace/weighted-coverage/nonzero-scalar/
nonzero-member hypotheses, index zero, index past the end and empty update.
The checker also verifies actual archive/shared-data imports and std/WiX equality.

No trust, axiom, abstract_prop, scalar ordering or selected replacement is
introduced. The later basis_comparison export uses finite repeated exchange
to prove length comparison and invariant finite basis length. Basis extension,
a dimension selector and general rank-nullity remain separate results.
