# General finite span reduction

The main consumer checks deletion of the middle, first and last vector from
(1,2,3), obtaining lists (1,3), (2,3) and (1,2) with the same span. It also
rechecks a nontrivial zero combination and obtains the general dependent-list
deletion witness. The real-field data come from ../dependence/main.lit through
the ordered context export; required mathematical facts are proved explicitly.
No producer's anonymous ambient fact is assumed to be imported.

contracts.lit checks all six new theorem interfaces over arbitrary supplied
fields and vector spaces. boundaries/main.lit independently uses the singleton
zero vector, removes it to the empty list, and checks empty-span minimality.
The actual list-domain bridges between lengths 3-1 and 2, or 1-1 and 0, are
explicit; no new coercion or default list is introduced.

Run python3 examples/algebra/span_reduction/check.py after a release build.
The checker covers strict producer/consumer sources, nine controls rejecting
only their final statement, archive/shared-data imports and std/WiX inventory
equality. Missing redundancy, removed-list relation, dependence, subspace,
value relation or generator coverage must reject. Empty removal length,
wrong remaining length and invalid indices must also reject.

The mathematical sources have no trust, axiom or abstract_prop. General basis
extraction, exchange, basis-length invariance and dimension are still open.
