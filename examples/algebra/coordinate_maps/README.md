# Coordinate maps and finite-dimensional isomorphism existence

main.lit reuses the standard real plane and the preceding coordinate swap.
Prescribing both basis images as e1 constructs a linear, noninjective map and
checks (3,4)->(7,0). Prescribing the swapped basis constructs a linear
bijection, checks (3,4)->(4,3), its selected inverse at(4,3)=(3,4), and equality
with the reversed basis construction. A local witness is then obtained from
the general equal-finite-dimension existence theorem.

contracts.lit consumes all17 named source theorems, including both value
carriers. Its arbitrary-image construction and linearity interfaces require
only the source basis, with no target basis or target finite-dimension premise.
boundaries/main.lit uses an inherited zero subspace over the same field. Empty
images map its zero vector into the plane, without surjectivity. Two empty
bases give a bijection. It proves no linear bijection can exist from dimension0
to dimension2. isomorphism/main.lit is the complete isolated README consumer
for general existence.

Run from the repository root:

```sh
python3 examples/algebra/coordinate_maps/check.py --binary /path/to/litex
```

The twenty independent negative configurations cover missing basis/linearity/
agreement/dimension evidence, exact list lengths, illegal unit indices, wrong
values, distinct map instances and undefined inverses. Each rejects only its
final statement. Some test unproved interface obligations, not the logical
negation of the rejected statement.

The checker exercises actual copied binary/std installation layouts without
LITEX_STD_PATH and compares the complete std/WiX payload. Unrelated packaged
modules are not mathematically certified by these algebra checks.

The existing swap fixture adds one named two-fact export while preserving its
49-statement prefix. Source-file local names are retained so it can be
imported under a different alias. No Rust or native mathematical change is
needed. One draft trust was discharged; maintained mathematics is strict and
trust-free. Direct sums and matrix representation are future work.
