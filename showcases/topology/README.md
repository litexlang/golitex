# Topology in Litex

These lecture notes develop elementary topology from a single question:
what makes a function continuous when no distance has been specified?
Two topologies on the set `{0, 1}` provide the running example. Their points
are identical, but their open sets give different answers about continuity
and connectedness.

Read [topology.lit](topology.lit) from beginning to end. The first chapter
constructs spaces and studies open and closed subsets. The second develops
preimages, continuity and homeomorphisms. The third introduces connectedness
and shows that continuous surjections preserve it. In Litex, the same subsets
and functions used in the examples become arguments to the general definitions
and theorems.

## From subsets to spaces

A discrete space declares every subset open. An indiscrete space declares
only the empty set and the whole space open. The notes verify both choices
against the topology axioms, including closure under arbitrary unions.

The following excerpt uses the two spaces constructed in Chapter 1:

<!-- litex:skip-test -->
```litex
{0} $in discrete.opens
not {0} $in indiscrete.opens
```

`TopologicalSpace<Ambient>` packages a carrier contained in `Ambient` and its
collection of open sets, together with the topology laws. Taking `Ambient`
to be the carrier itself allows any set, including the empty set. A closed
subset is defined by its open complement. Thus `{0}` is both open and closed
in the discrete two-point space, and neither in the indiscrete one.

## From preimages to continuity

Continuity says that the preimage of each open target set is open in the
source. The notes use Litex's native `preimage_set(f, U)` throughout. Two
set identities do the main work: preimages commute with composition, and
preimages commute with relative complements. They yield continuity of a
composite and both directions of the closed-preimage characterization.

The identity function makes the dependence on topology concrete. This
excerpt uses the `points`, `discrete`, `indiscrete` and `identity` declarations
from the notes:

<!-- litex:skip-test -->
```litex
$is_continuous(points, points, discrete, indiscrete, identity)
not $is_continuous(points, points, indiscrete, discrete, identity)
```

In the forward direction every possible preimage is open in the discrete
source. In the reverse direction the open target set `{0}` has preimage
`{0}`, which is not open in the indiscrete source. The function is bijective,
so this is also a counterexample to the claim that every continuous bijection
has a continuous inverse.

A homeomorphism requires both maps to be continuous and inverse to one
another. The Chapter 2 closing example swaps the two points of the discrete
space: `swap(0) = 1` and `swap(1) = 0`. Applying the swap twice returns the
original point, and the notes verify that it is a homeomorphism.

## From separations to connectedness

A space is connected when it cannot be written as the union of two nonempty
disjoint open sets. The same two-point carrier again supplies the contrast:
the indiscrete space is connected, while the discrete space is not. Clopen
sets detect the same distinction: connected spaces admit only the trivial
clopen sets, and the discrete singleton `{0}` is a nontrivial clopen set.

Continuous surjections preserve connectedness. Preimages turn a target
separation into a source separation, and surjectivity returns emptiness of
a preimage to emptiness of the target piece. This excerpt uses the Chapter 3
definitions and the running spaces:

<!-- litex:skip-test -->
```litex
$is_connected(points, indiscrete)
not $is_connected(points, discrete)
```

## Reading guide

| Sections | Mathematical progression |
|---|---|
| 1.1–1.2 | Subsets; topology axioms; discrete and indiscrete spaces; arbitrary unions |
| 1.3 | Relative complements; closed sets; open-and-closed examples; triple intersections |
| 2.1–2.2 | Identity and composite preimages; continuous maps; continuous composition |
| 2.3 | Complement preimages; the closed-preimage characterization in both directions |
| 2.4 | A continuous bijection with discontinuous inverse; homeomorphisms; the two-point swap |
| 3.1–3.3 | Connectedness; trivial-open spaces; discrete `{0,1}` disconnected, indiscrete connected |
| 3.4–3.5 | Preimage union and intersection; continuous surjections preserve connectedness |
| 3.6 | Clopen characterization in both directions; nontrivial clopen on the discrete space |

These are original, selected lectures, not a textbook translation or a
complete topology course. Compactness, separation axioms, subspace and product
topologies, metric spaces and algebraic topology are outside this development.
For a separate checked slice reaching compact images, see the existing
[topology concepts showcase](../math_concepts_in_litex/9_topology/README.md).

The complete lecture passes strict Litex verification and contains no user
`trust`, `axiom` or `abstract_prop`. Verification uses Litex's own verifier
and builtin mathematical rules; no Lean certification is claimed.

[math_collections.md](math_collections.md) explains the interface choices
and dependencies. [litex.config](litex.config) exports the lecture as
`topology`. For command-line usage, see the [CLI documentation](../../docs/cli.md).
