# Topology in Litex

These lecture notes develop elementary topology from a single question:
what makes a function continuous when no distance has been specified?
Two topologies on the set `{0, 1}` provide the running example. Their points
are identical, but their open sets give different answers about continuity.

Read [topology.lit](topology.lit) from beginning to end. The first chapter
constructs spaces and studies open and closed subsets. The second develops
preimages, continuity and homeomorphisms. In Litex, the same subsets and
functions used in the examples become arguments to the general definitions
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
another. The final example swaps the two points of the discrete space:
`swap(0) = 1` and `swap(1) = 0`. Applying the swap twice returns the original
point, and the notes verify that it is a homeomorphism.

## Reading guide

| Sections | Mathematical progression |
|---|---|
| 1.1–1.2 | Subsets; topology axioms; discrete and indiscrete spaces; arbitrary unions |
| 1.3 | Relative complements; closed sets; open-and-closed examples; triple intersections |
| 2.1–2.2 | Identity and composite preimages; continuous maps; continuous composition |
| 2.3 | Complement preimages; the closed-preimage characterization in both directions |
| 2.4 | A continuous bijection with discontinuous inverse; homeomorphisms; the two-point swap |

These are original, selected lectures, not a textbook translation or a
complete topology course. Compactness, connectedness, separation axioms,
metric spaces and algebraic topology are outside this development. For a
separate checked slice reaching compact images, see the existing
[topology concepts showcase](../math_concepts_in_litex/9_topology/README.md).

The complete lecture passes strict Litex verification and contains no user
`trust`, `axiom` or `abstract_prop`. Verification uses Litex's own verifier
and builtin mathematical rules; no Lean certification is claimed.

[math_collections.md](math_collections.md) explains the interface choices
and dependencies. [litex.config](litex.config) exports the lecture as
`topology`. For command-line usage, see the [CLI documentation](../../docs/cli.md).
