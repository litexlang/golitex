# Topology in Litex

These lecture notes develop elementary topology from a single question:
what makes a function continuous when no distance has been specified?
Two topologies on the set `{0, 1}` provide the running example. Their points
are identical, but their open sets give different answers about continuity,
connectedness and separation. Later chapters add compactness, products, a
compact Hausdorff homeomorphism package, and the metric topology on `R`
with the intermediate value theorem.

Read [topology.lit](topology.lit) from beginning to end. In Litex, the same
subsets and functions used in the examples become arguments to the general
definitions and theorems.

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

## Separation, compactness, products and the real line

Chapter 4 defines T0, T1 and Hausdorff, proves the chain
Hausdorff ⇒ T1 ⇒ T0, and shows that T1 (hence Hausdorff) spaces have closed
singletons. The discrete two-point space is Hausdorff; the indiscrete one
fails even T0.

Chapter 5 defines indexed compactness and proves that continuous images of
compact sets are compact. Chapter 6 introduces open rectangles and
product-open sets, builds the discrete and indiscrete grids on
`cart({0,1},{0,1})`, and proves that a product of two spaces with only
trivial opens remains connected.

Chapter 7 packages the homeomorphism conclusion for a continuous bijection
that already has a continuous inverse, with the discrete two-point swap as
instance, and records that the discrete two-point space is a compact
Hausdorff space. The classical theorem “compact Hausdorff continuous
bijection ⇒ homeomorphism” is not proved in full generality here; the notes
keep the continuous-inverse hypothesis explicit.

Chapter 8 equips `R` with the metric topology, builds `real_line`, and proves
the intermediate value theorem for continuous real functions on a closed
interval by a least-upper-bound argument.

<!-- litex:skip-test -->
```litex
$is_Hausdorff(points, discrete)
not $is_T0(points, indiscrete)
by thm continuous_image_of_compact_is_compact(points, points, discrete, discrete, identity, {0})
    => $is_compact_subset(points, discrete, fn_range(\restricted<discrete.carrier, discrete.carrier, identity, {0}>))
$is_connected(grid, indiscrete_grid)
by thm continuous_bijection_with_continuous_inverse_is_homeomorphism(points, points, discrete, discrete, swap, swap)
    => $is_homeomorphism(points, points, discrete, discrete, swap, swap)
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
| 4.1–4.4 | T0 / T1 / Hausdorff; Hausdorff ⇒ T1 ⇒ T0; closed singletons; discrete vs indiscrete |
| 5.1–5.3 | Restrictions; compact subsets and spaces; continuous images of compact sets |
| 6.1–6.3 | Open rectangles; product opens; discrete / indiscrete grids; trivial-open products connected |
| 7.1–7.4 | Closed unions; two-point Hausdorff closed sets; continuous bijection with continuous inverse; compact discrete `{0,1}` |
| 8.1–8.3 | Metric opens on `R`; `real_line`; intermediate value theorem via least upper bounds |

These are original, selected lectures, not a textbook translation or a
complete topology course. Subspace topology, general product topology as a
constructed space, path connectedness, one-sided limits and algebraic topology
remain outside this development. For a separate checked slice that also
reaches compact images in a settings-first style, see
[topology concepts](../math_concepts_in_litex/9_topology/README.md).

The complete lecture passes strict Litex verification and contains no user
`trust`, `axiom` or `abstract_prop`. Verification uses Litex's own verifier
and builtin mathematical rules; no Lean certification is claimed.

[math_collections.md](math_collections.md) explains the interface choices
and dependencies. [litex.config](litex.config) exports the lecture as
`topology`. For command-line usage, see the [CLI documentation](../../docs/cli.md).
