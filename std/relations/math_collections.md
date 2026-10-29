# Equivalence classes, partitions and ordered sets

An equivalence relation supplies an actual carrier and a set of ordered pairs
inside its square. `EquivalenceRelation<Ambient>` packages those data with
reflexivity, symmetry and transitivity as direct laws. The ambient set only
bounds the actual carrier; empty carriers are permitted. A Boolean-valued
function would encode an extra logical representation without owning the
ordinary relation-as-a-subset interface.

The class of x is the actual subset of related elements. A template-indexed
complete function `equivalence_class(x)` returns it; the quotient is the image
of this class map. No representative is selected. The checked main results
are self-membership/nonemptiness, equality of related classes, the equal-or-
disjoint dichotomy, and that all classes form a partition. A partition is an
independent relation on a supplied family: nonempty blocks, full union and
pairwise equal-or-disjoint blocks. The empty family partitions the empty set.

A partial order supplies a carrier and a reflexive/transitive/antisymmetric
pair relation. Least/greatest and minimal/maximal elements are properties of
supplied points of supplied subsets; membership in the subset belongs to the
property. A least element is unique and minimal, whereas a minimal element
need not be least. Monotone maps preserve ordered pairs; composition uses the
native function composition value.

Dependency order: sets and ordered pairs -> bundled relation laws -> class
map -> related classes and disjointness -> quotient family -> partition;
separately ordered-pair laws -> subset extrema -> uniqueness and monotone maps.
These are signature, definition, well-definedness and proof edges. Empty
carriers introduce no arbitrary element or choice dependency. The interfaces above are materialized in main.lit. The README records the
strict source and imported-consumer evidence and the unsupported boundaries.
