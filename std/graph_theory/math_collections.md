# Finite simple graphs and degree arguments

## Data and domains

A graph is a symmetric, irreflexive adjacency relation on an actual finite
set V. `FiniteSimpleGraph<V>` stores `(V,arcs)`. Its first field is required
to equal V, and its second field is a subset of V times V. The actual carrier
is fixed in the graph's type, so complement keeps the same carrier while an
induced subgraph changes its type to the chosen subset U. Empty carriers are
legitimate.

An undirected edge has both ordered adjacency pairs in arcs. Degree counts
distinct neighbors. It does not count arcs twice at a vertex, and no claim
about an undirected edge cardinality or the handshaking identity is made here.

## Neighborhoods, extremal degrees and isolation

For v in V, its neighborhood is the actual set builder of adjacent vertices.
It is a subset of the finite carrier and hence finite. Irreflexivity excludes
v, so this neighborhood lies in V minus `{v}`. Finite cardinality and removal
of one point give degree(v) at most size(V)-1, equivalently below size(V).

Degree zero is equivalent, through two separate implication theorems, to
isolation. Finite cardinality zero gives an empty neighborhood. Conversely,
absence of every adjacency makes the neighborhood empty. At maximal degree,
the neighborhood and V minus `{v}` have the same cardinality; finite subset
equality gives every other vertex as a neighbor.

If the graph has at least two vertices and z is isolated, every degree is at
most size(V)-2. For v=z this is degree zero. For a distinct v, degree size(V)-1
would make z its neighbor. Symmetry would then give an edge from z, contrary
to isolation. Integrality converts the strict exclusion of the maximum into
the stated one-step smaller bound.

## Equal degrees from the existing pigeonhole theorem

Let n=size(V), n at least 2. Split by whether an isolated vertex exists.

- If one exists, every degree lies in the n-1 element set `[0,n-2]`.
- If none exists, every degree lies in the n-1 element set `[1,n-1]`.

In each case define the actual degree-label function into that interval.
The source imports the existing finite pigeonhole collision theorem from
combinatorics. Since V has n elements, it gives distinct v,w with equal labels,
and unfolding the labels gives equal degrees. No ordering of the vertices,
numbering of the graph, or extremum selector is assumed. Empty and singleton
graphs are outside this theorem's size hypothesis while remaining valid graph
objects.

## Actual constructions and their degree formulas

The edgeless graph uses the empty adjacency set. The complete graph uses all
pairs with unequal coordinates. Their graph laws are checked directly; their
neighborhoods give degree zero and size(V)-1, respectively.

Complement uses all unequal-coordinate pairs absent from the original arcs.
Symmetry follows by contradiction from the original relation's symmetry.
Its neighborhood is exactly

    set_minus(set_minus(V,{v}),graph_neighbors(v)).

The original neighborhood is a subset of V minus `{v}`. Finite set-difference
cardinality therefore gives

    degree_G(v)+degree_complement(v)=size(V)-1.

For U a subset of V, induced adjacency is `intersect(G.arcs,cart(U,U))`.
It inherits irreflexivity and symmetry. Its neighborhood at v in U is exactly
the original neighborhood intersected with U, so finite subset monotonicity
shows that restriction cannot increase degree. The empty subset is allowed.

The constructor values, their graph-law certificates and the two degree
functions are actual source objects. In imported generic goals, the consumer
proves the constructor memberships explicitly before nesting constructor
values in degree expressions. The standalone README example builds a typed
raw pair from a construction theorem and verifies independently.

## Source proof and acceptance evidence

The dependency spine is finite sets and relation laws -> actual neighborhoods
and finite cardinality -> degree bounds/isolation/maximal neighborhoods ->
two pigeonhole branches and equal-degree vertices. In parallel, actual
complete/complement/induced adjacency sets -> graph-law certificates ->
neighborhood formulas -> degree identities and monotonicity.

The canonical source contains 21 theorems in 36 statements. The public checker
passes those statements, 96 imported consumer statements, a fresh five-statement
README example, and ten final-only refusals. The concrete path on `{1,2,3}`
has neighborhoods `{2}`, `{1,3}`, `{2}` and degrees 1,2,1. Its complement has
center degree 0 and endpoint degree 1. Its induced graph on `{1,3}` has no
neighbors. Empty, singleton and empty-induced examples verify too.

All proofs and data live under std. No trust declaration, axiom, parser,
verifier, compiler or other std-external change is part of this batch. Paths,
connectedness, unordered edge counting/handshaking, trees, coloring and graph
isomorphism require further source mathematics and are not inferred here.
