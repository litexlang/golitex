# Finite simple graphs and degree arguments

## Data and domains

A graph is a symmetric, irreflexive adjacency relation on an actual finite
set V. `FiniteSimpleGraph<V>` stores `(V,arcs)`. Its first field is required
to equal V, and its second field is a subset of V times V. The actual carrier
is fixed in the graph's type, so complement keeps the same carrier while an
induced subgraph changes its type to the chosen subset U. Empty carriers are
legitimate.

An undirected edge has both ordered adjacency pairs in arcs. Degree counts
distinct neighbors. The actual unordered-edge image and its two-arc fibers
now justify the handshaking identity; neither the graph data nor degree
definition has changed.

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

## Actual unordered edges and degree counting

The source route follows Levin, *Discrete Mathematics: An Open Introduction*,
third edition, [4.1, Lemma 4.1.5](https://discrete.openmathbooks.org/dmoi3/sec_gt-intro.html).
The 36-statement baseline is preserved exactly. The new 24 statements add
13 named theorems. Before the requested cleanup, clean source/imported gates
and all 28 final-only refusals passed, including a fresh replay of the 147
positive statements. The extension fixtures and temporary evidence were
subsequently removed; the mathematical source remains unchanged.

The actual source-coordinate map on arcs is the restriction of the first
coordinate map on cart(V,V). A fiber over v is in bijection with the actual
neighbor set of v; the existing finite-fiber theorem then gives the degree sum
as the size of G.arcs. Typed coordinate maps are applied to arc members after
explicitly proving their product membership; no WD or verifier change is used.

`graph_arc_to_vertex_set` similarly restricts the map sending (u,v) to the
union of its singleton endpoints. `graph_edges` is its actual image, a subset
of power_set(V). Symmetry and irreflexivity prove that each edge has exactly the two distinct
arcs (u,v) and (v,u). Uniform fiber counting then proves
size(G.arcs)=2*size(graph_edges) and the handshake identity.
The image and its proof, rather than a quotient count or an arbitrary vertex
ordering, own the unordered-edge construction. Empty graphs remain allowed.
A local corestriction into the actual image is constructed for the counting call;
it does not retype a larger-codomain function or assume a representative.

## Source proof and acceptance evidence

The dependency spine is finite sets and relation laws -> actual neighborhoods
and finite cardinality -> degree bounds/isolation/maximal neighborhoods ->
two pigeonhole branches and equal-degree vertices. In parallel, actual
complete/complement/induced adjacency sets -> graph-law certificates ->
neighborhood formulas -> degree identities and monotonicity.

The canonical source contains 34 theorems in 60 statements. Before cleanup, the positive gates
passed those statements, 147 imported consumer statements, the five-statement
original README example and an independent eleven-statement handshake example.
The final run confirmed 28 final-only refusals after replaying the 147 positives. The concrete path on `{1,2,3}`
has neighborhoods `{2}`, `{1,3}`, `{2}` and degrees 1,2,1. Its complement has
center degree 0 and endpoint degree 1. Its induced graph on `{1,3}` has no
neighbors. Empty, singleton and empty-induced examples verify too.

All proofs and data live under std. No trust declaration, axiom, parser,
verifier, compiler or other std-external change is part of this batch. Paths,
connectedness, trees, coloring and graph isomorphism require further source
mathematics and are not inferred here. The native-divisibility convenience
corollary has an unpublished source-proof follow-up in [todo.md](todo.md); no
trust or kernel repair was used to hide it.

At the user's pause request, this round's added caller cases, refusals,
handshake project, failed reproduction and temporary verification directory
were removed. The original 96-statement caller, five-statement example and
ten refusals remain; the retained checker only aligns the source count with
the 60 retained statements. No new verifier run was started during cleanup.
