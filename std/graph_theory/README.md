# Finite simple graph theory

This source module contains 34 named theorems in 60 strict statements. It
supplies finite simple undirected graphs, neighborhoods, degrees, four graph
constructions, equal-degree vertices, actual unordered edge sets and the
handshake theorem. It adds no axioms, trust blocks or native rules.

## Import and first use

Add this to the caller's `litex.config`, with its own `[export]` table:

```ini
[import std]
GraphTheory = graph_theory
[alias]
graph = GraphTheory::main
```

This complete example is [checked from an empty context](validation/readme.lit):

```litex
have demo_vertices finite_set={1,2,3}

release thm graph::edgeless_graph_construction(demo_vertices)

have demo &graph::FiniteSimpleGraph<demo_vertices> = (demo_vertices,{})

finite_set_size(demo_vertices)=finite_set_size({1,2,3})=3

release thm graph::finite_simple_graph_has_equal_degrees(demo_vertices,demo)
```

The final theorem supplies two distinct vertices with equal degrees. Its
hypothesis is at least two vertices; it is not available on a singleton.

## Exact graph contract

`FiniteSimpleGraph<V>` takes the actual finite vertex set V as a type parameter.
Its value is a pair `(V,arcs)` with fields `vertices` and `arcs`. The definition
requires `vertices=V`, `arcs` a subset of V times V, no pair `(v,v)` in arcs,
and symmetry: `(v,w)` in arcs implies `(w,v)` in arcs.

Thus the graph has no loops, parallel edges or directions. The storage uses
ordered adjacency pairs: each undirected edge occurs as two opposite arcs.
The actual unordered edge set is now constructed as the image of the
arc-to-endpoint-set map. Its cardinality counts edges once; it is not defined
as half the arc count.
A smaller first field is invalid even if it is a subset of V. Empty and
singleton vertex sets are allowed. Infinite V is outside this graph type.

The callable operations are templates:

- `\graph_neighbors<V,G>(v)` is `{w V:(v,w) in G.arcs}`.
- `\graph_degree<V,G>(v)` is the natural cardinality of that neighborhood.
- `\graph_arc_source<V,G>(arc)` is the source-coordinate map on G.arcs.
- `\graph_arc_to_vertex_set<V,G>(arc)` returns the union of singleton endpoints.
- `\graph_edges<V,G>` is the actual image of that map, a finite set of
  two-element subsets of V. Both orientations have the same image.
- `$is_isolated_vertex(V,G,v)` means no w in V is adjacent to v.
- `$has_isolated_vertex(V,G)` means such a vertex exists.

All require a checked `G &FiniteSimpleGraph<V>` and, where present, v in V
or arc in G.arcs. Endpoints in V alone do not make an input arc valid.
Use the module prefix inside a template call, for example
`\graph::graph_degree<V,G>(v)`.

## Constructions

| Template value | Actual vertex set and adjacency |
| --- | --- |
| `\edgeless_graph<V>` | V, with no arcs |
| `\complete_graph<V>` | V, with all ordered pairs of distinct vertices |
| `\complement_graph<V,G>` | V, with distinct pairs absent from G.arcs |
| `\induced_graph<V,G,U>` | U subset V, with arcs `intersect(G.arcs,cart(U,U))` |

The induced graph has type `FiniteSimpleGraph<U>`. Complement retains type
`FiniteSimpleGraph<V>`. `complete_graph_arcs` and `complement_graph_arcs` expose
the actual adjacency sets used in their values.

The four `*_graph_construction` theorems prove membership for the displayed
raw pairs. The [generic consumer](validation/main.lit) also explicitly proves
the imported template values' graph memberships before nesting those values
in generic degree goals. These are checked constructor certificates, not
assumptions about a supplied adjacency relation.

## Main results

Use the prefix `graph::` for theorem names. V is finite, G has graph type over
V, and v,w,z are in V unless the row specifies U.

| Theorem | Result |
| --- | --- |
| `graph_neighbors_are_finite(V,G,v)` | The neighborhood is finite |
| `vertex_is_not_its_neighbor(V,G,v)` | No vertex belongs to its own neighborhood |
| `adjacent_vertex_is_neighbor(V,G,v,w)` | An arc gives both neighborhood memberships |
| `graph_neighbors_exclude_vertex(V,G,v)` | The neighborhood is a subset of V minus `{v}` |
| `graph_degree_upper_bound(V,G,v)` | Degree is strictly below the size of V |
| `zero_degree_has_no_neighbors(V,G,v)` | Degree zero implies the isolated-vertex predicate |
| `no_neighbors_has_zero_degree(V,G,v)` | An isolated vertex has degree zero |
| `maximal_degree_has_all_neighbors(V,G,v)` | Degree size(V)-1 forces the full neighborhood V minus `{v}` |
| `isolated_vertex_bounds_all_degrees(V,G,z,v)` | At least two vertices and isolated z imply degree(v) at most size(V)-2 |
| `finite_simple_graph_has_equal_degrees(V,G)` | At least two vertices imply distinct v,w with equal degrees |
| `edgeless_graph_construction(V)` | `(V,{})` is a graph over V |
| `complete_graph_construction(V)` | The complete adjacency set gives a graph over V |
| `complement_graph_construction(V,G)` | The complement adjacency set gives a graph over V |
| `induced_graph_construction(V,G,U)` | Restriction to U gives a graph over U |
| `edgeless_graph_degree(V,v)` | Degree in the edgeless graph is zero |
| `complete_graph_neighbors(V,v)` | The complete neighborhood is V minus `{v}` |
| `complete_graph_degree(V,v)` | Complete degree is size(V)-1 |
| `complement_graph_neighbors(V,G,v)` | The complement neighborhood is V minus `{v}` minus the original neighborhood |
| `complement_graph_degree_sum(V,G,v)` | Original and complement degrees sum to size(V)-1 |
| `induced_graph_neighbors(V,G,U,v)` | For v in U, the restricted neighborhood is the original neighborhood intersected with U |
| `induced_graph_degree_bound(V,G,U,v)` | For v in U, restriction cannot increase degree |

## Unordered edges and degree counting

The new results take the same V and G. An `edge` argument is an actual member
of `\graph_edges<V,G>`. No vertex ordering or representative selector is used.
The source-coordinate map is a restriction of the first-coordinate map on
cart(V,V); its fiber over v is in bijection with the actual neighborhood of v.
The arc-to-endpoint-set map has exactly two inputs per edge. The existing
finite-fiber counting theorems give the following results.

| Theorem | Contract |
| --- | --- |
| `graph_arcs_are_finite(V,G)` | The actual ordered adjacency set is finite. |
| `graph_arc_source_fiber_degree(V,G,v)` | The source-coordinate fiber has cardinality degree(v). |
| `graph_degree_sum_equals_arc_count(V,G)` | The sum of vertex degrees is size(G.arcs). |
| `graph_edges_are_finite(V,G)` | The actual unordered edge collection is finite. |
| `graph_edge_has_two_arcs(V,G,edge)` | Its preimage under the endpoint-set map has cardinality 2. |
| `graph_arc_count_twice_edge_count(V,G)` | size(G.arcs)=2*size(graph_edges). |
| `graph_handshake(V,G)` | The degree sum is 2*size(graph_edges). |
| `graph_edge_endpoints(V,G,edge)` | Supplies distinct u,v in V with (u,v) in G.arcs and edge=union({u},{v}). |
| `graph_edge_has_two_vertices(V,G,edge)` | The edge itself has cardinality 2. |
| `graph_edge_from_arc(V,G,u,v)` | An actual adjacency pair gives union({u},{v}) in the edge collection. |
| `graph_regular_edge_count(V,G,r)` | For natural r, degree(v)=r for every vertex implies r*size(V)=2*size(graph_edges). Empty V is allowed. |
| `graph_no_arcs_has_no_edges(V,G)` | Empty arcs imply the actual edge collection is empty. |
| `graph_no_edges_has_no_arcs(V,G)` | Empty edge collection implies empty arcs. |

Release the named finiteness results before using the corresponding cardinality
expressions in a caller. The generic contracts show how to establish preimage
and edge-element finiteness without adding hypotheses to the public theorems.
For constructed template values, expose the defining raw pair and its checked
graph membership before using it as G; the independent example below does so.

The three-vertex complete graph has three unordered edges and degree sum six.
This complete excerpt was checked independently before the requested test cleanup:

```litex
# A triangle has degree sum 6 and exactly 3 unordered edges.

have handshake_vertices finite_set={1,2,3}

finite_set_size(handshake_vertices)=finite_set_size({1,2,3})=3

release thm graph::complete_graph_construction(handshake_vertices)

\graph::complete_graph<handshake_vertices> = (handshake_vertices,\graph::complete_graph_arcs<handshake_vertices>)

\graph::complete_graph<handshake_vertices> $in &graph::FiniteSimpleGraph<handshake_vertices>

release thm graph::graph_edges_are_finite(handshake_vertices,\graph::complete_graph<handshake_vertices>)

claim:
    ? forall v handshake_vertices:
        \graph::graph_degree<handshake_vertices,\graph::complete_graph<handshake_vertices>>(v)=2
    release thm graph::complete_graph_degree(handshake_vertices,v)
    \graph::graph_degree<handshake_vertices,\graph::complete_graph<handshake_vertices>>(v)=finite_set_size(handshake_vertices)-1=3-1=2

release thm graph::graph_regular_edge_count(handshake_vertices,\graph::complete_graph<handshake_vertices>,2)

finite_set_size(\graph::graph_edges<handshake_vertices,\graph::complete_graph<handshake_vertices>>)=(2*finite_set_size(\graph::graph_edges<handshake_vertices,\graph::complete_graph<handshake_vertices>>))/2=(2*finite_set_size(handshake_vertices))/2=(2*3)/2=3

release thm graph::graph_handshake(handshake_vertices,\graph::complete_graph<handshake_vertices>)

finite_set_sum(handshake_vertices,fn(v handshake_vertices) N {\graph::graph_degree<handshake_vertices,\graph::complete_graph<handshake_vertices>>(v)})=2*finite_set_size(\graph::graph_edges<handshake_vertices,\graph::complete_graph<handshake_vertices>>)=2*3=6
```

Before cleanup, the extended caller also obtained actual path edges {1,2}
and {2,3}, verified both two-arc fibers, and checked the path's degree sum 4,
arc count 4 and edge count 2. Empty, singleton and empty-induced graphs have
no edges. A generic application proves that a nine-vertex graph has a vertex
whose degree differs from seven, following Levin's 4.1.7 example without
assuming that such a regular graph exists.

## Verification and remaining work

```bash
python3 std/graph_theory/validation/check.py
```

Before cleanup, the positive gates passed 60 strict source statements, 147 full imported
consumer statements, the independent five-statement original README example,
and the new eleven-statement handshake example. All 34 theorem contracts are
exercised. A fresh Session replays all 147 positive statements and confirms 28
final-only refusals at their intended phases. These are historical checkpoint
results. At the user's pause request, the round's 51 added caller statements,
18 added refusals, standalone handshake project, pending proof reproduction,
journals and pinned executable were removed. The original 96 caller
statements, five-statement example and ten refusals remain. The retained
checker covers those original fixtures and the 60-statement source; it no
longer covers the removed extension suites. No new verification run was
started during cleanup. No Cargo, Lean, installer or local textbook
certification is implied.

Refusals cover invalid graph data, outside endpoints, missing adjacency or
regularity hypotheses, confusing ordered arcs with unordered edges, wrong
fiber/edge sizes and empty-graph boundaries. The passing checker excludes the
unpublished proof follow-up described in [todo.md](todo.md). The degree-sum equation is
checked; an additional native `$dvd` convenience theorem is not published.
Odd-degree vertex parity is further mathematics, not inferred as a library
interface from the current equation alone.

Paths and connectedness, trees, cycles, colorings, graph isomorphisms, directed
graphs and multigraphs remain future work. This is not a complete graph course.
See [the mathematical spine](math_collections.md) for the proof dependencies.
