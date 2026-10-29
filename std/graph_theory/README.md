# Finite simple graph theory

This source module contains 21 named theorems in 36 strict statements. It
supplies finite simple undirected graphs, neighborhoods, degrees, four actual
graph constructions, the complement degree identity, and the equal-degree
vertex theorem. It adds no axioms, trust blocks or native rules.

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
There is no edge-count operation or handshaking theorem in this batch.
A smaller first field is invalid even if it is a subset of V. Empty and
singleton vertex sets are allowed. Infinite V is outside this graph type.

The callable operations are templates:

- `\graph_neighbors<V,G>(v)` is `{w V:(v,w) in G.arcs}`.
- `\graph_degree<V,G>(v)` is the natural cardinality of that neighborhood.
- `$is_isolated_vertex(V,G,v)` means no w in V is adjacent to v.
- `$has_isolated_vertex(V,G)` means such a vertex exists.

All require a checked `G &FiniteSimpleGraph<V>` and, where present, v in V.
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

## Verification and remaining work

```bash
python3 std/graph_theory/validation/check.py
```

The checker verifies 36 strict source statements, 96 full imported consumer
statements, the independent five-statement README example, and ten final-only
refusals in a fresh persistent strict Session. The consumer includes full-domain
calls for all 21 theorems; the actual path 1--2--3 with degrees 1,2,1; its complement;
its induced graph on endpoints; complete and edgeless graphs; empty and singleton
carriers; and empty induced graphs.

Refusals cover a loop, a single directed arc, an outside endpoint, incorrect
vertex metadata, an infinite vertex set, a singleton equal-degree call, a self
neighbor, an outside degree argument, an excessive degree and an edge retained
in the complement of a complete graph. Every refusal has an accepted prefix.

Paths and connectedness, unordered edge objects and handshaking, trees, cycles,
colorings, graph isomorphisms, directed graphs and multigraphs remain future
work. The current results do not constitute a complete graph-theory course.
See [the mathematical spine](math_collections.md) for the proof dependencies.
