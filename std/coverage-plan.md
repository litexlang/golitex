# Mathematics coverage plan

Status: active, 2026-10-29. This is the continuing standard-library work plan,
not a declaration that undergraduate mathematics is already covered.

## Goal and evidence

Expand the major branches through reusable definitions, actual constructions,
core theorems and representative callers. A collection of names, definitions
alone, native capability names, or specialized examples is insufficient.
Retain exact domains, meaningful hypotheses and explicit unsupported boundaries.
All task-authored file changes are confined to `std/`, including journals and
validation. Read other source only for reference. Do not repair the verifier,
compiler, examples, tests, documentation or installers outside this directory.

Baseline: 15 directories and 792 named source theorems. The completed first
batches add 165 named core-export theorems, bringing that source count to 957.
These are declaration counts, not independent course results or completeness.
Relations/order, metric-space and ring foundations, positive finite series
limit comparison, and positive square-root Newton iteration are now supplied.
Metric sequences, real-line completeness and the Banach contraction theorem
now have a separate source spine. Finite simple graph theory has a source spine; complex analysis and
differential equations still lack public source spines. The numerical-analysis
spine covers positive square-root Newton iteration; metric_sequences also
supplies general contractive fixed-point iteration, convergence and error bounds.

## Dependency order and target mathematics

| Lane | Present mathematical base | Next main content | Dependencies and honest boundary |
| --- | --- | --- | --- |
| Sets, relations and order | Native sets/functions, finite maps, equivalence classes/partitions, partial orders and monotone maps | Converse partition construction, quotient tools, total orders, lattices and suprema | Arbitrary carriers, empty cases; no arbitrary representative selector. |
| Metric spaces and elementary geometry | Bundled metrics/balls/maps; metric limits and Cauchy; real-line completeness; actual contraction iterates, Banach unique fixed points, convergence and error bounds | Closed-subspace completeness, product metrics, generated topology and sequential compactness | Empty carriers are allowed; fixed-point existence needs nonemptiness; no unproved metric-to-topology bridge. |
| Abstract algebra | Groups, fields, unital rings, ideals, homomorphisms and kernels | Polynomial and quotient constructions; group actions/cosets | Do not assume all rings are commutative or exclude the zero ring silently. Quotient existence needs actual constructions. |
| Linear algebra | Linear maps, kernel/image, finite-dimensional rank-nullity, bases, dimension, coordinates and direct sums | Matrix representations, dual spaces and eigen/spectral theory | Preserve arbitrary fields and finite-dimensional hypotheses; rank-nullity already exists in linear_dimension.lit. |
| Elementary number theory | Congruences, Euclidean steps, general Bezout, coprime inverse existence, Diophantine solvability and two-modulus CRT | General noncoprime/finite-system CRT, prime factorization and quotient arithmetic | Prove existence rather than taking the desired witness as an assumption. |
| Combinatorics and discrete mathematics | Cardinality, pigeonhole, binomial recursion; finite simple graphs, neighborhoods, degrees, complement/induced graphs and equal-degree vertices | Factorial formula, binomial theorem/row sums, fiber counting; graph paths, handshaking and trees | Distinguish ordinary and directed/simple graph contracts; keep empty boundaries. |
| Probability and statistics | Finite spaces, moments, inequalities and pushforwards | Random-variable independence, distributions and expectation transfer; finite-sample statistics | Countable/measure probability requires its own foundations. |
| Real sequences and series | Cauchy/comparison/ratio/root/alternating tools | General real-p/integral tests; power/function series | Natural p>=2 does not cover every real p>1; convergence does not permit rearrangement. |
| Single-variable real analysis | Native limits, derivatives, Riemann rules | IVT, extreme value, Rolle/MVT, Taylor; standard applications and improper integration | Rebuild missing compactness/extrema dependencies; never promote trusted textbook statements as proofs. |
| General topology | Continuity, connectedness, separation, compactness, actual subspaces, closed compact subsets/maps and compact-to-Hausdorff continuous inverse existence | Product and quotient topology, generated metric topology and path foundations | Distinguish image topology from the original target; construct exact carriers. |
| Multivariable/vector calculus | Coordinates, directional/higher derivatives, ordered integrals | Differentiability/chain rule applications, extrema, Fubini prerequisites, line/surface integration | Existing ordered rectangular integrals do not establish order exchange or integral theorems. |
| Complex analysis, ODE and numerical analysis | Native complex/real primitives; positive square-root Newton iteration and general contractive fixed-point iteration with bounds/convergence | Complex polynomial/analytic foundations; elementary ODE solution contracts; other numerical methods and rounding/error analysis | The current iteration results do not constitute a numerical-analysis course. Complex/ODE source lanes remain planned. |

Foundation dependency spine: sets/functions -> relations/order and algebraic
structures -> maps/constructions -> finite-dimensional/metric/topological tools
-> analysis/probability/geometry -> advanced applications. Edges are definition,
well-definedness, existence, uniqueness or proof dependencies; crossing a source
module also creates an import dependency. Source-order deviations follow this
mathematical order rather than target-specific proof convenience.

## Execution protocol

1. Close the already accepted series limit-comparison batch; add public source
   and real imported callers under std, with false/missing-premise controls.
2. Build relations/order and metric-space foundations, then ring foundations.
   Choose one concrete consumer per batch before proof work.
3. Continue the lanes above according to their actual dependencies, prioritizing
   missing core results across branches rather than adding isolated trivia.
4. Use one persistent Session per context, one statement at a time. Retain the
   process after ordinary failure and journal accepted source and rejection
   evidence under `.verification/`. Materialize coherent accepted batches only.
5. At each batch, run a clean strict file and actual caller; require exit 0,
   Normal `kind=run`, `run_result=success`, empty errors,
   `session_terminated=false`, `termination=null`. Verify false claims and
   missing premises fail at the intended final statement.
6. Update the owning README and mathematical manual. Record an exact blocker
   here when it prevents a main result, then continue independent mathematics.

## Progress

- [x] Positive finite limit comparison: 3 source theorems added (103 total); strict 116-statement source and std-owned imported consumers pass; missing limit, missing denominator positivity and zero-limit final-premise controls reject.
- [x] Relations/order foundation: 21 source theorems; strict 33-declaration source and 43-statement imported consumers pass; four mathematical/domain refusal controls reject. Further order and quotient work remains.
- [x] Metric-space foundation: 13 source theorems; strict 19-declaration source and 33-statement imported consumers pass, including real-line/empty instances and L=0; six refusal controls reject. Its imports and source remain unchanged; the later completeness/iteration lane is a separate module. Metric-topology work remains.
- [x] Ring foundation: 27 source theorems; strict 33-declaration source, full std-imported 58-statement consumer and five focused source refusals pass. Noncommutative concrete-model proof debt is recorded in algebra/todo.md; quotients/polynomials remain.
- [x] Numerical first spine: 12 theorems / 17 strict source statements, 34 strict full-imported consumer statements and seven fresh-Session refusals pass. Covers the general positive square-root Newton iteration, error estimates and convergence; other numerical methods remain.
- [x] Number-theory existence: 12 theorems added (37 total) and a proved unique-residue function; 40 strict source statements, 58 full imported statements and 11 fresh-Session refusals pass. Covers general Bezout, coprime modular inverses, Diophantine solvability and the two-modulus coprime CRT, including unit moduli.
- [x] Finite simple graphs: 21 theorems / 36 strict source statements, 96 full imported statements, an independent five-statement README example and ten fresh-Session refusals pass. Degree bounds, isolation, equal-degree vertices and complete/complement/induced constructions are supplied; paths, trees and handshaking remain.
- [x] Topology extension: 26 theorems added (73 total) / 102 strict source statements, 123 full imported statements and 12 fresh-Session refusals pass. Includes compact-to-Hausdorff continuous inverse existence, actual subspaces and both compactness directions, including empty spaces and arbitrary cover indices.
- [x] Metric sequence and contraction spine: 30 theorems / 45 strict source statements and 106 full imported statements pass; all theorem signatures have generic callers. Covers real-line completeness, actual N-indexed iterates, Banach unique fixed points, canonical point values, orbit convergence and residual/a priori/a posteriori bounds. The affine map has fixed point 2 and iterates 1, 3/2, 7/4; zero factors, empty complete spaces with no fixed point and the 1-Lipschitz noncontraction are checked. Twelve fresh-Session final-only refusals cover missing premises and exact domains. Closed-subspace/product/metric-topology work remains.
- [ ] Subsequent lane batches as the dependencies above become available.

## Integration boundary

The archive packaging helper excludes hidden local journals automatically.
Any Windows installer manifest update or other file change outside std must be
a separately authorized task. This plan does not authorize such changes.
