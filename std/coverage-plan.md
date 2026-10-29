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
batches add 76 named core-export theorems, bringing that source count to 868.
These are declaration counts, not independent course results or completeness.
Relations/order, metric-space and ring foundations, positive finite series
limit comparison, and positive square-root Newton iteration are now supplied.
Graph theory, complex analysis and differential equations still lack public
source spines. The numerical-analysis spine currently covers one method.

## Dependency order and target mathematics

| Lane | Present mathematical base | Next main content | Dependencies and honest boundary |
| --- | --- | --- | --- |
| Sets, relations and order | Native sets/functions, finite maps, equivalence classes/partitions, partial orders and monotone maps | Converse partition construction, quotient tools, total orders, lattices and suprema | Arbitrary carriers, empty cases; no arbitrary representative selector. |
| Metric spaces and elementary geometry | Bundled metrics, actual balls, separation, reverse triangle and Lipschitz/continuous maps | Metric sequence/Cauchy theory, completeness and generated topology | Domain/triangle laws belong to the structure; no unproved metric-to-topology bridge. |
| Abstract algebra | Groups, fields, unital rings, ideals, homomorphisms and kernels | Polynomial and quotient constructions; group actions/cosets | Do not assume all rings are commutative or exclude the zero ring silently. Quotient existence needs actual constructions. |
| Linear algebra | Linear maps, kernel/image, finite-dimensional rank-nullity, bases, dimension, coordinates and direct sums | Matrix representations, dual spaces and eigen/spectral theory | Preserve arbitrary fields and finite-dimensional hypotheses; rank-nullity already exists in linear_dimension.lit. |
| Elementary number theory | Congruences, Euclidean steps, supplied inverses | General Bezout, coprime inverse existence, linear Diophantine equations, CRT, prime factorization | Prove existence rather than taking the desired witness as an assumption. |
| Combinatorics and discrete mathematics | Cardinality, pigeonhole, binomial recursion | Factorial formula, binomial theorem/row sums, fiber counting; finite graphs, paths, degree and trees | Distinguish ordinary and directed/simple graph contracts; keep empty boundaries. |
| Probability and statistics | Finite spaces, moments, inequalities and pushforwards | Random-variable independence, distributions and expectation transfer; finite-sample statistics | Countable/measure probability requires its own foundations. |
| Real sequences and series | Cauchy/comparison/ratio/root/alternating tools | General real-p/integral tests; power/function series | Natural p>=2 does not cover every real p>1; convergence does not permit rearrangement. |
| Single-variable real analysis | Native limits, derivatives, Riemann rules | IVT, extreme value, Rolle/MVT, Taylor; standard applications and improper integration | Rebuild missing compactness/extrema dependencies; never promote trusted textbook statements as proofs. |
| General topology | Continuity, connectedness, separation, compactness | Subspace topology, closed subsets of compact spaces, compact-to-Hausdorff maps, products | Distinguish image topology from the original target; construct exact carriers. |
| Multivariable/vector calculus | Coordinates, directional/higher derivatives, ordered integrals | Differentiability/chain rule applications, extrema, Fubini prerequisites, line/surface integration | Existing ordered rectangular integrals do not establish order exchange or integral theorems. |
| Complex analysis, ODE and numerical analysis | Native complex/real primitives; positive square-root Newton updates, bounds and convergence | Complex polynomial/analytic foundations; elementary ODE solution contracts; other numerical methods and rounding/error analysis | Newton is one checked numerical method. Complex/ODE source lanes remain planned; no complete-course claim. |

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
- [x] Metric-space foundation: 13 source theorems; strict 19-declaration source and 33-statement imported consumers pass, including real-line/empty instances and L=0; six refusal controls reject. Completeness and metric-topology work remain.
- [x] Ring foundation: 27 source theorems; strict 33-declaration source, full std-imported 58-statement consumer and five focused source refusals pass. Noncommutative concrete-model proof debt is recorded in algebra/todo.md; quotients/polynomials remain.
- [x] Numerical first spine: 12 theorems / 17 strict source statements, 34 strict full-imported consumer statements and seven fresh-Session refusals pass. Covers the general positive square-root Newton iteration, error estimates and convergence; other numerical methods remain.
- [ ] Number-theory existence: general Bezout and coprime modular inverses, then CRT.
- [ ] Subsequent lane batches as the dependencies above become available.

## Integration boundary

The archive packaging helper excludes hidden local journals automatically.
Any Windows installer manifest update or other file change outside std must be
a separately authorized task. This plan does not authorize such changes.
