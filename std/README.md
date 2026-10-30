# Litex standard mathematics library

The standard library contains reusable mathematical definitions, constructions
and checked source theorems. Native operations remain available without an
import; these modules supply reusable source mathematics above them.

## Current modules

| Subject | Modules and current source scope |
| --- | --- |
| Sets, relations and order | [relations](relations/README.md): equivalence classes and partitions, partial orders, subset extrema, monotone maps and order embeddings. |
| Abstract algebra and linear algebra | [algebra](algebra/README.md): groups, unital rings/ideals/homomorphisms, fields, vector spaces, linear maps, kernel/image, finite-dimensional rank-nullity, finite spans, independence, bases, exchange, basis extension, dimension, coordinate maps, direct sums and subspace sums. |
| Elementary real algebra | [real_quadratics](real_quadratics/README.md): actual quadratic solution sets, discriminant and degenerate classification, Vieta/converse, factorization, sign-dependent root order and attained extrema. |
| Real and complex matrices | [matrix](matrix/README.md): finite matrix relations and entrywise laws above native matrix operations. |
| Finite graph theory | [graph_theory](graph_theory/README.md): simple undirected graphs, neighborhoods, degrees, complement/induced constructions, actual unordered edges, handshaking, regular-graph edge counts and equal-degree vertices. Paths, trees and odd-degree subset parity remain. |
| Number theory | [number_theory](number_theory/README.md): divisibility, congruence, general Bezout existence, coprime modular inverses, integer-equation solvability and the two-modulus CRT with a canonical natural residue. |
| Finite combinatorics | [combinatorics](combinatorics/README.md): finite maps, cardinality, inclusion-exclusion, binomial coefficients/expansion and finite fiber counting, with checked full-domain imported callers and refusal boundaries. Subset counting and Vandermonde remain. |
| Finite probability | [probability](probability/README.md): bundled finite spaces, conditioning, Bayes, moments, variance, covariance, correlation, tail inequalities and pushforward spaces. |
| Metric spaces and sequences | [metric](metric/README.md): bundled distances, balls, separation and Lipschitz/continuous maps; [metric_sequences](metric_sequences/README.md): limits, Cauchy, real-line completeness, actual iterates, Banach unique fixed points, convergence and error bounds. |
| General topology | [topology](topology/README.md): open-set spaces, continuity, homeomorphisms, connectedness, separation, compactness, actual subspaces and compact-to-Hausdorff continuous inverse existence. |
| Ordered real series | [real_series](real_series/README.md): partial sums, convergence, Cauchy, comparison, geometric and telescoping sums, ratio/root and alternating tests with remainder estimates. |
| Numerical analysis | [numerical_analysis](numerical_analysis/README.md): general positive square-root Newton updates, exact identities, iterate error bounds and convergence for any positive seed. |
| Real integration | [real_integral_laws](real_integral_laws/README.md): absolute-integral and integral-difference bounds, with exact orientation and integrability hypotheses. |
| Multivariable analysis | [real_multivariable](real_multivariable/README.md): coordinate paths, local scalar/vector relations, directional and higher derivatives, cross products and ordered rectangular iterated integrals. |
| Regularity and higher derivatives | [real_regularity](real_regularity/README.md), [real_regularity_laws](real_regularity_laws/README.md), [real_higher_order_laws](real_higher_order_laws/README.md). |
| Finite function sums | [real_function_sums](real_function_sums/README.md) and [real_scalar_function_sums](real_scalar_function_sums/README.md): finite combinations and the corresponding analysis laws. |
| Compatibility | [basics](basics/README.md) exports no declarations; use native vocabulary directly. |

A module's presence does not imply that a complete course is covered. Its
README states the implemented interface and boundaries; `math_collections.md`
explains the mathematical dependency spine. The [coverage plan](coverage-plan.md)
separates present source, planned mathematics and blocked obligations.
The [secondary and undergraduate curriculum map](curriculum-map.md) records
the full planned subject scope, chapter clusters and the evidence needed to
claim coverage. Planned subjects do not imply implemented public modules.
The [chapter specifications](chapter-specifications.md) expand 21
clusters into precise mathematical obligations and distinguish reusable std,
native and showcase material from work still to implement.

## Use and verification

Import a module through a project's `litex.config` `[import std]` table. Follow
that module's explicit definition-release and theorem-call contract; imported
ambient facts do not automatically become caller facts.

All source changes for the coverage task are confined to `std/`. Module-owned
validation projects also live here. Local Session journals are kept under
`.verification/`, ignored by Git and excluded by the std packaging helper.
No kernel change, new trust, or extra unproved assumption is used to make a
library theorem pass.
