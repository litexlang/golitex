# Litex standard mathematics library

The standard library contains reusable mathematical definitions, constructions
and checked source theorems. Native operations remain available without an
import; these modules supply reusable source mathematics above them.

## Current modules

| Subject | Modules and current source scope |
| --- | --- |
| Sets, relations and order | [relations](relations/README.md): equivalence classes and partitions, partial orders, subset extrema, monotone maps and order embeddings. |
| Abstract algebra and linear algebra | [algebra](algebra/README.md): groups, unital rings/ideals/homomorphisms, fields, vector spaces, linear maps, kernel/image, finite-dimensional rank-nullity, finite spans, independence, bases, exchange, basis extension, dimension, coordinate maps, direct sums and subspace sums. |
| Real and complex matrices | [matrix](matrix/README.md): finite matrix relations and entrywise laws above native matrix operations. |
| Number theory | [number_theory](number_theory/README.md): divisibility, congruence, Euclidean transformations, supplied Bezout witnesses and supplied modular inverses. General Bezout and CRT are not yet supplied. |
| Finite combinatorics | [combinatorics](combinatorics/README.md): finite maps, pigeonhole, cardinality, inclusion-exclusion and recursive natural binomial coefficients. |
| Finite probability | [probability](probability/README.md): bundled finite spaces, conditioning, Bayes, moments, variance, covariance, correlation, tail inequalities and pushforward spaces. |
| Metric spaces | [metric](metric/README.md): bundled distances, balls, reverse triangle and separation, Lipschitz maps and metric continuity; the standard real-line instance. |
| General topology | [topology](topology/README.md): open-set spaces, continuity, homeomorphisms, connectedness, separation and compactness. |
| Ordered real series | [real_series](real_series/README.md): partial sums, convergence, Cauchy, comparison, geometric and telescoping sums, ratio/root and alternating tests with remainder estimates. |
| Real integration | [real_integral_laws](real_integral_laws/README.md): absolute-integral and integral-difference bounds, with exact orientation and integrability hypotheses. |
| Multivariable analysis | [real_multivariable](real_multivariable/README.md): coordinate paths, local scalar/vector relations, directional and higher derivatives, cross products and ordered rectangular iterated integrals. |
| Regularity and higher derivatives | [real_regularity](real_regularity/README.md), [real_regularity_laws](real_regularity_laws/README.md), [real_higher_order_laws](real_higher_order_laws/README.md). |
| Finite function sums | [real_function_sums](real_function_sums/README.md) and [real_scalar_function_sums](real_scalar_function_sums/README.md): finite combinations and the corresponding analysis laws. |
| Compatibility | [basics](basics/README.md) exports no declarations; use native vocabulary directly. |

A module's presence does not imply that a complete course is covered. Its
README states the implemented interface and boundaries; `math_collections.md`
explains the mathematical dependency spine. The [coverage plan](coverage-plan.md)
separates present source, planned mathematics and blocked obligations.

## Use and verification

Import a module through a project's `litex.config` `[import std]` table. Follow
that module's explicit definition-release and theorem-call contract; imported
ambient facts do not automatically become caller facts.

All source changes for the coverage task are confined to `std/`. Module-owned
validation projects also live here. Local Session journals are kept under
`.verification/`, ignored by Git and excluded by the std packaging helper.
No kernel change, new trust, or extra unproved assumption is used to make a
library theorem pass.
