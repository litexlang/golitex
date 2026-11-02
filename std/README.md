# Litex standard mathematics library

The standard library contains reusable mathematical definitions, constructions
and checked source theorems. Native operations remain available without an
import; these modules supply reusable source mathematics above them.

## Current modules

| Subject | Modules and current source scope |
| --- | --- |
| Natural numbers and recursion | [natural_numbers](natural_numbers/README.md): actual index-dependent recursion on any set, unique existence, unique predecessors and natural Euclidean division. |
| Sets, relations and order | [set_laws](set_laws/README.md): pair-display compatibility, relative-complement partitions and the bounded Russell diagonal; [relations](relations/README.md): equivalence classes and partitions, partial orders, subset extrema, monotone maps and order embeddings. |
| Finite Cartesian products | [finite_products](finite_products/README.md): actual products of arbitrary finite families, the singleton empty product, finite choice by induction and empty-factor/positive native-product compatibility laws. |
| Equinumerosity and cardinality | [cardinality](cardinality/README.md): bijections on arbitrary sets, source/native finite-cardinality correspondence, finite image bounds and sequence/function-space counting with empty cases. |
| Countability | [countability](countability/README.md): distinct finite/countably-infinite conventions, unique increasing natural-subset enumerations, subsets, images, unions, integers, triangular pairs, products and rationals. |
| Scalar approximation | [real_approximation](real_approximation/README.md): positive-radius epsilon-closeness, sharp product-error bounds, interval betweenness, bounded-product and reciprocal errors, and absolute values of natural/integer powers. |
| Rational-square gaps | [rational_numbers](rational_numbers/README.md): no rational square equals two, and nonnegative rational squares straddle two at every positive separation. |
| Rational sequences | [rational_sequences](rational_sequences/README.md): arbitrary integer starts, source Cauchy and rational bounds, actual native reindexing, sequence equivalence, arithmetic and reciprocals, geometric perturbations and separated and signed representatives of native reals, and limit order. |
| Extended real order and extrema | [extended_reals](extended_reals/README.md): finite completeness, literal real inclusion with two nonreal infinities, total negation/order, and suprema/infima of arbitrary extended-real subsets. |
| Real power laws | [real_power_laws](real_power_laws/README.md): positive-real power algebra, actual nonnegative root suprema, corrected root laws and rational exponent order. |
| Real sequences on integer tails | [real_sequences](real_sequences/README.md): arbitrary integer starts, closed-epsilon Cauchy/convergence, partial selected limits, boundedness and all eight arithmetic/minimum/maximum limit laws; [rational_sequence_limits](rational_sequence_limits/README.md): actual rational-to-real values, radius consistency and equality of formal/genuine selected limits. |
| Sequence extrema and monotone limits | [extended_sequence_extrema](extended_sequence_extrema/README.md): complete extended-real-valued tails, total extrema, full extended bounds/strict approach and actual same-value real embedding; [real_sequence_extrema](real_sequence_extrema/README.md): real one-sided bounds, pairwise monotonicity and exact extremal monotone limits on arbitrary integer tails. |
| Limit points and extremal limits | [real_sequence_limsup](real_sequence_limsup/README.md): actual tail restrictions and extended-valued limsup/liminf, finite limit points, full extremal bounds/comparison, finite convergence criterion, squeeze, absolute-value zero test and source/native Cauchy completeness. |
| Standard real sequence limits | [real_standard_limits](real_standard_limits/README.md): reciprocal natural roots, every geometric convergence/divergence case, and fixed positive-base nth roots on the complete original integer domain. |
| Real subsequences | [real_subsequences](real_subsequences/README.md): actual increasing integer-tail index maps, source subsequence relations and limit preservation, constructive limit-point equivalence and Bolzano-Weierstrass. |
| Real exponent limits | [real_exponent_limits](real_exponent_limits/README.md): actual continuous images and fixed-base power functions, rational-approximation limit compatibility and independence, and full real-exponent order laws. |
| Finite real sums | [finite_sums](finite_sums/README.md): total interval sums on exact original domains, corrected empty-boundary laws, actual bijective enumerations and translation, arbitrary finite-set laws and finite Fubini with empty factors. |
| Real series on integer tails | [real_tail_series](real_tail_series/README.md): complete original-domain convergence and Cauchy/absolute/alternating tests at any integer start, full sum bounds and series algebra, finite-prefix equivalence including zero length, integer translation and general telescoping. |
| Nonnegative real series, condensation and reciprocal powers | [real_nonnegative_series](real_nonnegative_series/README.md): real upper-bound convergence criterion including zero bounds, full absolute comparison and scalar sum bounds, the nonabsolute/divergent-majorant contrapositive on original integer tails, complete start0 geometric sums/absolute convergence/divergence, dyadic condensation with exact partial-sum bounds, and positive real-exponent p-series classification. |
| Rearrangements of real series | [real_series_rearrangements](real_series_rearrangements/README.md): arbitrary natural bijections preserve nonnegative sums and absolute convergence with signed sums; actual finite-prefix image bounds and inverse maps retain complete original domains. |
| Root and ratio tests for real series | [real_series_root_ratio_tests](real_series_root_ratio_tests/README.md): original-degree root tests with extended extrema, the complete ratio/root inequality chain, absolute-ratio criteria for nonzero signed terms on original integer tails, and the actual variable-base limit n^(1/n) -> 1. |
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
| Real interval existence | [real_interval_laws](real_interval_laws/README.md): closed-interval intermediate values, both endpoint orders, interior witnesses, local upper bounds and bounded continuous images. |
| Real integration | [real_integral_laws](real_integral_laws/README.md): absolute-integral and integral-difference bounds, with exact orientation and integrability hypotheses. |
| Multivariable analysis | [real_multivariable](real_multivariable/README.md): coordinate paths, local scalar/vector relations, directional and higher derivatives, cross products and ordered rectangular iterated integrals. |
| Regularity and higher derivatives | [real_regularity](real_regularity/README.md), [real_regularity_laws](real_regularity_laws/README.md), [real_higher_order_laws](real_higher_order_laws/README.md). |
| Finite function sums | [real_function_sums](real_function_sums/README.md) and [real_scalar_function_sums](real_scalar_function_sums/README.md): finite combinations and the corresponding analysis laws. |
| Compatibility | [basics](basics/README.md) exports no declarations; use native vocabulary directly. |

A module's presence does not imply that a complete course is covered. Its
README states the implemented interface and boundaries; `math_collections.md`
explains the mathematical dependency spine. Course coverage requires checked
definitions, actual constructions, main results and representative uses for
each chapter.

## Use and verification

Import a module through a project's `litex.config` `[import std]` table. Follow
that module's explicit definition-release and theorem-call contract; imported
ambient facts do not automatically become caller facts.

These source theorems reuse Litex's native mathematical foundations. They do
not introduce new trust or extra unproved assumptions to make a library
theorem pass.
