```litex
# Analysis I, Chapter 1: Introduction.
#
# Core coverage snapshot.
# Essential content: motivation examples showing that limits, sums, integrals,
# derivatives, and lengths need hypotheses before algebraic manipulation.
# Fully formalized: no theorem core is meant to be checked here; this chapter
# is runnable commentary that points to Chapters 6-11.  Approximate core
# coverage: 0/0 active theorem targets; later chapters carry the formal APIs.
#
# Chapter 1 is a motivation chapter. Its mathematical content is mostly a
# sequence of examples showing that familiar limit, sum, integral, derivative,
# and length manipulations need hypotheses. This file is intentionally
# documentation-like: it does not introduce placeholder props or theorem
# interfaces before the later chapters and standard-library files have made
# those APIs stable.
#
# The analysis formalization will build the following mathematical layers in
# the order suggested by the book:
#
# - Chapter 2: natural numbers, induction, recursion, finite sums, and
#   exponentiation;
# - Chapter 3: sets, functions, images, cardinality, and finite products;
# - Chapter 4: integers, rationals, and rational metric estimates;
# - Chapter 5: real order, absolute value, intervals, and completeness;
# - Chapter 6: sequences, Cauchy sequences, subsequences, limsup/liminf, and
#   monotone convergence;
# - Chapters 7-8: infinite series, countability, choice, countable sums, and
#   rearrangement theorems;
# - Chapter 9: real-subset topology, function limits, continuity, compactness,
#   IVT, EVT, and uniform continuity;
# - Chapter 10: differentiation, derivative rules, Rolle's theorem, MVT,
#   inverse functions, and L'Hopital-style results;
# - Chapter 11: Riemann integration, partitions, upper and lower sums, FTC,
#   change of variables, and integration by parts;
# - Later analysis: curve length and other geometric limiting constructions.
#
# The snippets below are intentionally commented out. They are not runnable as
# isolated code: making them executable would require the later APIs and the
# surrounding hypotheses, which would obscure the point of this introductory
# chapter. Those APIs should be read as future interfaces shaped by this
# Analysis I formalization, not as an external package that the book depends on.

# Chapter 2 preview: natural numbers, induction, and recursive definitions.
# This preview says Chapter 2 treats `N` as the basic counting system.  The
# formal work is to show that addition, Euclidean division, and recursion are
# governed by induction: prove the base case, then prove the successor step.
#
# ```litex
# forall n N:
#     n + 0 = n
#
# forall n N, q N_pos:
#     exist a, r N st {n = a * q + r, r < q}
#
# have fn factorial(n N) N by cases:
#     case n = 0: 1
#     case n > 0: n * factorial(n - 1)
#
# forall n N:
#     factorial(n) $in N_pos
# ```

# Chapter 3 preview: sets, functions, and extensional reasoning.
# This preview says Chapter 3 reads sets by their elements and functions by
# their values.  Subset proofs introduce an arbitrary member; equality proofs
# prove both membership directions; function-image statements describe exactly
# which values occur.
#
# ```litex
# forall A, B, C set:
#     A $subset B
#     B $subset C
#     =>:
#         A $subset C
#
# forall X set:
#     have fn id_X(x X) X = x
#     $is_bijective_fn(X, X, id_X)
#
# forall S, T set, f fn(x S) T, A power_set(S):
#     $is_forward_image_of(S, T, f, A, {f(x): x A})
# ```

# Chapters 4-5 preview: rationals, metric estimates, and real completeness.
# This preview says Chapters 4 and 5 build the numeric background for
# analysis.  Rational estimates use absolute-value distance and epsilon
# closeness, while real completeness asserts that bounded nonempty sets have
# least upper bounds and that rational Cauchy representatives determine real
# numbers.
#
# ```litex
# forall x, y, z Q:
#     dist_Q(x, z) <= dist_Q(x, y) + dist_Q(y, z)
#
# forall a seq(Q):
#     $is_cauchy_sequence_in_Q(a)
#     =>:
#         exist x R st {$has_formal_limit_in_Q(a, x)}
#
# forall E power_set(R):
#     $is_nonempty_set(E)
#     $has_upper_bound(E)
#     =>:
#         exist s R st {$is_least_upper_bound(E, s)}
# ```

# Chapter 6 preview: sequence limits and compactness pressure tests.
# This preview says Chapter 6 turns epsilon arguments into reusable sequence
# patterns.  A limit proof chooses a tail index; a Cauchy proof compares two
# late terms; compactness and monotone convergence turn boundedness into
# subsequential or ordinary convergence.
#
# ```litex
# $has_limit('(n N_pos) R {1 / n}, 0)
#
# forall a seq(R):
#     $is_cauchy_sequence(a)
#     =>:
#         $is_bounded_sequence(a)
#
# forall a seq(R):
#     $is_increasing_sequence(a)
#     $is_bounded_above_sequence(a)
#     =>:
#         exist L R st {$has_limit(a, L)}
#
# forall a seq(R), X power_set(R):
#     $is_sequence_in_subset(a, X)
#     $is_sequentially_compact_subset(X)
#     =>:
#         exist b seq(R), L X st {$has_subsequence(a, b), $has_limit(b, L)}
# ```

# Chapters 7-8 preview: infinite series, countability, and rearrangement.
# This preview says Chapters 7 and 8 recast infinite sums through partial sums
# and countable enumerations.  The key proof ideas are Cauchy criteria for
# tails, bounded partial sums for nonnegative series, and invariance under
# allowed reindexings.
#
# ```litex
# forall a seq(R), s R:
#     $has_series_sum(a, s)
#     =>:
#         $has_limit(a, 0)
#
# forall a seq(R):
#     $is_nonnegative_sequence(a)
#     $is_bounded_above_sequence('(n N_pos) R {sum(1, n, a)})
#     =>:
#         $is_convergent_series(a)
#
# forall a seq(R), f fn(n N_pos) N_pos, s R:
#     $is_absolutely_convergent_series(a)
#     $is_permutation_of_N_pos(f)
#     =>:
#         $has_series_sum('(n N_pos) R {a(f(n))}, s)
# ```

# Chapter 9 preview: real-line topology and continuous functions.
# This preview says Chapter 9 formalizes "near a point" reasoning on subsets
# of `R`.  Function limits choose a delta for each epsilon; continuity sets the
# limiting value equal to the function value; compactness supplies maximum,
# minimum, and intermediate-value witnesses.
#
# ```litex
# $is_closure_of(R, Q)
#
# forall X power_set(R), x0 R:
#     $is_adherent_point(X, x0)
#     =>:
#         $has_function_limit_at(X, X, '(x X) R {x}, x0, x0)
#
# forall a, b R, f fn(x cc(a, b)) R:
#     a < b
#     $is_continuous_on(cc(a, b), f)
#     =>:
#         exist xmax cc(a, b) st {$has_maximum_at(cc(a, b), f, xmax)}
#
# forall a, b, y R, f fn(x cc(a, b)) R:
#     a < b
#     $is_continuous_on(cc(a, b), f)
#     f(a) <= y
#     y <= f(b)
#     =>:
#         exist c cc(a, b) st {f(c) = y}
# ```

# Chapter 10 preview: local linear approximation, not only algebra rules.
# This preview says Chapter 10 defines a derivative as the limit of the
# difference quotient.  The central proof move is to replace a function near a
# point by its best linear approximation, then use Rolle/MVT-style interval
# arguments to control signs and monotonicity.
#
# ```litex
# forall X set, f fn(x X) R, x0 X, L R:
#     X $subset R
#     $has_derivative_at(X, f, x0, L)
#     =>:
#         $is_continuous_at(X, f, x0)
#
# forall a, b R, f fn(x cc(a, b)) R:
#     a < b
#     $is_continuous_on(cc(a, b), f)
#     $is_differentiable_on(oo(a, b), f)
#     f(a) = f(b)
#     =>:
#         exist c oo(a, b) st {$has_derivative_at(oo(a, b), f, c, 0)}
#
# forall a, b R, f fn(x cc(a, b)) R:
#     a < b
#     $is_continuous_on(cc(a, b), f)
#     $is_differentiable_on(oo(a, b), f)
#     =>:
#         exist c oo(a, b) st {$has_derivative_at(oo(a, b), f, c, (f(b) - f(a)) / (b - a))}
# ```

# Chapter 11 preview: Riemann partitions, upper/lower sums, and FTC.
# This preview says Chapter 11 defines integration by cutting an interval into
# finitely many pieces.  Partition sums approximate area; upper and lower
# integrals squeeze each other; the FTC connects those integrals to
# derivatives and antiderivatives.
#
# ```litex
# forall a, b R, P set:
#     a < b
#     $is_partition_of_interval(cc(a, b), P)
#     =>:
#         $is_finite_set(P)
#
# forall a, b R, f fn(x cc(a, b)) R:
#     a < b
#     $is_continuous_on(cc(a, b), f)
#     =>:
#         $is_riemann_integrable(cc(a, b), f)
#
# forall a, b R, f fn(x cc(a, b)) R, P set:
#     $is_partition_of_interval(cc(a, b), P)
#     =>:
#         lower_sum(f, P) <= upper_sum(f, P)
#
# forall a, b R, F, f fn(x cc(a, b)) R:
#     a < b
#     $is_derivative_function_on(cc(a, b), F, f)
#     $is_riemann_integrable(cc(a, b), f)
#     =>:
#         $has_riemann_integral(cc(a, b), f, F(b) - F(a))
# ```

# Later analysis preview: curve length and other limiting constructions.
# This preview records the later pattern behind many geometric limits: define
# finite approximations first, prove their estimates, and then take a limiting
# limit once the required convergence or supremum interface exists.
#
# ```litex
# forall gamma fn(t cc(0, 1)) cart(R, R), P set:
#     $is_partition_of_interval(cc(0, 1), P)
#     =>:
#         $polygonal_length(gamma, P) >= 0
#
# forall gamma fn(t cc(0, 1)) cart(R, R), L R:
#     $has_curve_length(gamma, L)
#     =>:
#         L >= 0
#
# forall gamma fn(t cc(0, 1)) cart(R, R):
#     $piecewise_smooth_path(gamma)
#     =>:
#         exist L R st {$has_curve_length(gamma, L)}
# ```

# Deferred source-section map.
#
# Chapter 1 has only Section 1.2 as formalization source material.  The
# comments above point to later APIs rather than active proof obligations:
# - Example 1.2.2 and Example 1.2.5: series, infinite sums, and Fubini-style
#   interchange.  These are Chapter 7 and Chapter 8 debt.
# - Example 1.2.3, Example 1.2.4, Example 1.2.7, and Example 1.2.8: sequence
#   limits, function limits, iterated limits, and uniform-control hypotheses.
#   These are Chapter 6 and Chapter 9 debt.
# - Example 1.2.6 and Example 1.2.9: interchanging integrals and limits under
#   integration.  These are Chapter 11 and later integration-library debt.
# - Example 1.2.10 and Example 1.2.12: derivative-limit interchange and
#   L'Hopital-style hypotheses.  These are Chapter 10 debt.
# - Example 1.2.13: curve length as a limiting construction.  This is later
#   analysis-library debt beyond the current Chapter 11 slice.

```
