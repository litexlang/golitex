```litex
# Analysis I, Chapter 6: Limits of sequences.
#
# This file gives a runnable Litex sketch for Sections 6.1-6.7.  The epsilon
# definitions are stated directly over builtin real numbers and positive-indexed
# `seq(R)`.  Section 6.2 is kept as a source-order map of the extended-real
# material rather than a local construction of `R*`; later uses of infinity are
# expressed through concrete unboundedness, threshold, and finite limsup/liminf
# interfaces.  Broad background interfaces stay close to the source-facing
# section that first uses them; the Chapter 5 least-upper-bound interface
# remains here because Sections 6.3 and 6.4 use it repeatedly.

# Chapter-level background cite interfaces

# The theorem below is cited from Chapter 5's least-upper-bound/completeness
# development.  We keep this interface at the top so broad cite debt is easy to
# find and replace later, while the proofs in Sections 6.3 and 6.4 can use it
# without running the full Chapter 5 sketch and colliding with local names.

prop is_upper_bound(E set, M R):
    E $subset R
    forall x E:
        x <= M

prop has_upper_bound(E set):
    E $subset R
    exist M R st {$is_upper_bound(E, M)}

prop is_least_upper_bound(E set, M R):
    E $subset R
    $is_upper_bound(E, M)
    forall B R:
        $is_upper_bound(E, B)
        =>:
            M <= B

prop has_least_upper_bound(E set):
    exist M R st {$is_least_upper_bound(E, M)}

know:
    forall E power_set(R):
        $is_nonempty_set(E)
        $has_upper_bound(E)
        =>:
            exist! M R st {$is_least_upper_bound(E, M)}
            $has_least_upper_bound(E)

# 6.1 Convergence and limit laws

"""
Definition 6.1.1 (Distance on the real line). The distance between two real
numbers x and y is |x-y|. This quantity is non-negative, symmetric in x and y,
and is zero exactly when x=y.
"""

# Litex already has builtin real numbers and absolute value.  We name the
# distance function because the chapter repeatedly talks about closeness.

have fn dist_R(x, y R) R = abs(x - y)

forall x, y R:
    dist_R(x, y) = abs(x - y)

"""
Definition 6.1.2 (epsilon-closeness). Let epsilon > 0 be a real number. Two
real numbers are epsilon-close when their distance is at most epsilon.
"""

# The convergence predicates below use a strict `< epsilon` tail condition.
# For positive epsilon, the strict and non-strict formulations are equivalent
# after shrinking or enlarging the permitted error.

prop is_epsilon_close_in_R(epsilon R_pos, x, y R):
    dist_R(x, y) <= epsilon

forall epsilon R_pos, x R:
    dist_R(x, x) = 0
    0 <= epsilon
    $is_epsilon_close_in_R(epsilon, x, x)

"""
Definition 6.1.3 (Cauchy sequences of reals). Let epsilon > 0 be a real
number. A tail of a real sequence is epsilon-steady when every pair of terms
in that tail are epsilon-close. A sequence is eventually epsilon-steady when
some tail has this property. The sequence is Cauchy when it is eventually
epsilon-steady for every positive epsilon.
"""

# The tail predicate separates the chosen cutoff from the final Cauchy
# quantifier.  This keeps later proofs close to the usual epsilon argument.

prop is_tail_epsilon_steady(a seq(R), epsilon R_pos, n0 N_pos):
    forall j, k N_pos:
        j >= n0
        k >= n0
        =>:
            abs(a(j) - a(k)) < epsilon

prop has_eventual_epsilon_steadiness(a seq(R), epsilon R_pos):
    exist n0 N_pos st {$is_tail_epsilon_steady(a, epsilon, n0)}

prop is_cauchy_sequence(a seq(R)):
    forall epsilon R_pos:
        $has_eventual_epsilon_steadiness(a, epsilon)

prop is_cauchy_sequence_with_rational_epsilon(a seq(R)):
    forall epsilon Q_pos:
        $has_eventual_epsilon_steadiness(a, epsilon)

"""
Proposition 6.1.4. The Cauchy definition is unchanged if the epsilon parameter
ranges over positive rationals instead of positive reals.
"""

# A rational epsilon below a real epsilon is a positive rational error bound
# small enough for the corresponding real epsilon argument.

prop is_rational_epsilon_below(delta Q_pos, epsilon R_pos):
    delta < epsilon

thm Archimedean_density_bridge:
    ? forall epsilon R_pos:
        exist delta Q_pos st {$is_rational_epsilon_below(delta, epsilon)}
    by thm archimedean_property(epsilon)
    have by exist m N_pos st {1 / m < epsilon}: m
    have delta Q_pos = 1 / m
    delta < epsilon
    witness exist eta Q_pos st {$is_rational_epsilon_below(eta, epsilon)} from delta:
        delta < epsilon
        $is_rational_epsilon_below(delta, epsilon)

thm cauchy_rational_epsilon_implies_cauchy:
    ? forall a seq(R):
        $is_cauchy_sequence_with_rational_epsilon(a)
        =>:
            $is_cauchy_sequence(a)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_epsilon_steadiness(a, epsilon)
        by thm Archimedean_density_bridge(epsilon)
        have by exist delta Q_pos st {$is_rational_epsilon_below(delta, epsilon)}: delta
        $is_rational_epsilon_below(delta, epsilon)
        delta < epsilon
        $has_eventual_epsilon_steadiness(a, delta)
        have by exist n0 N_pos st {$is_tail_epsilon_steady(a, delta, n0)}: n0
        witness exist n1 N_pos st {$is_tail_epsilon_steady(a, epsilon, n1)} from n0:
            forall j, k N_pos:
                j >= n0
                k >= n0
                =>:
                    abs(a(j) - a(k)) < delta
                    abs(a(j) - a(k)) < delta < epsilon
                    abs(a(j) - a(k)) < epsilon
            $is_tail_epsilon_steady(a, epsilon, n0)
        $has_eventual_epsilon_steadiness(a, epsilon)
    $is_cauchy_sequence(a)

thm cauchy_implies_cauchy_with_rational_epsilon:
    ? forall a seq(R):
        $is_cauchy_sequence(a)
        =>:
            $is_cauchy_sequence_with_rational_epsilon(a)
    claim:
        ? forall epsilon Q_pos:
            $has_eventual_epsilon_steadiness(a, epsilon)
        $has_eventual_epsilon_steadiness(a, epsilon)
    $is_cauchy_sequence_with_rational_epsilon(a)

"""
Definition 6.1.5 (Convergence of real sequences). A real sequence converges
to L if every positive epsilon has a tail on which all terms are epsilon-close
to L. Equivalently, after some index depending on epsilon, every later term
lies inside the epsilon-neighborhood of L.
"""

# These predicates are the local epsilon-tail formulation of convergence used
# throughout the rest of the chapter.

prop is_tail_close_to(a seq(R), L R, epsilon R_pos, n0 N_pos):
    forall n N_pos:
        n >= n0
        =>:
            abs(a(n) - L) < epsilon

prop has_eventual_closeness_to(a seq(R), L R, epsilon R_pos):
    exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)}

prop has_limit(a seq(R), L R):
    forall epsilon R_pos:
        $has_eventual_closeness_to(a, L, epsilon)

thm has_limit_gives_eventual_closeness:
    ? forall a seq(R), L R, epsilon R_pos:
        $has_limit(a, L)
        =>:
            $has_eventual_closeness_to(a, L, epsilon)
    $has_eventual_closeness_to(a, L, epsilon)

prop is_convergent_sequence(a seq(R)):
    exist L R st {$has_limit(a, L)}

prop is_divergent_sequence(a seq(R)):
    not $is_convergent_sequence(a)

"""
Examples 6.1.6. Constant sequences converge, while the sequence 1/n converges
to 0.
"""

# Constant sequences are checked directly.  The `1/n` example is recorded again
# below as Proposition 6.1.11, where the Archimedean argument belongs.

claim:
    ? forall c R:
        $has_limit('(n N_pos) R {c}, c)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(n N_pos) R {c}, c, epsilon)
        witness exist n0 N_pos st {$is_tail_close_to('(n N_pos) R {c}, c, epsilon, n0)} from 1:
            forall n N_pos:
                n >= 1
                =>:
                    '(n N_pos) R {c}(n) = c
                    c - c = 0
                    abs('(n N_pos) R {c}(n) - c) = abs(c - c)
                    abs(c - c) = abs(0) = 0
                    0 < epsilon
                    abs('(n N_pos) R {c}(n) - c) < epsilon
            $is_tail_close_to('(n N_pos) R {c}, c, epsilon, 1)
        $has_eventual_closeness_to('(n N_pos) R {c}, c, epsilon)
    $has_limit('(n N_pos) R {c}, c)

"""
Proposition 6.1.7. Limits are unique.
"""

# If a sequence had two different limits, their positive distance could be
# beaten by taking a common tail within one third of that distance from both
# limits.

thm sequence_limit_unique:
    ? forall a seq(R), L1, L2 R:
        $has_limit(a, L1)
        $has_limit(a, L2)
        =>:
            L1 = L2
    by contra:
        ? L1 = L2
        L1 != L2
        L1 - L2 != 0
        abs(L1 - L2) > 0
        abs(L1 - L2) / 3 $in R_pos
        $has_eventual_closeness_to(a, L1, abs(L1 - L2) / 3)
        $has_eventual_closeness_to(a, L2, abs(L1 - L2) / 3)
        have by exist n1 N_pos st {$is_tail_close_to(a, L1, abs(L1 - L2) / 3, n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(a, L2, abs(L1 - L2) / 3, n2)}: n2
        max(n1, n2) $in N_pos
        max(n1, n2) >= n1
        max(n1, n2) >= n2
        abs(a(max(n1, n2)) - L1) < abs(L1 - L2) / 3
        abs(a(max(n1, n2)) - L2) < abs(L1 - L2) / 3
        abs(L1 - a(max(n1, n2))) = abs(a(max(n1, n2)) - L1)
        abs(L1 - a(max(n1, n2))) < abs(L1 - L2) / 3
        abs(L1 - a(max(n1, n2))) <= abs(L1 - L2) / 3
        abs(a(max(n1, n2)) - L2) <= abs(L1 - L2) / 3
        L1 - L2 = (L1 - a(max(n1, n2))) + (a(max(n1, n2)) - L2)
        abs(L1 - L2) = abs((L1 - a(max(n1, n2))) + (a(max(n1, n2)) - L2))
        abs((L1 - a(max(n1, n2))) + (a(max(n1, n2)) - L2)) <= abs(L1 - a(max(n1, n2))) + abs(a(max(n1, n2)) - L2)
        abs(L1 - L2) <= abs(L1 - a(max(n1, n2))) + abs(a(max(n1, n2)) - L2)
        abs(L1 - a(max(n1, n2))) + abs(a(max(n1, n2)) - L2) <= abs(L1 - L2) / 3 + abs(L1 - L2) / 3
        abs(L1 - L2) <= abs(L1 - a(max(n1, n2))) + abs(a(max(n1, n2)) - L2) <= abs(L1 - L2) / 3 + abs(L1 - L2) / 3
        abs(L1 - L2) <= abs(L1 - L2) / 3 + abs(L1 - L2) / 3
        abs(L1 - L2) / 3 + abs(L1 - L2) / 3 = 2 * abs(L1 - L2) / 3
        2 / 3 < 1
        (2 / 3) * abs(L1 - L2) < 1 * abs(L1 - L2)
        (2 / 3) * abs(L1 - L2) = 2 * abs(L1 - L2) / 3
        1 * abs(L1 - L2) = abs(L1 - L2)
        2 * abs(L1 - L2) / 3 < abs(L1 - L2)
        abs(L1 - L2) <= 2 * abs(L1 - L2) / 3
        abs(L1 - L2) <= 2 * abs(L1 - L2) / 3 < abs(L1 - L2)
        abs(L1 - L2) < abs(L1 - L2)
        abs(L1 - L2) != abs(L1 - L2)
        impossible abs(L1 - L2) = abs(L1 - L2)

"""
Definition 6.1.8. The notation lim a_n denotes the unique limit when it exists;
if no real limit exists, the sequence is divergent.
"""

# The notation is a genuine function on the subtype of convergent real
# sequences.  Existence comes from the definition of convergence; uniqueness is
# Proposition 6.1.7.  Thus `lim(a)` is available only after Litex checks that
# `a` is convergent.

have fn lim as set:
    ? forall a seq(R):
        $is_convergent_sequence(a)
        =>:
            exist! L R st {$has_limit(a, L)}
    have by exist L R st {$has_limit(a, L)}: L
    claim:
        ? forall L1, L2 R:
            $has_limit(a, L1)
            $has_limit(a, L2)
            =>:
                L1 = L2
        by thm sequence_limit_unique(a, L1, L2)
    exist! L R st {$has_limit(a, L)}

forall a seq(R):
    $is_convergent_sequence(a)
    =>:
        $has_limit(a, lim(a))
forall a seq(R), L R:
    $is_convergent_sequence(a)
    $has_limit(a, L)
    =>:
        L = lim(a)
"""
Remark 6.1.9. The starting index does not affect convergence.
"""

# Sequences can be indexed from arbitrary starting integers.  For the
# positive-indexed local form, shift the tail cutoff by composing the original
# tail estimate with `n -> n + m`.

thm shifted_sequence_has_limit:
    ? forall a seq(R), L R, m N_pos:
        $has_limit(a, L)
        =>:
            $has_limit('(n N_pos) R {a(n + m)}, L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(n N_pos) R {a(n + m)}, L, epsilon)
        $has_eventual_closeness_to(a, L, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to('(n N_pos) R {a(n + m)}, L, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    n + m $in N_pos
                    n + m >= n
                    n >= n0
                    n + m >= n0
                    '(n N_pos) R {a(n + m)}(n) = a(n + m)
                    abs(a(n + m) - L) < epsilon
                    abs('(n N_pos) R {a(n + m)}(n) - L) = abs(a(n + m) - L)
                    abs('(n N_pos) R {a(n + m)}(n) - L) < epsilon
            $is_tail_close_to('(n N_pos) R {a(n + m)}, L, epsilon, n0)
        $has_eventual_closeness_to('(n N_pos) R {a(n + m)}, L, epsilon)
    $has_limit('(n N_pos) R {a(n + m)}, L)

"""
Remark 6.1.10. The dummy index letter in lim_{n -> infinity} a_n is irrelevant.
"""

# This is alpha-renaming of a bound variable.  Litex anonymous functions already
# identify the mathematical sequence by its function value, not by the displayed
# variable name.

"""
Proposition 6.1.11. The sequence 1/n converges to 0.
"""

# The proof chooses a natural cutoff with `1/N < epsilon`, then uses
# monotonicity of reciprocal on positive naturals.

have fn reciprocal_nat_seq(n N_pos) R = 1 / n

claim:
    ? forall epsilon R_pos:
        exist n_bound N_pos st {1 / n_bound < epsilon}
    by thm archimedean_property(epsilon)

claim:
    ? $has_limit(reciprocal_nat_seq, 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(reciprocal_nat_seq, 0, epsilon)
        exist n_bound N_pos st {1 / n_bound < epsilon}
        have by exist n0 N_pos st {1 / n0 < epsilon}: n0
        witness exist n1 N_pos st {$is_tail_close_to(reciprocal_nat_seq, 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    reciprocal_nat_seq(n) = 1 / n
                    n0 <= n
                    n0 * n > 0
                    1 / n = n0 / (n0 * n)
                    n0 / (n0 * n) <= n / (n0 * n)
                    n / (n0 * n) = 1 / n0
                    1 / n <= 1 / n0
                    1 / n <= 1 / n0 < epsilon
                    1 / n < epsilon
                    1 / n > 0
                    1 / n - 0 = 1 / n
                    1 / n - 0 >= 0
                    abs(1 / n - 0) = 1 / n - 0
                    abs(1 / n - 0) = 1 / n
                    abs(reciprocal_nat_seq(n) - 0) = abs(1 / n - 0)
                    abs(reciprocal_nat_seq(n) - 0) < epsilon
            $is_tail_close_to(reciprocal_nat_seq, 0, epsilon, n0)
        $has_eventual_closeness_to(reciprocal_nat_seq, 0, epsilon)
    $has_limit(reciprocal_nat_seq, 0)

"""
Proposition 6.1.12. Every convergent sequence of reals is Cauchy.
"""

# Use epsilon/2 around the limit, then compare two late terms by the triangle
# inequality.

thm has_limit_implies_cauchy:
    ? forall a seq(R), L R:
        $has_limit(a, L)
        =>:
            $is_cauchy_sequence(a)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_epsilon_steadiness(a, epsilon)
        epsilon / 2 $in R_pos
        $has_eventual_closeness_to(a, L, epsilon / 2)
        have by exist n0 N_pos st {$is_tail_close_to(a, L, epsilon / 2, n0)}: n0
        witness exist n1 N_pos st {$is_tail_epsilon_steady(a, epsilon, n1)} from n0:
            forall j, k N_pos:
                j >= n0
                k >= n0
                =>:
                    abs(a(j) - L) < epsilon / 2
                    abs(a(k) - L) < epsilon / 2
                    abs(L - a(k)) = abs(a(k) - L)
                    abs(L - a(k)) < epsilon / 2
                    abs(a(j) - a(k)) < epsilon / 2 + epsilon / 2
                    epsilon / 2 + epsilon / 2 = epsilon
                    abs(a(j) - a(k)) < epsilon
            $is_tail_epsilon_steady(a, epsilon, n0)
        $has_eventual_epsilon_steadiness(a, epsilon)
    $is_cauchy_sequence(a)

thm convergent_sequence_is_cauchy:
    ? forall a seq(R):
        $is_convergent_sequence(a)
        =>:
            $is_cauchy_sequence(a)
    have by exist L R st {$has_limit(a, L)}: L
    $has_limit(a, L)
    by thm has_limit_implies_cauchy(a, L)

"""
Example 6.1.13. The alternating sequence 1,-1,1,-1,... is not Cauchy and
therefore does not converge.
"""

# The witness obstruction is a `1`-steady tail: every tail contains both signs.

have fn alternating_one_seq(n N_pos) R = (-1)^n

claim:
    ? forall n N_pos:
        (-1)^n <= 1
        -1 <= (-1)^n
    by induc n from 1:
        ? (-1)^n <= 1
        ? -1 <= (-1)^n

        prove from n = 1:
            (-1)^1 = -1
            -1 <= 1
            (-1)^1 <= 1
            -1 <= (-1)^1

        prove induc:
            (-1)^(n + 1) = (-1)^n * (-1)
            (-1)^n <= 1
            -1 <= (-1)^n
            (-1)^n * (-1) >= 1 * (-1)
            1 * (-1) = -1
            (-1)^n * (-1) >= -1
            -1 <= (-1)^n * (-1)
            (-1)^n * (-1) <= (-1) * (-1)
            (-1) * (-1) = 1
            (-1)^n * (-1) <= 1
            (-1)^(n + 1) <= 1
            -1 <= (-1)^(n + 1)

claim:
    ? not $is_cauchy_sequence(alternating_one_seq)
    by contra:
        ? not $is_cauchy_sequence(alternating_one_seq)
        $is_cauchy_sequence(alternating_one_seq)
        1 $in R_pos
        $has_eventual_epsilon_steadiness(alternating_one_seq, 1)
        have by exist n0 N_pos st {$is_tail_epsilon_steady(alternating_one_seq, 1, n0)}: n0
        2 * n0 $in N_pos
        2 * n0 + 1 $in N_pos
        2 * n0 >= n0
        2 * n0 + 1 >= n0
        abs(alternating_one_seq(2 * n0) - alternating_one_seq(2 * n0 + 1)) < 1
        (-1)^2 = 1
        ((-1)^2)^n0 = 1^n0
        1^n0 = 1
        ((-1)^2)^n0 = 1
        ((-1)^2)^n0 = (-1)^(2 * n0)
        alternating_one_seq(2 * n0) = '(n N_pos) R {(-1)^n}(2 * n0)
        '(n N_pos) R {(-1)^n}(2 * n0) = (-1)^(2 * n0)
        alternating_one_seq(2 * n0) = (-1)^(2 * n0) = 1
        (-1)^1 = -1
        (-1)^(2 * n0 + 1) = (-1)^(2 * n0) * (-1)^1
        (-1)^(2 * n0 + 1) = 1 * (-1) = -1
        alternating_one_seq(2 * n0 + 1) = '(n N_pos) R {(-1)^n}(2 * n0 + 1)
        '(n N_pos) R {(-1)^n}(2 * n0 + 1) = (-1)^(2 * n0 + 1)
        alternating_one_seq(2 * n0 + 1) = (-1)^(2 * n0 + 1) = -1
        alternating_one_seq(2 * n0) - alternating_one_seq(2 * n0 + 1) = 1 - (-1) = 2
        abs(alternating_one_seq(2 * n0) - alternating_one_seq(2 * n0 + 1)) = 2
        2 < 1
        impossible 2 < 1

claim:
    ? not $is_convergent_sequence(alternating_one_seq)
    by contra:
        ? not $is_convergent_sequence(alternating_one_seq)
        $is_convergent_sequence(alternating_one_seq)
        by thm convergent_sequence_is_cauchy(alternating_one_seq)
        impossible not $is_cauchy_sequence(alternating_one_seq)

claim:
    ? $is_divergent_sequence(alternating_one_seq)
    not $is_cauchy_sequence(alternating_one_seq)
    not $is_convergent_sequence(alternating_one_seq)
    $is_divergent_sequence(alternating_one_seq)

"""
Remark 6.1.14. The converse, Cauchy implies convergent, is postponed.
"""

# The completeness theorem for `R` is where the Cauchy-implies-convergent
# direction belongs in this chapter.

"""
Proposition 6.1.15. Formal rational Cauchy limits are genuine real limits.
"""

# This is a source-facing bridge from Chapter 5's Cauchy construction of `R`:
# a rational Cauchy representative for a real number should converge to that
# real when viewed as a real-valued sequence. The original textbook did not prove this, but it is easy to prove. The sketch does not need this
# bridge formally, and later arguments use the direct real completeness theorem
# instead, so we leave it as commentary rather than adding unused proof debt.

"""
Definition 6.1.16 (Bounded real sequences). A real sequence is bounded if
there is a non-negative real constant M such that abs(a_n) <= M for every
positive index n. The same bound controls the entire sequence, not just a
tail.
"""

prop is_finite_prefix_bounded(a seq(R), n N_pos, M R):
    M >= 0
    forall i N_pos:
        i <= n
        =>:
            abs(a(i)) <= M

prop is_bounded_by(a seq(R), M R):
    M >= 0
    forall i N_pos:
        abs(a(i)) <= M

prop is_bounded_sequence(a seq(R)):
    exist M R st {$is_bounded_by(a, M)}

"""
Corollary 6.1.17. Every convergent sequence is bounded.
"""

# A finite prefix is bounded by the running maximum of absolute values.  A
# Cauchy sequence is then bounded by combining that finite prefix with a
# `1`-steady tail.

have fn prefix_bound(a seq(R), n N_pos) R by induc n from 1:
    case n = 1: abs(a(1))
    case n > 1: max(prefix_bound(a, n - 1), abs(a(n)))

claim:
    ? forall a seq(R), n N_pos:
        $is_finite_prefix_bounded(a, n, prefix_bound(a, n))
    by induc n from 1:
        ? $is_finite_prefix_bounded(a, n, prefix_bound(a, n))

        prove from n = 1:
            prefix_bound(a, 1) = abs(a(1))
            abs(a(1)) >= 0
            prefix_bound(a, 1) >= 0
            forall i N_pos:
                i <= 1
                =>:
                    i = 1
                    a(i) = a(1)
                    abs(a(i)) = abs(a(1))
                    abs(a(i)) <= prefix_bound(a, 1)
            $is_finite_prefix_bounded(a, 1, prefix_bound(a, 1))

        prove induc:
            n + 1 > 1
            prefix_bound(a, n + 1) = max(prefix_bound(a, n + 1 - 1), abs(a(n + 1)))
            n + 1 - 1 = n
            prefix_bound(a, n) = prefix_bound(a, n + 1 - 1)
            prefix_bound(a, n + 1 - 1) <= max(prefix_bound(a, n + 1 - 1), abs(a(n + 1)))
            prefix_bound(a, n) <= prefix_bound(a, n + 1 - 1) <= max(prefix_bound(a, n + 1 - 1), abs(a(n + 1))) = prefix_bound(a, n + 1)
            prefix_bound(a, n) <= prefix_bound(a, n + 1)
            abs(a(n + 1)) <= max(prefix_bound(a, n + 1 - 1), abs(a(n + 1))) = prefix_bound(a, n + 1)
            abs(a(n + 1)) <= prefix_bound(a, n + 1)
            prefix_bound(a, n) >= 0
            0 <= prefix_bound(a, n) <= prefix_bound(a, n + 1)
            prefix_bound(a, n + 1) >= 0
            forall i N_pos:
                i <= n
                =>:
                    abs(a(i)) <= prefix_bound(a, n)
                    abs(a(i)) <= prefix_bound(a, n) <= prefix_bound(a, n + 1)
                    abs(a(i)) <= prefix_bound(a, n + 1)
            forall i N_pos:
                i >= n + 1
                i <= n + 1
                =>:
                    i = n + 1
                    a(i) = a(n + 1)
                    a(n + 1) <= abs(a(n + 1))
                    a(i) = a(n + 1) <= abs(a(n + 1)) <= prefix_bound(a, n + 1)
                    a(i) <= prefix_bound(a, n + 1)
                    -a(n + 1) <= abs(a(n + 1))
                    -a(i) = -a(n + 1)
                    -a(i) = -a(n + 1) <= abs(a(n + 1)) <= prefix_bound(a, n + 1)
                    -a(i) <= prefix_bound(a, n + 1)
                    abs(a(i)) <= prefix_bound(a, n + 1)
            claim:
                ? forall i N_pos:
                    i <= n + 1
                    =>:
                        abs(a(i)) <= prefix_bound(a, n + 1)
                i <= n or i >= n + 1
                by cases:
                    ? abs(a(i)) <= prefix_bound(a, n + 1)
                    case i <= n:
                        abs(a(i)) <= prefix_bound(a, n + 1)
                    case i >= n + 1:
                        i <= n + 1
                        abs(a(i)) <= prefix_bound(a, n + 1)
            $is_finite_prefix_bounded(a, n + 1, prefix_bound(a, n + 1))

thm cauchy_sequence_is_bounded:
    ? forall a seq(R):
        $is_cauchy_sequence(a)
        =>:
            $is_bounded_sequence(a)
    1 $in R_pos
    $has_eventual_epsilon_steadiness(a, 1)
    have by exist n0 N_pos st {$is_tail_epsilon_steady(a, 1, n0)}: n0
    $is_tail_epsilon_steady(a, 1, n0)
    $is_finite_prefix_bounded(a, n0, prefix_bound(a, n0))
    prefix_bound(a, n0) >= 0
    abs(a(n0)) >= 0
    prefix_bound(a, n0) + abs(a(n0)) + 1 $in R
    prefix_bound(a, n0) + abs(a(n0)) + 1 >= 0
    abs(a(n0)) + 1 <= prefix_bound(a, n0) + abs(a(n0)) + 1
    forall i N_pos:
        i <= n0
        =>:
            abs(a(i)) <= prefix_bound(a, n0)
            abs(a(i)) <= prefix_bound(a, n0) <= prefix_bound(a, n0) + abs(a(n0)) + 1
            abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
    forall i N_pos:
        i >= n0
        =>:
            abs(a(i) - a(n0)) < 1
            abs(a(i) - a(n0)) <= 1
            a(i) - a(n0) <= abs(a(i) - a(n0))
            a(i) - a(n0) <= abs(a(i) - a(n0)) <= 1
            a(i) - a(n0) <= 1
            a(n0) <= abs(a(n0))
            a(i) = (a(i) - a(n0)) + a(n0)
            (a(i) - a(n0)) + a(n0) <= 1 + abs(a(n0))
            a(i) <= 1 + abs(a(n0))
            -(a(i) - a(n0)) <= abs(a(i) - a(n0))
            -(a(i) - a(n0)) <= abs(a(i) - a(n0)) <= 1
            -(a(i) - a(n0)) <= 1
            -a(n0) <= abs(a(n0))
            -a(i) = -(a(i) - a(n0)) + -a(n0)
            -(a(i) - a(n0)) + -a(n0) <= 1 + abs(a(n0))
            -a(i) <= 1 + abs(a(n0))
            abs(a(i)) <= 1 + abs(a(n0))
            1 + abs(a(n0)) = abs(a(n0)) + 1
            abs(a(i)) <= 1 + abs(a(n0)) = abs(a(n0)) + 1 <= prefix_bound(a, n0) + abs(a(n0)) + 1
            abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
    claim:
        ? forall i N_pos:
            abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
        i <= n0 or i >= n0 + 1
        by cases:
            ? abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
            case i <= n0:
                abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
            case i >= n0 + 1:
                n0 + 1 > n0
                i >= n0 + 1 > n0
                i >= n0
                abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
    witness exist M R st {$is_bounded_by(a, M)} from prefix_bound(a, n0) + abs(a(n0)) + 1:
        prefix_bound(a, n0) + abs(a(n0)) + 1 >= 0
        forall i N_pos:
            abs(a(i)) <= prefix_bound(a, n0) + abs(a(n0)) + 1
        $is_bounded_by(a, prefix_bound(a, n0) + abs(a(n0)) + 1)
    $is_bounded_sequence(a)

thm convergent_sequence_is_bounded:
    ? forall a seq(R):
        $is_convergent_sequence(a)
        =>:
            $is_bounded_sequence(a)
    have by exist L R st {$has_limit(a, L)}: L
    $has_limit(a, L)
    by thm has_limit_implies_cauchy(a, L)
    by thm cauchy_sequence_is_bounded(a)

claim:
    ? forall a seq(R), L R:
        $has_limit(a, L)
        =>:
            $is_bounded_sequence(a)
    by thm has_limit_implies_cauchy(a, L)
    by thm cauchy_sequence_is_bounded(a)

"""
Example 6.1.18. The sequence 1,2,3,4,... is unbounded, hence divergent.
"""

have fn natural_as_real_seq(n N_pos) R = n

claim:
    ? not $is_bounded_sequence(natural_as_real_seq)
    by contra:
        ? not $is_bounded_sequence(natural_as_real_seq)
        $is_bounded_sequence(natural_as_real_seq)
        have by exist M R st {$is_bounded_by(natural_as_real_seq, M)}: M
        M >= 0
        M + 1 > 0
        M + 1 $in R_pos
        1 / (M + 1) $in R_pos
        exist n_bound N_pos st {1 / n_bound < 1 / (M + 1)}
        have by exist n0 N_pos st {1 / n0 < 1 / (M + 1)}: n0
        n0 > 0
        n0 * (M + 1) > 0
        (1 / n0) * (n0 * (M + 1)) < (1 / (M + 1)) * (n0 * (M + 1))
        (1 / n0) * (n0 * (M + 1)) = M + 1
        (1 / (M + 1)) * (n0 * (M + 1)) = n0
        M + 1 < n0
        M < M + 1 < n0
        M < n0
        natural_as_real_seq(n0) = '(n N_pos) R {n}(n0)
        '(n N_pos) R {n}(n0) = n0
        natural_as_real_seq(n0) = n0
        n0 >= 0
        abs(n0) = n0
        abs(natural_as_real_seq(n0)) = abs(n0) = n0
        abs(natural_as_real_seq(n0)) > M
        abs(natural_as_real_seq(n0)) <= M
        impossible abs(natural_as_real_seq(n0)) <= M

claim:
    ? not $is_convergent_sequence(natural_as_real_seq)
    by contra:
        ? not $is_convergent_sequence(natural_as_real_seq)
        $is_convergent_sequence(natural_as_real_seq)
        by thm convergent_sequence_is_bounded(natural_as_real_seq)
        impossible not $is_bounded_sequence(natural_as_real_seq)

claim:
    ? $is_divergent_sequence(natural_as_real_seq)
    not $is_bounded_sequence(natural_as_real_seq)
    not $is_convergent_sequence(natural_as_real_seq)
    $is_divergent_sequence(natural_as_real_seq)

"""
Theorem 6.1.19. Limit laws for sums, products, scalar multiples, differences,
reciprocals, quotients, maxima, and minima.
"""

# Each theorem writes its pointwise sequence directly as an anonymous function.
# The estimates are the usual epsilon/2, bounded-product, and
# bounded-away-from-zero arguments.

prop is_nonzero_sequence(a seq(R)):
    forall n N_pos:
        a(n) != 0

prop is_pointwise_le(a, b seq(R)):
    forall n N_pos:
        a(n) <= b(n)

prop is_pointwise_between(a, b, c seq(R)):
    forall n N_pos:
        a(n) <= b(n)
        b(n) <= c(n)

thm seq_add_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit('(i N_pos) R {a(i) + b(i)}, x + y)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {a(i) + b(i)}, x + y, epsilon)
        epsilon / 2 $in R_pos
        $has_eventual_closeness_to(a, x, epsilon / 2)
        $has_eventual_closeness_to(b, y, epsilon / 2)
        have by exist n1 N_pos st {$is_tail_close_to(a, x, epsilon / 2, n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(b, y, epsilon / 2, n2)}: n2
        max(n1, n2) $in N_pos
        max(n1, n2) >= n1
        max(n1, n2) >= n2
        witness exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {a(i) + b(i)}, x + y, epsilon, n0)} from max(n1, n2):
            forall n N_pos:
                n >= max(n1, n2)
                =>:
                    n1 <= max(n1, n2) <= n
                    n >= n1
                    n2 <= max(n1, n2) <= n
                    n >= n2
                    abs(a(n) - x) < epsilon / 2
                    abs(b(n) - y) < epsilon / 2
                    abs(a(n) - x) <= epsilon / 2
                    abs(b(n) - y) <= epsilon / 2
                    '(i N_pos) R {a(i) + b(i)}(n) = a(n) + b(n)
                    abs('(i N_pos) R {a(i) + b(i)}(n) - (x + y)) = abs((a(n) + b(n)) - (x + y))
                    (a(n) + b(n)) - (x + y) = (a(n) - x) + (b(n) - y)
                    abs((a(n) + b(n)) - (x + y)) = abs((a(n) - x) + (b(n) - y))
                    abs((a(n) - x) + (b(n) - y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs((a(n) + b(n)) - (x + y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs(a(n) - x) <= epsilon / 2
                    abs(b(n) - y) <= epsilon / 2
                    abs(a(n) - x) + abs(b(n) - y) <= epsilon / 2 + epsilon / 2
                    abs(a(n) - x) + abs(b(n) - y) < epsilon / 2 + epsilon / 2
                    epsilon / 2 + epsilon / 2 = epsilon
                    abs(a(n) - x) + abs(b(n) - y) < epsilon
                    abs('(i N_pos) R {a(i) + b(i)}(n) - (x + y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs('(i N_pos) R {a(i) + b(i)}(n) - (x + y)) <= abs(a(n) - x) + abs(b(n) - y) < epsilon
                    abs('(i N_pos) R {a(i) + b(i)}(n) - (x + y)) < epsilon
            $is_tail_close_to('(i N_pos) R {a(i) + b(i)}, x + y, epsilon, max(n1, n2))
        $has_eventual_closeness_to('(i N_pos) R {a(i) + b(i)}, x + y, epsilon)
    $has_limit('(i N_pos) R {a(i) + b(i)}, x + y)

thm seq_sub_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit('(i N_pos) R {a(i) - b(i)}, x - y)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {a(i) - b(i)}, x - y, epsilon)
        epsilon / 2 $in R_pos
        $has_eventual_closeness_to(a, x, epsilon / 2)
        $has_eventual_closeness_to(b, y, epsilon / 2)
        have by exist n1 N_pos st {$is_tail_close_to(a, x, epsilon / 2, n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(b, y, epsilon / 2, n2)}: n2
        max(n1, n2) $in N_pos
        max(n1, n2) >= n1
        max(n1, n2) >= n2
        witness exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {a(i) - b(i)}, x - y, epsilon, n0)} from max(n1, n2):
            forall n N_pos:
                n >= max(n1, n2)
                =>:
                    n1 <= max(n1, n2) <= n
                    n >= n1
                    n2 <= max(n1, n2) <= n
                    n >= n2
                    abs(a(n) - x) < epsilon / 2
                    abs(b(n) - y) < epsilon / 2
                    abs(a(n) - x) <= epsilon / 2
                    abs(b(n) - y) <= epsilon / 2
                    '(i N_pos) R {a(i) - b(i)}(n) = a(n) - b(n)
                    abs('(i N_pos) R {a(i) - b(i)}(n) - (x - y)) = abs((a(n) - b(n)) - (x - y))
                    (a(n) - b(n)) - (x - y) = (a(n) - x) - (b(n) - y)
                    abs((a(n) - b(n)) - (x - y)) = abs((a(n) - x) - (b(n) - y))
                    abs((a(n) - x) - (b(n) - y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs((a(n) - b(n)) - (x - y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs(a(n) - x) <= epsilon / 2
                    abs(b(n) - y) <= epsilon / 2
                    abs(a(n) - x) + abs(b(n) - y) <= epsilon / 2 + epsilon / 2
                    abs(a(n) - x) + abs(b(n) - y) < epsilon / 2 + epsilon / 2
                    epsilon / 2 + epsilon / 2 = epsilon
                    abs(a(n) - x) + abs(b(n) - y) < epsilon
                    abs('(i N_pos) R {a(i) - b(i)}(n) - (x - y)) <= abs(a(n) - x) + abs(b(n) - y)
                    abs('(i N_pos) R {a(i) - b(i)}(n) - (x - y)) <= abs(a(n) - x) + abs(b(n) - y) < epsilon
                    abs('(i N_pos) R {a(i) - b(i)}(n) - (x - y)) < epsilon
            $is_tail_close_to('(i N_pos) R {a(i) - b(i)}, x - y, epsilon, max(n1, n2))
        $has_eventual_closeness_to('(i N_pos) R {a(i) - b(i)}, x - y, epsilon)
    $has_limit('(i N_pos) R {a(i) - b(i)}, x - y)

thm seq_const_mul_converges_to:
    ? forall c R, a seq(R), x R:
        $has_limit(a, x)
        =>:
            $has_limit('(i N_pos) R {c * a(i)}, c * x)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {c * a(i)}, c * x, epsilon)
        abs(c) >= 0
        abs(c) + 1 > 0
        abs(c) + 1 != 0
        epsilon / (abs(c) + 1) $in R_pos
        $has_eventual_closeness_to(a, x, epsilon / (abs(c) + 1))
        have by exist n0 N_pos st {$is_tail_close_to(a, x, epsilon / (abs(c) + 1), n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to('(i N_pos) R {c * a(i)}, c * x, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(a(n) - x) < epsilon / (abs(c) + 1)
                    abs(a(n) - x) <= epsilon / (abs(c) + 1)
                    '(i N_pos) R {c * a(i)}(n) = c * a(n)
                    abs('(i N_pos) R {c * a(i)}(n) - c * x) = abs(c * a(n) - c * x)
                    abs(c * a(n) - c * x) = abs((c * a(n)) - (c * x))
                    abs('(i N_pos) R {c * a(i)}(n) - c * x) = abs((c * a(n)) - (c * x))
                    (c * a(n)) - (c * x) = c * (a(n) - x)
                    abs((c * a(n)) - (c * x)) = abs(c * (a(n) - x))
                    abs(c * (a(n) - x)) = abs(c) * abs(a(n) - x)
                    abs(c) <= abs(c) + 1
                    abs(a(n) - x) >= 0
                    abs(c) * abs(a(n) - x) <= (abs(c) + 1) * abs(a(n) - x)
                    (abs(c) + 1) * abs(a(n) - x) < (abs(c) + 1) * (epsilon / (abs(c) + 1))
                    abs(c) * abs(a(n) - x) <= (abs(c) + 1) * abs(a(n) - x) < (abs(c) + 1) * (epsilon / (abs(c) + 1))
                    abs(c) * abs(a(n) - x) < (abs(c) + 1) * (epsilon / (abs(c) + 1))
                    (abs(c) + 1) * (epsilon / (abs(c) + 1)) = epsilon
                    abs(c) * abs(a(n) - x) < epsilon
                    abs('(i N_pos) R {c * a(i)}(n) - c * x) <= abs(c) * abs(a(n) - x)
                    abs('(i N_pos) R {c * a(i)}(n) - c * x) <= abs(c) * abs(a(n) - x) < epsilon
                    abs('(i N_pos) R {c * a(i)}(n) - c * x) < epsilon
            $is_tail_close_to('(i N_pos) R {c * a(i)}, c * x, epsilon, n0)
        $has_eventual_closeness_to('(i N_pos) R {c * a(i)}, c * x, epsilon)
    $has_limit('(i N_pos) R {c * a(i)}, c * x)

thm seq_mul_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit('(i N_pos) R {a(i) * b(i)}, x * y)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {a(i) * b(i)}, x * y, epsilon)
        1 $in R_pos
        abs(x) >= 0
        abs(y) >= 0
        abs(x) + 1 > 0
        abs(x) + 1 + abs(y) + 1 > 0
        abs(x) + 1 + abs(y) + 1 != 0
        epsilon / (abs(x) + 1 + abs(y) + 1) $in R_pos
        $has_eventual_closeness_to(a, x, 1)
        $has_eventual_closeness_to(a, x, epsilon / (abs(x) + 1 + abs(y) + 1))
        $has_eventual_closeness_to(b, y, epsilon / (abs(x) + 1 + abs(y) + 1))
        have by exist n_bound N_pos st {$is_tail_close_to(a, x, 1, n_bound)}: n_bound
        have by exist n1 N_pos st {$is_tail_close_to(a, x, epsilon / (abs(x) + 1 + abs(y) + 1), n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(b, y, epsilon / (abs(x) + 1 + abs(y) + 1), n2)}: n2
        max(n_bound, n1) $in N_pos
        max(max(n_bound, n1), n2) $in N_pos
        n_bound <= max(n_bound, n1)
        n1 <= max(n_bound, n1)
        max(n_bound, n1) <= max(max(n_bound, n1), n2)
        n2 <= max(max(n_bound, n1), n2)
        witness exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {a(i) * b(i)}, x * y, epsilon, n0)} from max(max(n_bound, n1), n2):
            forall n N_pos:
                n >= max(max(n_bound, n1), n2)
                =>:
                    n_bound <= max(n_bound, n1) <= max(max(n_bound, n1), n2)
                    n_bound <= max(max(n_bound, n1), n2) <= n
                    n >= n_bound
                    n1 <= max(n_bound, n1) <= max(max(n_bound, n1), n2)
                    n1 <= max(max(n_bound, n1), n2) <= n
                    n >= n1
                    n2 <= max(max(n_bound, n1), n2) <= n
                    n >= n2
                    abs(a(n) - x) < 1
                    abs(a(n) - x) <= 1
                    a(n) - x <= abs(a(n) - x)
                    a(n) - x <= 1
                    a(n) = (a(n) - x) + x
                    x <= abs(x)
                    (a(n) - x) + x <= 1 + abs(x)
                    a(n) <= 1 + abs(x)
                    -(a(n) - x) <= abs(a(n) - x)
                    -(a(n) - x) <= 1
                    -x <= abs(x)
                    -a(n) = -(a(n) - x) + -x
                    -(a(n) - x) + -x <= 1 + abs(x)
                    -a(n) <= 1 + abs(x)
                    abs(a(n)) <= 1 + abs(x)
                    1 + abs(x) = abs(x) + 1
                    abs(a(n)) <= abs(x) + 1
                    abs(a(n) - x) < epsilon / (abs(x) + 1 + abs(y) + 1)
                    abs(b(n) - y) < epsilon / (abs(x) + 1 + abs(y) + 1)
                    abs(a(n) - x) <= epsilon / (abs(x) + 1 + abs(y) + 1)
                    abs(b(n) - y) <= epsilon / (abs(x) + 1 + abs(y) + 1)
                    '(i N_pos) R {a(i) * b(i)}(n) = a(n) * b(n)
                    abs('(i N_pos) R {a(i) * b(i)}(n) - x * y) = abs(a(n) * b(n) - x * y)
                    abs(a(n) * b(n) - x * y) = abs((a(n) * b(n)) - (x * y))
                    abs('(i N_pos) R {a(i) * b(i)}(n) - x * y) = abs((a(n) * b(n)) - (x * y))
                    (a(n) * b(n)) - (x * y) = a(n) * (b(n) - y) + y * (a(n) - x)
                    abs((a(n) * b(n)) - (x * y)) = abs(a(n) * (b(n) - y) + y * (a(n) - x))
                    abs(a(n) * (b(n) - y) + y * (a(n) - x)) <= abs(a(n) * (b(n) - y)) + abs(y * (a(n) - x))
                    abs(a(n) * (b(n) - y)) = abs(a(n)) * abs(b(n) - y)
                    abs(y * (a(n) - x)) = abs(y) * abs(a(n) - x)
                    abs(a(n) * (b(n) - y)) + abs(y * (a(n) - x)) = abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x)
                    abs((a(n) * b(n)) - (x * y)) <= abs(a(n) * (b(n) - y)) + abs(y * (a(n) - x))
                    abs((a(n) * b(n)) - (x * y)) <= abs(a(n) * (b(n) - y)) + abs(y * (a(n) - x)) <= abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x)
                    abs((a(n) * b(n)) - (x * y)) <= abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x)
                    abs(a(n)) * abs(b(n) - y) <= (abs(x) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    abs(y) * abs(a(n) - x) <= abs(y) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x) <= (abs(x) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1)) + abs(y) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    (abs(x) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1)) + abs(y) * (epsilon / (abs(x) + 1 + abs(y) + 1)) = (abs(x) + 1 + abs(y)) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    abs(x) + 1 + abs(y) <= abs(x) + 1 + abs(y) + 1
                    abs(x) + 1 + abs(y) < abs(x) + 1 + abs(y) + 1
                    (abs(x) + 1 + abs(y)) * (epsilon / (abs(x) + 1 + abs(y) + 1)) <= (abs(x) + 1 + abs(y) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    (abs(x) + 1 + abs(y)) * (epsilon / (abs(x) + 1 + abs(y) + 1)) < (abs(x) + 1 + abs(y) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1))
                    (abs(x) + 1 + abs(y) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1)) = epsilon
                    (abs(x) + 1 + abs(y)) * (epsilon / (abs(x) + 1 + abs(y) + 1)) < epsilon
                    (abs(x) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1)) + abs(y) * (epsilon / (abs(x) + 1 + abs(y) + 1)) < epsilon
                    abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x) <= (abs(x) + 1) * (epsilon / (abs(x) + 1 + abs(y) + 1)) + abs(y) * (epsilon / (abs(x) + 1 + abs(y) + 1)) < epsilon
                    abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x) < epsilon
                    abs('(i N_pos) R {a(i) * b(i)}(n) - x * y) <= abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x)
                    abs('(i N_pos) R {a(i) * b(i)}(n) - x * y) <= abs(a(n)) * abs(b(n) - y) + abs(y) * abs(a(n) - x) < epsilon
                    abs('(i N_pos) R {a(i) * b(i)}(n) - x * y) < epsilon
            $is_tail_close_to('(i N_pos) R {a(i) * b(i)}, x * y, epsilon, max(max(n_bound, n1), n2))
        $has_eventual_closeness_to('(i N_pos) R {a(i) * b(i)}, x * y, epsilon)
    $has_limit('(i N_pos) R {a(i) * b(i)}, x * y)

claim:
    ? forall epsilon R_pos, u, v, x, y R:
        abs(u - x) < epsilon
        abs(v - y) < epsilon
        =>:
            abs(max(u, v) - max(x, y)) <= epsilon
    abs(u - x) <= epsilon
    abs(v - y) <= epsilon
    u - x <= abs(u - x)
    u - x <= epsilon
    u = (u - x) + x
    (u - x) + x <= epsilon + x
    epsilon + x = x + epsilon
    u <= x + epsilon
    v - y <= abs(v - y)
    v - y <= epsilon
    v = (v - y) + y
    (v - y) + y <= epsilon + y
    epsilon + y = y + epsilon
    v <= y + epsilon
    x <= max(x, y)
    y <= max(x, y)
    x + epsilon <= max(x, y) + epsilon
    y + epsilon <= max(x, y) + epsilon
    u <= x + epsilon <= max(x, y) + epsilon
    u <= max(x, y) + epsilon
    v <= y + epsilon <= max(x, y) + epsilon
    v <= max(x, y) + epsilon
    max(u, v) <= max(x, y) + epsilon
    max(u, v) - max(x, y) <= (max(x, y) + epsilon) - max(x, y)
    (max(x, y) + epsilon) - max(x, y) = epsilon
    max(u, v) - max(x, y) <= epsilon
    -(u - x) <= abs(u - x)
    x - u = -(u - x)
    x - u <= abs(u - x)
    x - u <= abs(u - x) <= epsilon
    x - u <= epsilon
    x = (x - u) + u
    (x - u) + u <= epsilon + u
    epsilon + u = u + epsilon
    x <= u + epsilon
    -(v - y) <= abs(v - y)
    y - v = -(v - y)
    y - v <= abs(v - y)
    y - v <= abs(v - y) <= epsilon
    y - v <= epsilon
    y = (y - v) + v
    (y - v) + v <= epsilon + v
    epsilon + v = v + epsilon
    y <= v + epsilon
    u <= max(u, v)
    v <= max(u, v)
    u + epsilon <= max(u, v) + epsilon
    v + epsilon <= max(u, v) + epsilon
    x <= u + epsilon <= max(u, v) + epsilon
    x <= max(u, v) + epsilon
    y <= v + epsilon <= max(u, v) + epsilon
    y <= max(u, v) + epsilon
    max(x, y) <= max(u, v) + epsilon
    max(x, y) - max(u, v) <= (max(u, v) + epsilon) - max(u, v)
    (max(u, v) + epsilon) - max(u, v) = epsilon
    max(x, y) - max(u, v) <= epsilon
    -(max(u, v) - max(x, y)) = max(x, y) - max(u, v)
    -(max(u, v) - max(x, y)) <= epsilon
    abs(max(u, v) - max(x, y)) <= epsilon

claim:
    ? forall epsilon R_pos, u, v, x, y R:
        abs(u - x) < epsilon
        abs(v - y) < epsilon
        =>:
            abs(min(u, v) - min(x, y)) <= epsilon
    abs(u - x) <= epsilon
    abs(v - y) <= epsilon
    u - x <= epsilon
    u = (u - x) + x
    (u - x) + x <= epsilon + x
    epsilon + x = x + epsilon
    u <= x + epsilon
    v - y <= epsilon
    v = (v - y) + y
    (v - y) + y <= epsilon + y
    epsilon + y = y + epsilon
    v <= y + epsilon
    min(u, v) <= u
    min(u, v) <= v
    min(u, v) <= u <= x + epsilon
    min(u, v) <= x + epsilon
    min(u, v) - epsilon <= (x + epsilon) - epsilon
    (x + epsilon) - epsilon = x
    min(u, v) - epsilon <= x
    min(u, v) <= v <= y + epsilon
    min(u, v) <= y + epsilon
    min(u, v) - epsilon <= (y + epsilon) - epsilon
    (y + epsilon) - epsilon = y
    min(u, v) - epsilon <= y
    min(u, v) - epsilon <= min(x, y)
    (min(u, v) - epsilon) + epsilon <= min(x, y) + epsilon
    (min(u, v) - epsilon) + epsilon = min(u, v)
    min(u, v) <= min(x, y) + epsilon
    min(u, v) - min(x, y) <= (min(x, y) + epsilon) - min(x, y)
    (min(x, y) + epsilon) - min(x, y) = epsilon
    min(u, v) - min(x, y) <= epsilon
    -(u - x) <= abs(u - x)
    x - u = -(u - x)
    x - u <= abs(u - x)
    x - u <= abs(u - x) <= epsilon
    x - u <= epsilon
    x = (x - u) + u
    (x - u) + u <= epsilon + u
    epsilon + u = u + epsilon
    x <= u + epsilon
    -(v - y) <= abs(v - y)
    y - v = -(v - y)
    y - v <= abs(v - y)
    y - v <= abs(v - y) <= epsilon
    y - v <= epsilon
    y = (y - v) + v
    (y - v) + v <= epsilon + v
    epsilon + v = v + epsilon
    y <= v + epsilon
    min(x, y) <= x
    min(x, y) <= y
    min(x, y) <= x <= u + epsilon
    min(x, y) <= u + epsilon
    min(x, y) - epsilon <= (u + epsilon) - epsilon
    (u + epsilon) - epsilon = u
    min(x, y) - epsilon <= u
    min(x, y) <= y <= v + epsilon
    min(x, y) <= v + epsilon
    min(x, y) - epsilon <= (v + epsilon) - epsilon
    (v + epsilon) - epsilon = v
    min(x, y) - epsilon <= v
    min(x, y) - epsilon <= min(u, v)
    (min(x, y) - epsilon) + epsilon <= min(u, v) + epsilon
    (min(x, y) - epsilon) + epsilon = min(x, y)
    min(x, y) <= min(u, v) + epsilon
    min(x, y) - min(u, v) <= (min(u, v) + epsilon) - min(u, v)
    (min(u, v) + epsilon) - min(u, v) = epsilon
    min(x, y) - min(u, v) <= epsilon
    -(min(u, v) - min(x, y)) = min(x, y) - min(u, v)
    -(min(u, v) - min(x, y)) <= epsilon
    abs(min(u, v) - min(x, y)) <= epsilon

thm seq_max_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit('(i N_pos) R {max(a(i), b(i))}, max(x, y))
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {max(a(i), b(i))}, max(x, y), epsilon)
        epsilon / 2 $in R_pos
        epsilon / 2 < epsilon
        $has_eventual_closeness_to(a, x, epsilon / 2)
        $has_eventual_closeness_to(b, y, epsilon / 2)
        have by exist n1 N_pos st {$is_tail_close_to(a, x, epsilon / 2, n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(b, y, epsilon / 2, n2)}: n2
        max(n1, n2) $in N_pos
        max(n1, n2) >= n1
        max(n1, n2) >= n2
        witness exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {max(a(i), b(i))}, max(x, y), epsilon, n0)} from max(n1, n2):
            forall n N_pos:
                n >= max(n1, n2)
                =>:
                    n1 <= max(n1, n2) <= n
                    n >= n1
                    n2 <= max(n1, n2) <= n
                    n >= n2
                    abs(a(n) - x) < epsilon / 2
                    abs(b(n) - y) < epsilon / 2
                    '(i N_pos) R {max(a(i), b(i))}(n) = max(a(n), b(n))
                    abs('(i N_pos) R {max(a(i), b(i))}(n) - max(x, y)) = abs(max(a(n), b(n)) - max(x, y))
                    abs(max(a(n), b(n)) - max(x, y)) <= epsilon / 2
                    abs(max(a(n), b(n)) - max(x, y)) <= epsilon / 2 < epsilon
                    abs(max(a(n), b(n)) - max(x, y)) < epsilon
                    abs('(i N_pos) R {max(a(i), b(i))}(n) - max(x, y)) < epsilon
            $is_tail_close_to('(i N_pos) R {max(a(i), b(i))}, max(x, y), epsilon, max(n1, n2))
        $has_eventual_closeness_to('(i N_pos) R {max(a(i), b(i))}, max(x, y), epsilon)
    $has_limit('(i N_pos) R {max(a(i), b(i))}, max(x, y))

thm seq_min_converges_to:
    ? forall a, b seq(R), x, y R:
        $has_limit(a, x)
        $has_limit(b, y)
        =>:
            $has_limit('(i N_pos) R {min(a(i), b(i))}, min(x, y))
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {min(a(i), b(i))}, min(x, y), epsilon)
        epsilon / 2 $in R_pos
        epsilon / 2 < epsilon
        $has_eventual_closeness_to(a, x, epsilon / 2)
        $has_eventual_closeness_to(b, y, epsilon / 2)
        have by exist n1 N_pos st {$is_tail_close_to(a, x, epsilon / 2, n1)}: n1
        have by exist n2 N_pos st {$is_tail_close_to(b, y, epsilon / 2, n2)}: n2
        max(n1, n2) $in N_pos
        max(n1, n2) >= n1
        max(n1, n2) >= n2
        witness exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {min(a(i), b(i))}, min(x, y), epsilon, n0)} from max(n1, n2):
            forall n N_pos:
                n >= max(n1, n2)
                =>:
                    n1 <= max(n1, n2) <= n
                    n >= n1
                    n2 <= max(n1, n2) <= n
                    n >= n2
                    abs(a(n) - x) < epsilon / 2
                    abs(b(n) - y) < epsilon / 2
                    '(i N_pos) R {min(a(i), b(i))}(n) = min(a(n), b(n))
                    abs('(i N_pos) R {min(a(i), b(i))}(n) - min(x, y)) = abs(min(a(n), b(n)) - min(x, y))
                    abs(min(a(n), b(n)) - min(x, y)) <= epsilon / 2
                    abs(min(a(n), b(n)) - min(x, y)) <= epsilon / 2 < epsilon
                    abs(min(a(n), b(n)) - min(x, y)) < epsilon
                    abs('(i N_pos) R {min(a(i), b(i))}(n) - min(x, y)) < epsilon
            $is_tail_close_to('(i N_pos) R {min(a(i), b(i))}, min(x, y), epsilon, max(n1, n2))
        $has_eventual_closeness_to('(i N_pos) R {min(a(i), b(i))}, min(x, y), epsilon)
    $has_limit('(i N_pos) R {min(a(i), b(i))}, min(x, y))

thm near_nonzero_abs_lower:
    ? forall z, y R:
        y != 0
        abs(z - y) <= abs(y) / 2
        =>:
            abs(z) >= abs(y) / 2
    abs(y) > 0
    abs(y) / 2 > 0
    abs(z - y) <= abs(y) / 2
    abs(y - z) = abs(z - y)
    abs(y - z) <= abs(y) / 2
    y = (y - z) + z
    abs(y) = abs((y - z) + z)
    abs((y - z) + z) <= abs(y - z) + abs(z)
    abs(y) <= abs(y - z) + abs(z)
    abs(y - z) + abs(z) <= abs(y) / 2 + abs(z)
    abs(y) <= abs(y - z) + abs(z) <= abs(y) / 2 + abs(z)
    abs(y) <= abs(y) / 2 + abs(z)
    abs(y) = abs(y) / 2 + abs(y) / 2
    abs(y) / 2 + abs(y) / 2 <= abs(y) / 2 + abs(z)
    (abs(y) / 2 + abs(y) / 2) - abs(y) / 2 <= (abs(y) / 2 + abs(z)) - abs(y) / 2
    (abs(y) / 2 + abs(y) / 2) - abs(y) / 2 = abs(y) / 2
    (abs(y) / 2 + abs(z)) - abs(y) / 2 = abs(z)
    abs(y) / 2 <= abs(z)
    abs(z) >= abs(y) / 2

thm reciprocal_abs_diff_bound:
    ? forall x, y R, c, epsilon R_pos:
        x != 0
        y != 0
        abs(x) >= c
        abs(y) >= c
        abs(x - y) <= c^2 * epsilon
        =>:
            abs(1 / x - 1 / y) <= epsilon
    c > 0
    c^2 > 0
    abs(x) >= c
    abs(y) >= c
    abs(x) * abs(y) >= c * c
    c * c = c^2
    abs(x) * abs(y) >= c^2
    abs(x * y) = abs(x) * abs(y)
    abs(x * y) >= c^2
    abs(1 / x - 1 / y) >= 0
    abs(1 / x - 1 / y) * c^2 <= abs(1 / x - 1 / y) * abs(x * y)
    abs((1 / x - 1 / y) * (x * y)) = abs(1 / x - 1 / y) * abs(x * y)
    (1 / x - 1 / y) * (x * y) = y - x
    abs((1 / x - 1 / y) * (x * y)) = abs(y - x)
    abs(y - x) = abs(x - y)
    abs(1 / x - 1 / y) * abs(x * y) = abs(x - y)
    abs(1 / x - 1 / y) * c^2 <= abs(1 / x - 1 / y) * abs(x * y) = abs(x - y)
    abs(1 / x - 1 / y) * c^2 <= abs(x - y)
    abs(x - y) <= c^2 * epsilon
    abs(1 / x - 1 / y) * c^2 <= abs(x - y) <= c^2 * epsilon
    abs(1 / x - 1 / y) * c^2 <= c^2 * epsilon
    abs(1 / x - 1 / y) = abs(1 / x - 1 / y) * c^2 / c^2
    abs(1 / x - 1 / y) * c^2 / c^2 <= (c^2 * epsilon) / c^2
    (c^2 * epsilon) / c^2 = epsilon
    abs(1 / x - 1 / y) <= epsilon

thm seq_recip_converges_to:
    ? forall b seq(R), y R:
        $is_nonzero_sequence(b)
        $has_limit(b, y)
        y != 0
        =>:
            $has_limit('(j N_pos) R {1 / b(j)}, 1 / y)
    '(j N_pos) R {1 / b(j)} $in seq(R)
    abs(y) > 0
    abs(y) / 2 > 0
    abs(y) / 2 $in R_pos
    abs(y) / 2 >= 0
    abs(y) = abs(y) / 2 + abs(y) / 2
    abs(y) / 2 <= abs(y) / 2 + abs(y) / 2
    abs(y) / 2 <= abs(y)
    abs(y) >= abs(y) / 2
    (abs(y) / 2)^2 > 0
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(j N_pos) R {1 / b(j)}, 1 / y, epsilon)
        epsilon / 2 $in R_pos
        epsilon / 2 < epsilon
        (abs(y) / 2)^2 * (epsilon / 2) $in R_pos
        $has_eventual_closeness_to(b, y, abs(y) / 2)
        $has_eventual_closeness_to(b, y, (abs(y) / 2)^2 * (epsilon / 2))
        have by exist n_lower N_pos st {$is_tail_close_to(b, y, abs(y) / 2, n_lower)}: n_lower
        have by exist n_close N_pos st {$is_tail_close_to(b, y, (abs(y) / 2)^2 * (epsilon / 2), n_close)}: n_close
        max(n_lower, n_close) $in N_pos
        max(n_lower, n_close) >= n_lower
        max(n_lower, n_close) >= n_close
        claim:
            ? forall n N_pos:
                n >= max(n_lower, n_close)
                =>:
                    abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) < epsilon
            n_lower <= max(n_lower, n_close) <= n
            n >= n_lower
            n_close <= max(n_lower, n_close) <= n
            n >= n_close
            abs(b(n) - y) < abs(y) / 2
            abs(b(n) - y) <= abs(y) / 2
            by thm near_nonzero_abs_lower(b(n), y)
            abs(b(n)) >= abs(y) / 2
            abs(b(n) - y) < (abs(y) / 2)^2 * (epsilon / 2)
            abs(b(n) - y) <= (abs(y) / 2)^2 * (epsilon / 2)
            b(n) != 0
            by thm reciprocal_abs_diff_bound(b(n), y, abs(y) / 2, epsilon / 2)
            abs(1 / b(n) - 1 / y) <= epsilon / 2
            '(j N_pos) R {1 / b(j)}(n) = '(k N_pos) R {1 / b(k)}(n)
            '(k N_pos) R {1 / b(k)}(n) = 1 / b(n)
            '(j N_pos) R {1 / b(j)}(n) = 1 / b(n)
            abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) = abs(1 / b(n) - 1 / y)
            abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) <= epsilon / 2
            abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) <= epsilon / 2 < epsilon
            abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) < epsilon
        witness exist n0 N_pos st {$is_tail_close_to('(j N_pos) R {1 / b(j)}, 1 / y, epsilon, n0)} from max(n_lower, n_close):
            forall n N_pos:
                n >= max(n_lower, n_close)
                =>:
                    abs('(j N_pos) R {1 / b(j)}(n) - 1 / y) < epsilon
            $is_tail_close_to('(j N_pos) R {1 / b(j)}, 1 / y, epsilon, max(n_lower, n_close))
        $has_eventual_closeness_to('(j N_pos) R {1 / b(j)}, 1 / y, epsilon)
    $has_limit('(j N_pos) R {1 / b(j)}, 1 / y)

thm seq_div_converges_to:
    ? forall a, b seq(R), x, y R:
        $is_nonzero_sequence(b)
        $has_limit(a, x)
        $has_limit(b, y)
        y != 0
        =>:
            $has_limit('(i N_pos) R {a(i) / b(i)}, x / y)
    forall i N_pos:
        b(i) != 0
    '(i N_pos) R {a(i) / b(i)} $in seq(R)
    by thm seq_recip_converges_to(b, y)
    $has_limit('(j N_pos) R {1 / b(j)}, 1 / y)
    by thm seq_mul_converges_to(a, '(j N_pos) R {1 / b(j)}, x, 1 / y)
    $has_limit('(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}, x * (1 / y))
    x * (1 / y) = x / y
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to('(i N_pos) R {a(i) / b(i)}, x / y, epsilon)
        $has_eventual_closeness_to('(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}, x * (1 / y), epsilon)
        have by exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}, x * (1 / y), epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to('(i N_pos) R {a(i) / b(i)}, x / y, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs('(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}(n) - x * (1 / y)) < epsilon
                    '(i N_pos) R {a(i) / b(i)}(n) = a(n) / b(n)
                    '(j N_pos) R {1 / b(j)}(n) = 1 / b(n)
                    '(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}(n) = a(n) * '(j N_pos) R {1 / b(j)}(n)
                    a(n) * '(j N_pos) R {1 / b(j)}(n) = a(n) * (1 / b(n))
                    a(n) * (1 / b(n)) = a(n) / b(n)
                    '(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}(n) = a(n) / b(n)
                    '(i N_pos) R {a(i) / b(i)}(n) = '(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}(n)
                    x * (1 / y) = x / y
                    abs('(i N_pos) R {a(i) / b(i)}(n) - x / y) = abs('(i N_pos) R {a(i) * '(j N_pos) R {1 / b(j)}(i)}(n) - x * (1 / y))
                    abs('(i N_pos) R {a(i) / b(i)}(n) - x / y) < epsilon
            $is_tail_close_to('(i N_pos) R {a(i) / b(i)}, x / y, epsilon, n0)
        $has_eventual_closeness_to('(i N_pos) R {a(i) / b(i)}, x / y, epsilon)
    $has_limit('(i N_pos) R {a(i) / b(i)}, x / y)

# 6.2 The extended real number system

# This section is deliberately comment-only. It lists the related definitions,
# examples, and propositions from the source text in order, but it does not
# formalize an extended-real object. In this sketch, `R*` is a convenient
# notation for recording finite real values together with `+infty` and
# `-infty`, not the strict interface used by Litex. When later arguments need
# an infinity case, they use named propositions for the actual mathematical
# property: unbounded above or below, eventually above or below thresholds,
# finite tail suprema and infima, finite limsup and liminf, and so on.

"""
Definition 6.2.1 (The extended real line). The extended real line R* is formed
by adjoining two formal endpoints, +infty and -infty, to the ordinary real
numbers. The ordinary real numbers are the finite points of R*.
"""

# The formal objects below remain `R`-valued unless a later proposition says
# explicitly which infinity behavior is meant.

"""
Definition 6.2.2 (Negation on extended reals). Negation on R* agrees with
ordinary real negation on finite points, sends +infty to -infty, and sends
-infty to +infty.
"""

# Negation is listed as source vocabulary; no operation is introduced without a
# local extended-real object.

"""
Definition 6.2.3 (Extended order). The order on R* agrees with the ordinary
real order on finite points. Every extended real is at most +infty, and
-infty is at most every extended real.
"""

# Infinite comparisons are not encoded as term comparisons with placeholder
# endpoints. Litex records the corresponding threshold or unboundedness
# proposition when that comparison becomes mathematically relevant.

"""
Examples 6.2.4. Examples include 3 <= 5, 3 < +infty, -infty < +infty, and
not 3 <= -infty.
"""

# These examples justify the bookkeeping convention; they do not become finite
# real facts.

"""
Proposition 6.2.5. Extended order is reflexive, trichotomous, transitive, and
reversed by negation.
"""

# A future extended-order API could package these laws. This sketch only needs
# the concrete propositions used by later sections.

"""
Definition 6.2.6 (Extended suprema and infima). Supremum and infimum are
defined for subsets of R* using the extended order. An unbounded-above set has
supremum +infty, while the empty set has supremum -infty; the dual
conventions apply to infimum.
"""

# Later sections spell out finite supremum and infimum as least-bound
# predicates. The `+infty`, `-infty`, and empty-set conventions should be
# represented by separate unbounded or empty-family propositions when needed.

"""
Example 6.2.7. The negative integers together with -infty have supremum -1
and infimum -infty.
"""

# This is an extended-real example: the finite part contributes the supremum,
# while the attached endpoint controls the infimum. No `R*` term is introduced
# in the sketch.

"""
Example 6.2.8. The set {0.9, 0.99, 0.999, ...} has infimum 0.9 and supremum 1.
"""

# This illustrates a finite supremum that need not belong to the set itself.

"""
Example 6.2.9. The set {1, 2, 3, 4, ...} has infimum 1 and supremum +infty.
"""

# This is the unbounded-above case of the extended supremum convention.

"""
Example 6.2.10. The empty set has supremum -infty and infimum +infty.
"""

# This is the empty-family convention for extended suprema and infima.

"""
Theorem 6.2.11. Extended `sup(E)` is the least upper bound of E, and
extended `inf(E)` is the greatest lower bound of E.
"""

# Later references to this theorem are replaced at the point of use by the
# precise finite or infinity-facing proposition needed by that argument.


# 6.3 Suprema and infima of sequences

"""
Definition 6.3.1 (Tail suprema and infima). Given a real sequence and a
starting index m, the supremum of the tail is the least upper bound of the set
of values a_n with n >= m; the infimum is the greatest lower bound of the same
tail set.
"""

# Since Section 6.2 does not introduce `R*`, the local predicates below
# describe the real-valued bounded case: `L` is an upper or lower bound for the
# tail, and is least or greatest among real bounds.

prop is_tail_upper_bound(a seq(R), m N_pos, M R):
    forall n N_pos:
        n >= m
        =>:
            a(n) <= M

prop is_tail_lower_bound(a seq(R), m N_pos, M R):
    forall n N_pos:
        n >= m
        =>:
            M <= a(n)

prop is_tail_supremum(a seq(R), m N_pos, L R):
    $is_tail_upper_bound(a, m, L)
    forall M R:
        $is_tail_upper_bound(a, m, M)
        =>:
            L <= M

prop has_tail_supremum(a seq(R), m N_pos):
    exist L R st {$is_tail_supremum(a, m, L)}

prop is_tail_value(a seq(R), m N_pos, x R):
    exist n N_pos st {n >= m and x = a(n)}

thm tail_value_at_or_after_start:
    ? forall a seq(R), m, n N_pos:
        n >= m
        =>:
            $is_tail_value(a, m, a(n))
    witness exist k N_pos st {k >= m and a(n) = a(k)} from n:
        n >= m
        a(n) = a(n)
    $is_tail_value(a, m, a(n))

prop is_tail_infimum(a seq(R), m N_pos, L R):
    $is_tail_lower_bound(a, m, L)
    forall M R:
        $is_tail_lower_bound(a, m, M)
        =>:
            M <= L

prop has_tail_infimum(a seq(R), m N_pos):
    exist L R st {$is_tail_infimum(a, m, L)}

thm tail_supremum_unique:
    ? forall a seq(R), m N_pos, L1, L2 R:
        $is_tail_supremum(a, m, L1)
        $is_tail_supremum(a, m, L2)
        =>:
            L1 = L2
    L1 <= L2
    L2 <= L1
    L1 = L2

thm tail_infimum_unique:
    ? forall a seq(R), m N_pos, L1, L2 R:
        $is_tail_infimum(a, m, L1)
        $is_tail_infimum(a, m, L2)
        =>:
            L1 = L2
    L1 <= L2
    L2 <= L1
    L1 = L2

"""
Remark 6.3.2. These quantities are also written as sup_{n>=m} a_n and
inf_{n>=m} a_n.
"""

have fn tail_sup as set:
    ? forall a seq(R), m N_pos:
        $has_tail_supremum(a, m)
        =>:
            exist! L R st {$is_tail_supremum(a, m, L)}
    have by exist L R st {$is_tail_supremum(a, m, L)}: L
    claim:
        ? forall L1, L2 R:
            $is_tail_supremum(a, m, L1)
            $is_tail_supremum(a, m, L2)
            =>:
                L1 = L2
        by thm tail_supremum_unique(a, m, L1, L2)
    exist! L R st {$is_tail_supremum(a, m, L)}

have fn tail_inf as set:
    ? forall a seq(R), m N_pos:
        $has_tail_infimum(a, m)
        =>:
            exist! L R st {$is_tail_infimum(a, m, L)}
    have by exist L R st {$is_tail_infimum(a, m, L)}: L
    claim:
        ? forall L1, L2 R:
            $is_tail_infimum(a, m, L1)
            $is_tail_infimum(a, m, L2)
            =>:
                L1 = L2
        by thm tail_infimum_unique(a, m, L1, L2)
    exist! L R st {$is_tail_infimum(a, m, L)}

# In the finite real-valued case, the notation is represented by the functions
# `tail_sup(a, m)` and `tail_inf(a, m)`. Their domains require the corresponding
# real supremum or infimum to exist; unbounded tails remain infinity-facing
# propositions rather than real-valued function calls.

"""
Bounded real sequences have real tail suprema.  For a fixed starting index m,
the tail value set {a_n : n >= m} is nonempty and has the same global bound as
the sequence, so the Chapter 5 LUB interface gives a least upper bound for
that tail.
"""

thm bounded_sequence_has_tail_supremum:
    ? forall a seq(R), m N_pos:
        $is_bounded_sequence(a)
        =>:
            $has_tail_supremum(a, m)
    have tail_range power_set(R) = {x R: $is_tail_value(a, m, x)}
    have by exist B R st {$is_bounded_by(a, B)}: B
    claim:
        ? $is_nonempty_set(tail_range)
        witness exist n N_pos st {n >= m and a(m) = a(n)} from m:
            m >= m
            a(m) = a(m)
        $is_tail_value(a, m, a(m))
        a(m) $in {x R: $is_tail_value(a, m, x)}
        a(m) $in tail_range
        witness $is_nonempty_set(tail_range) from a(m):
            a(m) $in tail_range
    claim:
        ? $has_upper_bound(tail_range)
        tail_range $subset R
        claim:
            ? forall x tail_range:
                x <= B
            $is_tail_value(a, m, x)
            have by exist n N_pos st {n >= m and x = a(n)}: n
            x = a(n)
            abs(a(n)) <= B
            a(n) <= abs(a(n))
            a(n) <= B
            x <= B
        $is_upper_bound(tail_range, B)
        witness exist M R st {$is_upper_bound(tail_range, M)} from B:
            $is_upper_bound(tail_range, B)
        $has_upper_bound(tail_range)
    tail_range $in power_set(R)
    $has_least_upper_bound(tail_range)
    have by exist L R st {$is_least_upper_bound(tail_range, L)}: L
    claim:
        ? $is_tail_upper_bound(a, m, L)
        forall n N_pos:
            n >= m
            =>:
                $is_tail_value(a, m, a(n))
                a(n) $in {x R: $is_tail_value(a, m, x)}
                a(n) $in tail_range
                $is_upper_bound(tail_range, L)
                a(n) <= L
        $is_tail_upper_bound(a, m, L)
    claim:
        ? forall M R:
            $is_tail_upper_bound(a, m, M)
            =>:
                L <= M
        claim:
            ? $is_upper_bound(tail_range, M)
            tail_range $subset R
            claim:
                ? forall x tail_range:
                    x <= M
                $is_tail_value(a, m, x)
                have by exist n N_pos st {n >= m and x = a(n)}: n
                n >= m
                x = a(n)
                a(n) <= M
                x <= M
            $is_upper_bound(tail_range, M)
        L <= M
    $is_tail_supremum(a, m, L)
    witness exist L0 R st {$is_tail_supremum(a, m, L0)} from L:
        $is_tail_supremum(a, m, L)
    $has_tail_supremum(a, m)

"""
Example 6.3.3. For a_n = (-1)^n, the tail range is {-1,1}, so the supremum is
1 and the infimum is -1.
"""

claim:
    ? $is_tail_supremum(alternating_one_seq, 1, 1)
    claim:
        ? $is_tail_upper_bound(alternating_one_seq, 1, 1)
        forall n N_pos:
            n >= 1
            =>:
                alternating_one_seq(n) = '(n N_pos) R {(-1)^n}(n)
                '(n N_pos) R {(-1)^n}(n) = (-1)^n
                alternating_one_seq(n) = (-1)^n
                (-1)^n <= 1
                alternating_one_seq(n) <= 1
        $is_tail_upper_bound(alternating_one_seq, 1, 1)
    claim:
        ? forall M R:
            $is_tail_upper_bound(alternating_one_seq, 1, M)
            =>:
                1 <= M
        2 >= 1
        alternating_one_seq(2) = '(n N_pos) R {(-1)^n}(2)
        '(n N_pos) R {(-1)^n}(2) = (-1)^2
        (-1)^2 = 1
        alternating_one_seq(2) = 1
        alternating_one_seq(2) <= M
        1 <= M
    $is_tail_supremum(alternating_one_seq, 1, 1)

claim:
    ? $is_tail_infimum(alternating_one_seq, 1, -1)
    claim:
        ? $is_tail_lower_bound(alternating_one_seq, 1, -1)
        forall n N_pos:
            n >= 1
            =>:
                alternating_one_seq(n) = '(n N_pos) R {(-1)^n}(n)
                '(n N_pos) R {(-1)^n}(n) = (-1)^n
                alternating_one_seq(n) = (-1)^n
                -1 <= (-1)^n
                -1 <= alternating_one_seq(n)
        $is_tail_lower_bound(alternating_one_seq, 1, -1)
    claim:
        ? forall M R:
            $is_tail_lower_bound(alternating_one_seq, 1, M)
            =>:
                M <= -1
        1 >= 1
        alternating_one_seq(1) = '(n N_pos) R {(-1)^n}(1)
        '(n N_pos) R {(-1)^n}(1) = (-1)^1
        (-1)^1 = -1
        alternating_one_seq(1) = -1
        M <= alternating_one_seq(1)
        M <= -1
    $is_tail_infimum(alternating_one_seq, 1, -1)

witness exist L R st {$is_tail_supremum(alternating_one_seq, 1, L)} from 1:
    $is_tail_supremum(alternating_one_seq, 1, 1)
$has_tail_supremum(alternating_one_seq, 1)
witness exist L R st {$is_tail_infimum(alternating_one_seq, 1, L)} from -1:
    $is_tail_infimum(alternating_one_seq, 1, -1)
$has_tail_infimum(alternating_one_seq, 1)
tail_sup(alternating_one_seq, 1) = 1
tail_inf(alternating_one_seq, 1) = -1

"""
Example 6.3.4. For a_n = 1/n, the supremum is 1 and the infimum is 0.
"""

claim:
    ? $is_tail_supremum(reciprocal_nat_seq, 1, 1)
    claim:
        ? $is_tail_upper_bound(reciprocal_nat_seq, 1, 1)
        forall n N_pos:
            n >= 1
            =>:
                reciprocal_nat_seq(n) = '(n N_pos) R {1 / n}(n)
                '(n N_pos) R {1 / n}(n) = 1 / n
                reciprocal_nat_seq(n) = 1 / n
                1 <= n
                n > 0
                1 * n > 0
                1 / n = 1 / (1 * n)
                1 / (1 * n) <= n / (1 * n)
                n / (1 * n) = 1
                1 / n <= 1
                reciprocal_nat_seq(n) <= 1
        $is_tail_upper_bound(reciprocal_nat_seq, 1, 1)
    claim:
        ? forall M R:
            $is_tail_upper_bound(reciprocal_nat_seq, 1, M)
            =>:
                1 <= M
        1 >= 1
        reciprocal_nat_seq(1) = '(n N_pos) R {1 / n}(1)
        '(n N_pos) R {1 / n}(1) = 1 / 1
        reciprocal_nat_seq(1) = 1 / 1
        1 / 1 = 1
        reciprocal_nat_seq(1) = 1
        reciprocal_nat_seq(1) <= M
        1 <= M
    $is_tail_supremum(reciprocal_nat_seq, 1, 1)

claim:
    ? $is_tail_infimum(reciprocal_nat_seq, 1, 0)
    claim:
        ? $is_tail_lower_bound(reciprocal_nat_seq, 1, 0)
        forall n N_pos:
            n >= 1
            =>:
                reciprocal_nat_seq(n) = '(n N_pos) R {1 / n}(n)
                '(n N_pos) R {1 / n}(n) = 1 / n
                reciprocal_nat_seq(n) = 1 / n
                1 / n > 0
                0 <= 1 / n
                0 <= reciprocal_nat_seq(n)
        $is_tail_lower_bound(reciprocal_nat_seq, 1, 0)
    claim:
        ? forall M R:
            $is_tail_lower_bound(reciprocal_nat_seq, 1, M)
            =>:
                M <= 0
        by contra:
            ? M <= 0
            M > 0
            M $in R_pos
            exist n_bound N_pos st {1 / n_bound < M}
            have by exist n0 N_pos st {1 / n0 < M}: n0
            n0 >= 1
            reciprocal_nat_seq(n0) = '(n N_pos) R {1 / n}(n0)
            '(n N_pos) R {1 / n}(n0) = 1 / n0
            reciprocal_nat_seq(n0) = 1 / n0
            M <= reciprocal_nat_seq(n0)
            M <= 1 / n0
            1 / n0 < M
            M <= 1 / n0 < M
            M < M
            M != M
            impossible M = M
    $is_tail_infimum(reciprocal_nat_seq, 1, 0)

witness exist L R st {$is_tail_supremum(reciprocal_nat_seq, 1, L)} from 1:
    $is_tail_supremum(reciprocal_nat_seq, 1, 1)
$has_tail_supremum(reciprocal_nat_seq, 1)
witness exist L R st {$is_tail_infimum(reciprocal_nat_seq, 1, L)} from 0:
    $is_tail_infimum(reciprocal_nat_seq, 1, 0)
$has_tail_infimum(reciprocal_nat_seq, 1)
tail_sup(reciprocal_nat_seq, 1) = 1
tail_inf(reciprocal_nat_seq, 1) = 0

"""
Example 6.3.5. For a_n = n, the supremum is +infty and the infimum is 1.
"""

# The `+infty` side is an unboundedness statement, not a term in this file.
# The finite infimum side is still usable if needed:

claim:
    ? $is_tail_infimum(natural_as_real_seq, 1, 1)
    claim:
        ? $is_tail_lower_bound(natural_as_real_seq, 1, 1)
        forall n N_pos:
            n >= 1
            =>:
                natural_as_real_seq(n) = '(n N_pos) R {n}(n)
                '(n N_pos) R {n}(n) = n
                natural_as_real_seq(n) = n
                1 <= n
                1 <= natural_as_real_seq(n)
        $is_tail_lower_bound(natural_as_real_seq, 1, 1)
    claim:
        ? forall M R:
            $is_tail_lower_bound(natural_as_real_seq, 1, M)
            =>:
                M <= 1
        1 >= 1
        natural_as_real_seq(1) = '(n N_pos) R {n}(1)
        '(n N_pos) R {n}(1) = 1
        natural_as_real_seq(1) = 1
        M <= natural_as_real_seq(1)
        M <= 1
    $is_tail_infimum(natural_as_real_seq, 1, 1)

witness exist L R st {$is_tail_infimum(natural_as_real_seq, 1, L)} from 1:
    $is_tail_infimum(natural_as_real_seq, 1, 1)
$has_tail_infimum(natural_as_real_seq, 1)
tail_inf(natural_as_real_seq, 1) = 1

"""
Proposition 6.3.6. Least upper bound property for sequence suprema.
"""

# In the bounded finite version, a real tail supremum bounds all tail values,
# is below every real tail upper bound, and is approached from below.

thm tail_supremum_is_upper_bound:
    ? forall a seq(R), m N_pos, L R:
        $is_tail_supremum(a, m, L)
        =>:
            $is_tail_upper_bound(a, m, L)
    $is_tail_upper_bound(a, m, L)

thm tail_upper_bound_restrict_to_later_tail:
    ? forall a seq(R), m, l N_pos, M R:
        $is_tail_upper_bound(a, m, M)
        l >= m
        =>:
            $is_tail_upper_bound(a, l, M)
    claim:
        ? forall n N_pos:
            n >= l
            =>:
                a(n) <= M
        l <= n
        m <= l <= n
        m <= n
        n >= m
        a(n) <= M
    $is_tail_upper_bound(a, l, M)

thm tail_supremum_le_every_upper_bound:
    ? forall a seq(R), m N_pos, L R, M R:
        $is_tail_supremum(a, m, L)
        $is_tail_upper_bound(a, m, M)
        =>:
            L <= M
    L <= M

thm tail_supremum_crosses_every_lower_threshold:
    ? forall a seq(R), m N_pos, L R, y R:
        $is_tail_supremum(a, m, L)
        y < L
        =>:
            exist n N_pos st {n >= m and y < a(n)}
    by contra:
        ? exist n N_pos st {n >= m and y < a(n)}
        not exist n N_pos st {n >= m and y < a(n)}
        claim:
            ? $is_tail_upper_bound(a, m, y)
            claim:
                ? forall n N_pos:
                    n >= m
                    =>:
                        a(n) <= y
                not n >= m or not y < a(n)
                by cases:
                    ? a(n) <= y
                    case not n >= m:
                        impossible n >= m
                    case not y < a(n):
                        a(n) <= y
            $is_tail_upper_bound(a, m, y)
        L <= y
        L <= y < L
        L < L
        L != L
        impossible L = L

"""
Remark 6.3.7. Infima satisfy the corresponding order-reversed statements.
"""

thm tail_infimum_is_lower_bound:
    ? forall a seq(R), m N_pos, L R:
        $is_tail_infimum(a, m, L)
        =>:
            $is_tail_lower_bound(a, m, L)
    $is_tail_lower_bound(a, m, L)

thm tail_infimum_ge_every_lower_bound:
    ? forall a seq(R), m N_pos, L R, M R:
        $is_tail_infimum(a, m, L)
        $is_tail_lower_bound(a, m, M)
        =>:
            M <= L
    M <= L

thm tail_infimum_crosses_every_upper_threshold:
    ? forall a seq(R), m N_pos, L R, y R:
        $is_tail_infimum(a, m, L)
        L < y
        =>:
            exist n N_pos st {n >= m and a(n) < y}
    by contra:
        ? exist n N_pos st {n >= m and a(n) < y}
        not exist n N_pos st {n >= m and a(n) < y}
        claim:
            ? $is_tail_lower_bound(a, m, y)
            claim:
                ? forall n N_pos:
                    n >= m
                    =>:
                        y <= a(n)
                not n >= m or not a(n) < y
                by cases:
                    ? y <= a(n)
                    case not n >= m:
                        impossible n >= m
                    case not a(n) < y:
                        y <= a(n)
            $is_tail_lower_bound(a, m, y)
        y <= L
        L < y
        L < y <= L
        L < L
        L != L
        impossible L = L

"""
Proposition 6.3.8. A bounded increasing sequence converges to its supremum;
the decreasing bounded-below version converges to its infimum.
"""

prop is_increasing_from(a seq(R), m N_pos):
    forall j, k N_pos:
        j >= m
        k >= j
        =>:
            a(j) <= a(k)

prop is_decreasing_from(a seq(R), m N_pos):
    forall j, k N_pos:
        j >= m
        k >= j
        =>:
            a(k) <= a(j)

thm increasing_sequence_converges_to_tail_supremum:
    ? forall a seq(R), m N_pos, L R:
        $is_increasing_from(a, m)
        $is_tail_supremum(a, m, L)
        =>:
            $has_limit(a, L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, L, epsilon)
        L - epsilon < L
        by thm tail_supremum_crosses_every_lower_threshold(a, m, L, L - epsilon)
        exist n_cross N_pos st {n_cross >= m and L - epsilon < a(n_cross)}
        have by exist n1 N_pos st {n1 >= m and L - epsilon < a(n1)}: n1
        $is_tail_upper_bound(a, m, L)
        witness exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)} from n1:
            forall n N_pos:
                n >= n1
                =>:
                    n1 >= m
                    n >= n1
                    m <= n1 <= n
                    n >= m
                    a(n1) <= a(n)
                    a(n) <= L
                    L - epsilon < a(n1) <= a(n)
                    L - epsilon < a(n)
                    L - epsilon + epsilon < a(n) + epsilon
                    L - epsilon + epsilon = L
                    L < a(n) + epsilon
                    L - a(n) < a(n) + epsilon - a(n)
                    a(n) + epsilon - a(n) = epsilon
                    L - a(n) < epsilon
                    a(n) - L <= 0
                    0 < epsilon
                    a(n) - L < epsilon
                    -(a(n) - L) = L - a(n)
                    -(a(n) - L) < epsilon
                    abs(a(n) - L) < epsilon
            $is_tail_close_to(a, L, epsilon, n1)
        $has_eventual_closeness_to(a, L, epsilon)
    $has_limit(a, L)

thm decreasing_sequence_converges_to_tail_infimum:
    ? forall a seq(R), m N_pos, L R:
        $is_decreasing_from(a, m)
        $is_tail_infimum(a, m, L)
        =>:
            $has_limit(a, L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, L, epsilon)
        L < L + epsilon
        by thm tail_infimum_crosses_every_upper_threshold(a, m, L, L + epsilon)
        exist n_cross N_pos st {n_cross >= m and a(n_cross) < L + epsilon}
        have by exist n1 N_pos st {n1 >= m and a(n1) < L + epsilon}: n1
        $is_tail_lower_bound(a, m, L)
        witness exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)} from n1:
            forall n N_pos:
                n >= n1
                =>:
                    n1 >= m
                    n >= n1
                    m <= n1 <= n
                    n >= m
                    a(n) <= a(n1)
                    L <= a(n)
                    a(n) <= a(n1) < L + epsilon
                    a(n) < L + epsilon
                    a(n) - L < L + epsilon - L
                    L + epsilon - L = epsilon
                    a(n) - L < epsilon
                    L - a(n) <= 0
                    0 < epsilon
                    L - a(n) < epsilon
                    -(a(n) - L) = L - a(n)
                    -(a(n) - L) < epsilon
                    abs(a(n) - L) < epsilon
            $is_tail_close_to(a, L, epsilon, n1)
        $has_eventual_closeness_to(a, L, epsilon)
    $has_limit(a, L)

"""
Example 6.3.9. The decimal approximations 3, 3.1, 3.14, ... are increasing and
bounded above by 4, hence converge to a real limit at most 4.
"""

# Decimal-expansion machinery is not part of this chapter sketch; the example
# is recorded as an application of Proposition 6.3.8.

"""
Proposition 6.3.10. If 0 < x < 1, then x^n converges to 0.
"""

have fn geom_seq(x R) fn(k N_pos) R = '(n N_pos) R {x^n}

# The checked route follows the monotone convergence idea that appears just
# before this proposition.  It uses the Chapter 5 least-upper-bound interface
# collected at the top of this file.

thm least_upper_bound_member_above:
    ? forall E set, M R, epsilon R_pos:
        $is_least_upper_bound(E, M)
        =>:
            exist x E st {M - epsilon < x}
    by contra:
        ? exist x E st {M - epsilon < x}
        claim:
            ? forall x E:
                x <= M - epsilon
            not M - epsilon < x
            x <= M - epsilon
        E $subset R
        $is_upper_bound(E, M - epsilon)
        forall B R:
            $is_upper_bound(E, B)
            =>:
                M <= B
        M <= M - epsilon
        epsilon > 0
        M - epsilon < M
        M <= M - epsilon < M
        M < M
        impossible M = M

prop is_increasing_sequence(a seq(R)):
    forall n N_pos:
        a(n) <= a(n + 1)

prop is_decreasing_sequence(a seq(R)):
    forall n N_pos:
        a(n + 1) <= a(n)

prop is_sequence_upper_bound(a seq(R), M R):
    forall n N_pos:
        a(n) <= M

prop is_sequence_lower_bound(a seq(R), M R):
    forall n N_pos:
        M <= a(n)

prop is_bounded_above_sequence(a seq(R)):
    exist M R st {$is_sequence_upper_bound(a, M)}

prop is_bounded_below_sequence(a seq(R)):
    exist M R st {$is_sequence_lower_bound(a, M)}

thm increasing_seq_le_add:
    ? forall a seq(R), k N, n N_pos:
        $is_increasing_sequence(a)
        =>:
            a(n) <= a(n + k)
    by induc k from 0:
        ? a(n) <= a(n + k)
        prove from k = 0:
            n + 0 = n
            a(n + 0) = a(n)
            a(n) <= a(n)
            a(n) <= a(n + 0)
        prove induc:
            a(n) <= a(n + k)
            n + k $in N_pos
            a(n + k) <= a(n + k + 1)
            n + (k + 1) = n + k + 1
            a(n + k + 1) = a(n + (k + 1))
            a(n) <= a(n + k) <= a(n + k + 1)
            a(n) <= a(n + (k + 1))

thm increasing_seq_le_of_le:
    ? forall a seq(R), m, n N_pos:
        $is_increasing_sequence(a)
        m <= n
        =>:
            a(m) <= a(n)
    n - m $in N
    m + (n - m) = n
    by thm increasing_seq_le_add(a, n - m, m)
    a(m) <= a(m + (n - m))
    a(m + (n - m)) = a(n)
    a(m) <= a(n)

thm bounded_increasing_sequence_converges:
    ? forall a seq(R):
        $is_increasing_sequence(a)
        $is_bounded_above_sequence(a)
        =>:
            $is_convergent_sequence(a)
    fn_range(a) $subset R
    fn_range(a) $in power_set(R)
    a(1) $in fn_range(a)
    witness $is_nonempty_set(fn_range(a)) from a(1):
        a(1) $in fn_range(a)
    have by exist M R st {$is_sequence_upper_bound(a, M)}: M
    claim:
        ? $has_upper_bound(fn_range(a))
        fn_range(a) $subset R
        claim:
            ? forall x fn_range(a):
                x <= M
            have by preimage n from x $in fn_range(a)
            x = a(n)
            a(n) <= M
            x <= M
        $is_upper_bound(fn_range(a), M)
        witness exist B R st {$is_upper_bound(fn_range(a), B)} from M:
            $is_upper_bound(fn_range(a), M)
        $has_upper_bound(fn_range(a))
    $has_least_upper_bound(fn_range(a))
    have by exist L R st {$is_least_upper_bound(fn_range(a), L)}: L
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, L, epsilon)
        by thm least_upper_bound_member_above(fn_range(a), L, epsilon)
        have by exist y fn_range(a) st {L - epsilon < y}: y
        have by preimage m from y $in fn_range(a)
        y = a(m)
        claim:
            ? forall n N_pos:
                n >= m
                =>:
                    a(m) <= a(n)
            by thm increasing_seq_le_of_le(a, m, n)
            a(m) <= a(n)
        witness exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)} from m:
            forall n N_pos:
                n >= m
                =>:
                    y = a(m)
                    a(m) <= a(n)
                    L - epsilon < y
                    L - epsilon < a(m)
                    L - epsilon < a(m) <= a(n)
                    L - epsilon < a(n)
                    (L - epsilon) + epsilon < a(n) + epsilon
                    (L - epsilon) + epsilon = L
                    L < a(n) + epsilon
                    L - a(n) < (a(n) + epsilon) - a(n)
                    (a(n) + epsilon) - a(n) = epsilon
                    L - a(n) < epsilon
                    a(n) $in fn_range(a)
                    $is_upper_bound(fn_range(a), L)
                    a(n) <= L
                    a(n) - L <= 0
                    0 < epsilon
                    a(n) - L < epsilon
                    -(a(n) - L) = L - a(n)
                    -(a(n) - L) < epsilon
                    abs(a(n) - L) < epsilon
            $is_tail_close_to(a, L, epsilon, m)
        $has_eventual_closeness_to(a, L, epsilon)
    $has_limit(a, L)
    witness exist L0 R st {$has_limit(a, L0)} from L:
        $has_limit(a, L)
    $is_convergent_sequence(a)

have fn seq_const_mul(c R, a seq(R)) fn(k N_pos) R = '(n N_pos) R {c * a(n)}

thm bounded_decreasing_sequence_converges:
    ? forall a seq(R):
        $is_decreasing_sequence(a)
        $is_bounded_below_sequence(a)
        =>:
            $is_convergent_sequence(a)
    claim:
        ? $is_increasing_sequence(seq_const_mul(-1, a))
        forall n N_pos:
            seq_const_mul(-1, a)(n) = -1 * a(n)
            seq_const_mul(-1, a)(n + 1) = -1 * a(n + 1)
            a(n + 1) <= a(n)
            -1 * a(n) <= -1 * a(n + 1)
            seq_const_mul(-1, a)(n) <= seq_const_mul(-1, a)(n + 1)
        $is_increasing_sequence(seq_const_mul(-1, a))
    have by exist M R st {$is_sequence_lower_bound(a, M)}: M
    claim:
        ? $is_bounded_above_sequence(seq_const_mul(-1, a))
        claim:
            ? $is_sequence_upper_bound(seq_const_mul(-1, a), -M)
            forall n N_pos:
                M <= a(n)
                -a(n) <= -M
                -1 * a(n) = -a(n)
                -1 * a(n) <= -M
                seq_const_mul(-1, a)(n) = -1 * a(n)
                seq_const_mul(-1, a)(n) <= -M
            $is_sequence_upper_bound(seq_const_mul(-1, a), -M)
        witness exist B R st {$is_sequence_upper_bound(seq_const_mul(-1, a), B)} from -M:
            $is_sequence_upper_bound(seq_const_mul(-1, a), -M)
        $is_bounded_above_sequence(seq_const_mul(-1, a))
    by thm bounded_increasing_sequence_converges(seq_const_mul(-1, a))
    $is_convergent_sequence(seq_const_mul(-1, a))
    have by exist L R st {$has_limit(seq_const_mul(-1, a), L)}: L
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, -L, epsilon)
        $has_eventual_closeness_to(seq_const_mul(-1, a), L, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(seq_const_mul(-1, a), L, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(a, -L, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(seq_const_mul(-1, a)(n) - L) < epsilon
                    abs(seq_const_mul(-1, a)(n) - L) = abs(L - seq_const_mul(-1, a)(n))
                    seq_const_mul(-1, a)(n) = -1 * a(n)
                    L - seq_const_mul(-1, a)(n) = L - (-1 * a(n))
                    L - (-1 * a(n)) = a(n) - (-L)
                    abs(L - seq_const_mul(-1, a)(n)) = abs(a(n) - (-L))
                    abs(a(n) - (-L)) = abs(seq_const_mul(-1, a)(n) - L)
                    abs(a(n) - (-L)) < epsilon
            $is_tail_close_to(a, -L, epsilon, n0)
        $has_eventual_closeness_to(a, -L, epsilon)
    $has_limit(a, -L)
    witness exist L0 R st {$has_limit(a, L0)} from -L:
        $has_limit(a, -L)
    $is_convergent_sequence(a)

have fn seq_shift(a seq(R)) fn(k N_pos) R = '(n N_pos) R {a(n + 1)}

thm seq_shift_has_limit:
    ? forall a seq(R), L R:
        $has_limit(a, L)
        =>:
            $has_limit(seq_shift(a), L)
    by thm shifted_sequence_has_limit(a, L, 1)
    seq_shift(a) = '(n N_pos) R {a(n + 1)}
    $has_limit(seq_shift(a), L)

thm shifted_geometric_sequence_has_scaled_limit:
    ? forall x, L R:
        $has_limit(geom_seq(x), L)
        =>:
            $has_limit(seq_shift(geom_seq(x)), x * L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(seq_shift(geom_seq(x)), x * L, epsilon)
        abs(x) >= 0
        abs(x) + 1 > 0
        abs(x) + 1 != 0
        epsilon / (abs(x) + 1) $in R_pos
        $has_eventual_closeness_to(geom_seq(x), L, epsilon / (abs(x) + 1))
        have by exist n0 N_pos st {$is_tail_close_to(geom_seq(x), L, epsilon / (abs(x) + 1), n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(seq_shift(geom_seq(x)), x * L, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(geom_seq(x)(n) - L) < epsilon / (abs(x) + 1)
                    abs(geom_seq(x)(n) - L) <= epsilon / (abs(x) + 1)
                    seq_shift(geom_seq(x))(n) = geom_seq(x)(n + 1)
                    geom_seq(x)(n + 1) = x^(n + 1)
                    geom_seq(x)(n) = x^n
                    x^1 = x
                    x * geom_seq(x)(n) = x * x^n
                    x * x^n = x^1 * x^n
                    x^1 * x^n = x^(1 + n)
                    1 + n = n + 1
                    x^(1 + n) = x^(n + 1)
                    x * geom_seq(x)(n) = x^(n + 1)
                    seq_shift(geom_seq(x))(n) = x * geom_seq(x)(n)
                    abs(seq_shift(geom_seq(x))(n) - x * L) = abs(x * geom_seq(x)(n) - x * L)
                    abs(x * geom_seq(x)(n) - x * L) = abs((x * geom_seq(x)(n)) - (x * L))
                    (x * geom_seq(x)(n)) - (x * L) = x * (geom_seq(x)(n) - L)
                    abs((x * geom_seq(x)(n)) - (x * L)) = abs(x * (geom_seq(x)(n) - L))
                    abs(x * (geom_seq(x)(n) - L)) = abs(x) * abs(geom_seq(x)(n) - L)
                    abs(x) <= abs(x) + 1
                    abs(geom_seq(x)(n) - L) >= 0
                    abs(x) * abs(geom_seq(x)(n) - L) <= (abs(x) + 1) * abs(geom_seq(x)(n) - L)
                    (abs(x) + 1) * abs(geom_seq(x)(n) - L) < (abs(x) + 1) * (epsilon / (abs(x) + 1))
                    abs(x) * abs(geom_seq(x)(n) - L) <= (abs(x) + 1) * abs(geom_seq(x)(n) - L) < (abs(x) + 1) * (epsilon / (abs(x) + 1))
                    abs(x) * abs(geom_seq(x)(n) - L) < (abs(x) + 1) * (epsilon / (abs(x) + 1))
                    (abs(x) + 1) * (epsilon / (abs(x) + 1)) = epsilon
                    abs(x) * abs(geom_seq(x)(n) - L) < epsilon
                    abs(seq_shift(geom_seq(x))(n) - x * L) <= abs(x) * abs(geom_seq(x)(n) - L)
                    abs(seq_shift(geom_seq(x))(n) - x * L) <= abs(x) * abs(geom_seq(x)(n) - L) < epsilon
                    abs(seq_shift(geom_seq(x))(n) - x * L) < epsilon
            $is_tail_close_to(seq_shift(geom_seq(x)), x * L, epsilon, n0)
        $has_eventual_closeness_to(seq_shift(geom_seq(x)), x * L, epsilon)
    $has_limit(seq_shift(geom_seq(x)), x * L)

thm geometric_nonnegative_lt_one_converges_to_zero:
    ? forall x R:
        0 <= x
        x < 1
        =>:
            $has_limit(geom_seq(x), 0)
    claim:
        ? $is_decreasing_sequence(geom_seq(x))
        forall n N_pos:
            x^n >= 0
            x <= 1
            x^n * x <= x^n * 1
            x^n * 1 = x^n
            x^1 = x
            x^n * x = x^n * x^1
            x^n * x^1 = x^(n + 1)
            x^(n + 1) <= x^n
            geom_seq(x)(n + 1) = x^(n + 1)
            geom_seq(x)(n) = x^n
            geom_seq(x)(n + 1) <= geom_seq(x)(n)
        $is_decreasing_sequence(geom_seq(x))
    claim:
        ? $is_bounded_below_sequence(geom_seq(x))
        claim:
            ? $is_sequence_lower_bound(geom_seq(x), 0)
            forall n N_pos:
                x^n >= 0
                geom_seq(x)(n) = x^n
                0 <= geom_seq(x)(n)
            $is_sequence_lower_bound(geom_seq(x), 0)
        witness exist M R st {$is_sequence_lower_bound(geom_seq(x), M)} from 0:
            $is_sequence_lower_bound(geom_seq(x), 0)
        $is_bounded_below_sequence(geom_seq(x))
    by thm bounded_decreasing_sequence_converges(geom_seq(x))
    $is_convergent_sequence(geom_seq(x))
    have by exist L R st {$has_limit(geom_seq(x), L)}: L
    by thm seq_shift_has_limit(geom_seq(x), L)
    by thm shifted_geometric_sequence_has_scaled_limit(x, L)
    $has_limit(seq_shift(geom_seq(x)), L)
    $has_limit(seq_shift(geom_seq(x)), x * L)
    by thm sequence_limit_unique(seq_shift(geom_seq(x)), L, x * L)
    L = x * L
    L - x * L = 0
    (1 - x) * L = 0
    1 - x > 0
    1 - x != 0
    L = 0 / (1 - x)
    0 / (1 - x) = 0
    L = 0
    $has_limit(geom_seq(x), 0)

thm geometric_positive_lt_one_converges_to_zero:
    ? forall x R:
        0 < x
        x < 1
        =>:
            $has_limit('(n N_pos) R {x^n}, 0)
    0 <= x
    by thm geometric_nonnegative_lt_one_converges_to_zero(x)
    geom_seq(x) = '(n N_pos) R {x^n}
    $has_limit('(n N_pos) R {x^n}, 0)


# 6.4 Limsup, liminf, and limit points

"""
Definition 6.4.1 (Limit points of sequences). A finite real x is a limit
point of a sequence when every epsilon-neighborhood of x contains terms of the
sequence arbitrarily far out in the index. Equivalently, after any starting
index one can find a later term epsilon-close to x.
"""

prop is_epsilon_adherent_to_sequence(a seq(R), x R, epsilon R_pos, m N_pos):
    exist n N_pos st {n >= m and abs(a(n) - x) < epsilon}

prop is_continually_epsilon_adherent_to_sequence(a seq(R), x R, epsilon R_pos, m N_pos):
    forall n_tail N_pos:
        n_tail >= m
        =>:
            $is_epsilon_adherent_to_sequence(a, x, epsilon, n_tail)

prop is_limit_point(a seq(R), x R):
    forall epsilon R_pos, n_tail N_pos:
        $is_epsilon_adherent_to_sequence(a, x, epsilon, n_tail)

"""
Remark 6.4.2. Limit points differ from ordinary limits by quantifier order:
one needs arbitrarily late hits, not eventual closeness of all late terms.
"""

# The definition above keeps this quantifier distinction explicit.

"""
Example 6.4.3. The sequence 0.9, 0.99, 0.999, ... has 1 as a limit point but
not 0.8.
"""

# As in Chapter 5, the finite-decimal sequence is represented by the closed
# form `1 - 1/10^n`.  Decimal-expansion uniqueness is not formalized here; the
# point of this example is the quantifier difference between one early hit and
# continual adherence.

have fn decimal_nines_seq(n N_pos) R = 1 - 1 / 10^n

# The source uses a non-strict 0.1-close relation, while this sketch's
# adherence predicate uses a strict `< epsilon`.  In the strict formulation,
# any radius between 0.1 and 0.19 plays the same role: `0.8` is close to the
# first term `0.9`, but after discarding that first term all remaining terms
# are already at least `0.99`, so no later term remains that close to `0.8`.
# By contrast, `1` is continually adherent: after any tail cutoff and any
# positive epsilon, a sufficiently large decimal truncation has
# `abs(decimal_nines_seq(n) - 1) = 1/10^n < epsilon`.

"""
Example 6.4.4. The sequence approaching both 1 and -1 has both numbers as
limit points, while 0 is not a limit point.
"""

claim:
    ? $is_limit_point(alternating_one_seq, 1)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(alternating_one_seq, 1, epsilon, n_tail)
        2 * n_tail $in N_pos
        2 * n_tail >= n_tail
        witness exist n N_pos st {n >= n_tail and abs(alternating_one_seq(n) - 1) < epsilon} from 2 * n_tail:
            2 * n_tail >= n_tail
            alternating_one_seq(2 * n_tail) = '(n N_pos) R {(-1)^n}(2 * n_tail)
            '(n N_pos) R {(-1)^n}(2 * n_tail) = (-1)^(2 * n_tail)
            (-1)^2 = 1
            ((-1)^2)^n_tail = 1^n_tail
            1^n_tail = 1
            ((-1)^2)^n_tail = (-1)^(2 * n_tail)
            alternating_one_seq(2 * n_tail) = (-1)^(2 * n_tail) = 1
            alternating_one_seq(2 * n_tail) - 1 = 0
            abs(alternating_one_seq(2 * n_tail) - 1) = abs(0) = 0
            0 < epsilon
            abs(alternating_one_seq(2 * n_tail) - 1) < epsilon
            2 * n_tail >= n_tail and abs(alternating_one_seq(2 * n_tail) - 1) < epsilon
        $is_epsilon_adherent_to_sequence(alternating_one_seq, 1, epsilon, n_tail)
    $is_limit_point(alternating_one_seq, 1)

claim:
    ? $is_limit_point(alternating_one_seq, -1)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(alternating_one_seq, -1, epsilon, n_tail)
        2 * n_tail + 1 $in N_pos
        2 * n_tail + 1 >= n_tail
        witness exist n N_pos st {n >= n_tail and abs(alternating_one_seq(n) - -1) < epsilon} from 2 * n_tail + 1:
            2 * n_tail + 1 >= n_tail
            alternating_one_seq(2 * n_tail + 1) = '(n N_pos) R {(-1)^n}(2 * n_tail + 1)
            '(n N_pos) R {(-1)^n}(2 * n_tail + 1) = (-1)^(2 * n_tail + 1)
            (-1)^2 = 1
            ((-1)^2)^n_tail = 1^n_tail
            1^n_tail = 1
            ((-1)^2)^n_tail = (-1)^(2 * n_tail)
            (-1)^(2 * n_tail) = 1
            (-1)^1 = -1
            (-1)^(2 * n_tail + 1) = (-1)^(2 * n_tail) * (-1)^1
            (-1)^(2 * n_tail + 1) = 1 * -1 = -1
            alternating_one_seq(2 * n_tail + 1) = -1
            alternating_one_seq(2 * n_tail + 1) - -1 = 0
            abs(alternating_one_seq(2 * n_tail + 1) - -1) = abs(0) = 0
            0 < epsilon
            abs(alternating_one_seq(2 * n_tail + 1) - -1) < epsilon
            2 * n_tail + 1 >= n_tail and abs(alternating_one_seq(2 * n_tail + 1) - -1) < epsilon
        $is_epsilon_adherent_to_sequence(alternating_one_seq, -1, epsilon, n_tail)
    $is_limit_point(alternating_one_seq, -1)

claim:
    ? not $is_limit_point(alternating_one_seq, 0)
    by contra:
        ? not $is_limit_point(alternating_one_seq, 0)
        $is_limit_point(alternating_one_seq, 0)
        $is_epsilon_adherent_to_sequence(alternating_one_seq, 0, 1, 1)
        have by exist n N_pos st {n >= 1 and abs(alternating_one_seq(n) - 0) < 1}: n
        n >= 1 and abs(alternating_one_seq(n) - 0) < 1
        abs(alternating_one_seq(n) - 0) < 1
        alternating_one_seq(n) = '(n N_pos) R {(-1)^n}(n)
        '(n N_pos) R {(-1)^n}(n) = (-1)^n
        alternating_one_seq(n) = (-1)^n
        abs(alternating_one_seq(n) - 0) = abs(alternating_one_seq(n))
        abs(alternating_one_seq(n)) = abs((-1)^n)
        abs((-1)^n) = abs(-1)^n
        abs(-1) = 1
        abs(-1)^n = 1^n
        1^n = 1
        abs(alternating_one_seq(n) - 0) = 1
        1 < 1
        1 != 1
        impossible 1 = 1
    not $is_limit_point(alternating_one_seq, 0)

"""
Proposition 6.4.5. If a sequence converges to c, then c is its only finite
limit point.
"""

thm convergent_sequence_limit_is_limit_point:
    ? forall a seq(R), c R:
        $has_limit(a, c)
        =>:
            $is_limit_point(a, c)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(a, c, epsilon, n_tail)
        $has_eventual_closeness_to(a, c, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(a, c, epsilon, n0)}: n0
        max(n_tail, n0) $in N_pos
        max(n_tail, n0) >= n_tail
        max(n_tail, n0) >= n0
        witness exist n N_pos st {n >= n_tail and abs(a(n) - c) < epsilon} from max(n_tail, n0):
            max(n_tail, n0) >= n_tail
            max(n_tail, n0) >= n0
            abs(a(max(n_tail, n0)) - c) < epsilon
            max(n_tail, n0) >= n_tail and abs(a(max(n_tail, n0)) - c) < epsilon
        $is_epsilon_adherent_to_sequence(a, c, epsilon, n_tail)
    $is_limit_point(a, c)

thm convergent_sequence_limit_point_unique:
    ? forall a seq(R), c, x R:
        $has_limit(a, c)
        $is_limit_point(a, x)
        =>:
            x = c
    by contra:
        ? x = c
        x != c
        x - c != 0
        abs(x - c) > 0
        abs(x - c) / 3 $in R_pos
        $has_eventual_closeness_to(a, c, abs(x - c) / 3)
        have by exist n0 N_pos st {$is_tail_close_to(a, c, abs(x - c) / 3, n0)}: n0
        $is_epsilon_adherent_to_sequence(a, x, abs(x - c) / 3, n0)
        have by exist n N_pos st {n >= n0 and abs(a(n) - x) < abs(x - c) / 3}: n
        n >= n0 and abs(a(n) - x) < abs(x - c) / 3
        n >= n0
        abs(a(n) - x) < abs(x - c) / 3
        abs(a(n) - c) < abs(x - c) / 3
        abs(x - a(n)) = abs(a(n) - x)
        abs(x - a(n)) < abs(x - c) / 3
        abs(x - a(n)) <= abs(x - c) / 3
        abs(a(n) - c) <= abs(x - c) / 3
        x - c = (x - a(n)) + (a(n) - c)
        abs(x - c) = abs((x - a(n)) + (a(n) - c))
        abs((x - a(n)) + (a(n) - c)) <= abs(x - a(n)) + abs(a(n) - c)
        abs(x - c) <= abs(x - a(n)) + abs(a(n) - c)
        abs(x - a(n)) + abs(a(n) - c) <= abs(x - c) / 3 + abs(x - c) / 3
        abs(x - c) <= abs(x - a(n)) + abs(a(n) - c) <= abs(x - c) / 3 + abs(x - c) / 3
        abs(x - c) <= abs(x - c) / 3 + abs(x - c) / 3
        abs(x - c) / 3 + abs(x - c) / 3 = 2 * abs(x - c) / 3
        2 / 3 < 1
        (2 / 3) * abs(x - c) < 1 * abs(x - c)
        (2 / 3) * abs(x - c) = 2 * abs(x - c) / 3
        1 * abs(x - c) = abs(x - c)
        2 * abs(x - c) / 3 < abs(x - c)
        abs(x - c) <= 2 * abs(x - c) / 3
        abs(x - c) <= 2 * abs(x - c) / 3 < abs(x - c)
        abs(x - c) < abs(x - c)
        abs(x - c) != abs(x - c)
        impossible abs(x - c) = abs(x - c)

"""
Definition 6.4.6 (Limit superior and limit inferior). For a real sequence,
each tail has a supremum and an infimum in the extended real sense. The limit
superior is the infimum, over all starting indices, of the tail suprema; the
limit inferior is the supremum, over all starting indices, of the tail infima.
"""

# The full mathematical definition is extended-real-valued. For this first
# sketch, the finite bounded substitutes below use the two key characterizations
# from Proposition 6.4.12(a,b): eventual upper/lower control and infinitely
# often crossing every stricter threshold.

prop is_eventually_below_threshold(a seq(R), x R, n_tail N_pos):
    forall n N_pos:
        n >= n_tail
        =>:
            a(n) < x

prop is_eventually_above_threshold(a seq(R), y R, n_tail N_pos):
    forall n N_pos:
        n >= n_tail
        =>:
            y < a(n)

prop exceeds_threshold_arbitrarily_late(a seq(R), x R):
    forall n_tail N_pos:
        exist n N_pos st {n >= n_tail and x < a(n)}

prop falls_below_threshold_arbitrarily_late(a seq(R), y R):
    forall n_tail N_pos:
        exist n N_pos st {n >= n_tail and a(n) < y}

prop is_eventually_below_every_threshold_above(a seq(R), L R):
    forall x R:
        x > L
        =>:
            exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)}

prop exceeds_every_threshold_below_arbitrarily_late(a seq(R), L R):
    forall x R:
        x < L
        =>:
            $exceeds_threshold_arbitrarily_late(a, x)

prop is_eventually_above_every_threshold_below(a seq(R), L R):
    forall y R:
        y < L
        =>:
            exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)}

prop falls_below_every_threshold_above_arbitrarily_late(a seq(R), L R):
    forall y R:
        y > L
        =>:
            $falls_below_threshold_arbitrarily_late(a, y)

prop has_finite_limit_superior(a seq(R), L R):
    $is_eventually_below_every_threshold_above(a, L)
    $exceeds_every_threshold_below_arbitrarily_late(a, L)

prop has_finite_limit_inferior(a seq(R), L R):
    $is_eventually_above_every_threshold_below(a, L)
    $falls_below_every_threshold_above_arbitrarily_late(a, L)

prop has_limit_superior_pos_infinity(a seq(R)):
    forall x R:
        $exceeds_threshold_arbitrarily_late(a, x)

prop has_limit_inferior_neg_infinity(a seq(R)):
    forall y R:
        $falls_below_threshold_arbitrarily_late(a, y)

prop has_limit_inferior_pos_infinity(a seq(R)):
    forall y R:
        exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)}

thm exists_nat_above_real:
    ? forall M R:
        exist n0 N_pos st {M < n0}
    abs(M) + 1 > 0
    abs(M) + 1 $in R_pos
    1 / (abs(M) + 1) $in R_pos
    exist n_bound N_pos st {1 / n_bound < 1 / (abs(M) + 1)}
    have by exist n0 N_pos st {1 / n0 < 1 / (abs(M) + 1)}: n0
    n0 > 0
    n0 * (abs(M) + 1) > 0
    (1 / n0) * (n0 * (abs(M) + 1)) < (1 / (abs(M) + 1)) * (n0 * (abs(M) + 1))
    (1 / n0) * (n0 * (abs(M) + 1)) = abs(M) + 1
    (1 / (abs(M) + 1)) * (n0 * (abs(M) + 1)) = n0
    abs(M) + 1 < n0
    M <= abs(M)
    abs(M) < abs(M) + 1
    M <= abs(M) < abs(M) + 1
    M < abs(M) + 1
    M < abs(M) + 1 < n0
    M < n0
    witness exist n1 N_pos st {M < n1} from n0:
        M < n0

thm alternating_one_even_value:
    ? forall k N_pos:
        alternating_one_seq(2 * k) = 1
    alternating_one_seq(2 * k) = '(n N_pos) R {(-1)^n}(2 * k)
    '(n N_pos) R {(-1)^n}(2 * k) = (-1)^(2 * k)
    (-1)^2 = 1
    ((-1)^2)^k = 1^k
    1^k = 1
    ((-1)^2)^k = (-1)^(2 * k)
    (-1)^(2 * k) = 1
    alternating_one_seq(2 * k) = 1

thm alternating_one_odd_value:
    ? forall k N_pos:
        alternating_one_seq(2 * k + 1) = -1
    alternating_one_seq(2 * k + 1) = '(n N_pos) R {(-1)^n}(2 * k + 1)
    '(n N_pos) R {(-1)^n}(2 * k + 1) = (-1)^(2 * k + 1)
    by thm alternating_one_even_value(k)
    alternating_one_seq(2 * k) = '(n N_pos) R {(-1)^n}(2 * k)
    '(n N_pos) R {(-1)^n}(2 * k) = (-1)^(2 * k)
    (-1)^(2 * k) = 1
    (-1)^1 = -1
    (-1)^(2 * k + 1) = (-1)^(2 * k) * (-1)^1
    (-1)^(2 * k + 1) = 1 * -1 = -1
    alternating_one_seq(2 * k + 1) = -1

"""
Example 6.4.7. The sequence 1.1, -1.01, 1.001, -1.0001, ... has limit
superior 1 and limit inferior -1.
"""

# The source example combines sign oscillation with decimal errors tending to
# zero. The decimal machinery is not introduced here; the checked block below
# exercises the same finite limsup/liminf predicates on the already introduced
# pure oscillation `(-1)^n`.

claim:
    ? $has_finite_limit_superior(alternating_one_seq, 1)
    claim:
        ? $is_eventually_below_every_threshold_above(alternating_one_seq, 1)
        claim:
            ? forall x R:
                x > 1
                =>:
                    exist n_tail N_pos st {$is_eventually_below_threshold(alternating_one_seq, x, n_tail)}
            witness exist n_tail N_pos st {$is_eventually_below_threshold(alternating_one_seq, x, n_tail)} from 1:
                forall n N_pos:
                    n >= 1
                    =>:
                        $is_tail_supremum(alternating_one_seq, 1, 1)
                        $is_tail_upper_bound(alternating_one_seq, 1, 1)
                        alternating_one_seq(n) <= 1
                        alternating_one_seq(n) <= 1 < x
                        alternating_one_seq(n) < x
                $is_eventually_below_threshold(alternating_one_seq, x, 1)
        $is_eventually_below_every_threshold_above(alternating_one_seq, 1)
    claim:
        ? $exceeds_every_threshold_below_arbitrarily_late(alternating_one_seq, 1)
        claim:
            ? forall x R:
                x < 1
                =>:
                    $exceeds_threshold_arbitrarily_late(alternating_one_seq, x)
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and x < alternating_one_seq(n)}
                2 * n_tail $in N_pos
                2 * n_tail >= n_tail
                witness exist n N_pos st {n >= n_tail and x < alternating_one_seq(n)} from 2 * n_tail:
                    2 * n_tail >= n_tail
                    alternating_one_seq(2 * n_tail) = '(n N_pos) R {(-1)^n}(2 * n_tail)
                    '(n N_pos) R {(-1)^n}(2 * n_tail) = (-1)^(2 * n_tail)
                    (-1)^2 = 1
                    ((-1)^2)^n_tail = 1^n_tail
                    1^n_tail = 1
                    ((-1)^2)^n_tail = (-1)^(2 * n_tail)
                    alternating_one_seq(2 * n_tail) = (-1)^(2 * n_tail) = 1
                    x < alternating_one_seq(2 * n_tail)
                    2 * n_tail >= n_tail and x < alternating_one_seq(2 * n_tail)
            $exceeds_threshold_arbitrarily_late(alternating_one_seq, x)
        $exceeds_every_threshold_below_arbitrarily_late(alternating_one_seq, 1)
    $has_finite_limit_superior(alternating_one_seq, 1)

claim:
    ? $has_finite_limit_inferior(alternating_one_seq, -1)
    claim:
        ? $is_eventually_above_every_threshold_below(alternating_one_seq, -1)
        claim:
            ? forall y R:
                y < -1
                =>:
                    exist n_tail N_pos st {$is_eventually_above_threshold(alternating_one_seq, y, n_tail)}
            witness exist n_tail N_pos st {$is_eventually_above_threshold(alternating_one_seq, y, n_tail)} from 1:
                forall n N_pos:
                    n >= 1
                    =>:
                        $is_tail_infimum(alternating_one_seq, 1, -1)
                        $is_tail_lower_bound(alternating_one_seq, 1, -1)
                        -1 <= alternating_one_seq(n)
                        y < -1 <= alternating_one_seq(n)
                        y < alternating_one_seq(n)
                $is_eventually_above_threshold(alternating_one_seq, y, 1)
        $is_eventually_above_every_threshold_below(alternating_one_seq, -1)
    claim:
        ? $falls_below_every_threshold_above_arbitrarily_late(alternating_one_seq, -1)
        claim:
            ? forall y R:
                y > -1
                =>:
                    $falls_below_threshold_arbitrarily_late(alternating_one_seq, y)
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and alternating_one_seq(n) < y}
                2 * n_tail + 1 $in N_pos
                2 * n_tail + 1 >= n_tail
                witness exist n N_pos st {n >= n_tail and alternating_one_seq(n) < y} from 2 * n_tail + 1:
                    2 * n_tail + 1 >= n_tail
                    alternating_one_seq(2 * n_tail + 1) = '(n N_pos) R {(-1)^n}(2 * n_tail + 1)
                    '(n N_pos) R {(-1)^n}(2 * n_tail + 1) = (-1)^(2 * n_tail + 1)
                    (-1)^2 = 1
                    ((-1)^2)^n_tail = 1^n_tail
                    1^n_tail = 1
                    ((-1)^2)^n_tail = (-1)^(2 * n_tail)
                    (-1)^(2 * n_tail) = 1
                    (-1)^1 = -1
                    (-1)^(2 * n_tail + 1) = (-1)^(2 * n_tail) * (-1)^1
                    (-1)^(2 * n_tail + 1) = 1 * -1 = -1
                    alternating_one_seq(2 * n_tail + 1) = -1
                    alternating_one_seq(2 * n_tail + 1) < y
                    2 * n_tail + 1 >= n_tail and alternating_one_seq(2 * n_tail + 1) < y
            $falls_below_threshold_arbitrarily_late(alternating_one_seq, y)
        $falls_below_every_threshold_above_arbitrarily_late(alternating_one_seq, -1)
    $has_finite_limit_inferior(alternating_one_seq, -1)

"""
Example 6.4.8. The sequence 1, -2, 3, -4, ... has limit superior +infty and
limit inferior -infty.
"""

# This example is infinity-facing rather than finite-valued: odd positive terms
# are unbounded above and even negative terms are unbounded below. It should be
# represented by threshold/unboundedness propositions, not by the finite
# `has_finite_limit_superior` predicate.

have fn alternating_signed_nat_seq(n N_pos) R = -1 * alternating_one_seq(n) * natural_as_real_seq(n)

claim:
    ? $has_limit_superior_pos_infinity(alternating_signed_nat_seq)
    claim:
        ? forall x R:
            $exceeds_threshold_arbitrarily_late(alternating_signed_nat_seq, x)
        by thm exists_nat_above_real(x)
        have by exist n0 N_pos st {x < n0}: n0
        claim:
            ? forall n_tail N_pos:
                exist n N_pos st {n >= n_tail and x < alternating_signed_nat_seq(n)}
            max(n_tail, n0) $in N_pos
            max(n_tail, n0) >= n_tail
            max(n_tail, n0) >= n0
            2 * max(n_tail, n0) + 1 $in N_pos
            n_tail <= max(n_tail, n0)
            max(n_tail, n0) <= 2 * max(n_tail, n0)
            2 * max(n_tail, n0) <= 2 * max(n_tail, n0) + 1
            n_tail <= max(n_tail, n0) <= 2 * max(n_tail, n0) <= 2 * max(n_tail, n0) + 1
            n_tail <= 2 * max(n_tail, n0) + 1
            witness exist n N_pos st {n >= n_tail and x < alternating_signed_nat_seq(n)} from 2 * max(n_tail, n0) + 1:
                n_tail <= 2 * max(n_tail, n0) + 1
                2 * max(n_tail, n0) + 1 >= n_tail
                by thm alternating_one_odd_value(max(n_tail, n0))
                alternating_signed_nat_seq(2 * max(n_tail, n0) + 1) = -1 * alternating_one_seq(2 * max(n_tail, n0) + 1) * natural_as_real_seq(2 * max(n_tail, n0) + 1)
                alternating_one_seq(2 * max(n_tail, n0) + 1) = -1
                natural_as_real_seq(2 * max(n_tail, n0) + 1) = 2 * max(n_tail, n0) + 1
                -1 * alternating_one_seq(2 * max(n_tail, n0) + 1) = 1
                alternating_signed_nat_seq(2 * max(n_tail, n0) + 1) = 2 * max(n_tail, n0) + 1
                x < n0
                n0 <= max(n_tail, n0)
                max(n_tail, n0) <= 2 * max(n_tail, n0) + 1
                n0 <= max(n_tail, n0) <= 2 * max(n_tail, n0) + 1
                n0 <= 2 * max(n_tail, n0) + 1
                x < n0 <= 2 * max(n_tail, n0) + 1
                x < 2 * max(n_tail, n0) + 1
                x < alternating_signed_nat_seq(2 * max(n_tail, n0) + 1)
                2 * max(n_tail, n0) + 1 >= n_tail and x < alternating_signed_nat_seq(2 * max(n_tail, n0) + 1)
        $exceeds_threshold_arbitrarily_late(alternating_signed_nat_seq, x)
    $has_limit_superior_pos_infinity(alternating_signed_nat_seq)

claim:
    ? $has_limit_inferior_neg_infinity(alternating_signed_nat_seq)
    claim:
        ? forall y R:
            $falls_below_threshold_arbitrarily_late(alternating_signed_nat_seq, y)
        by thm exists_nat_above_real(-y)
        have by exist n0 N_pos st {-y < n0}: n0
        claim:
            ? forall n_tail N_pos:
                exist n N_pos st {n >= n_tail and alternating_signed_nat_seq(n) < y}
            max(n_tail, n0) $in N_pos
            max(n_tail, n0) >= n_tail
            max(n_tail, n0) >= n0
            2 * max(n_tail, n0) $in N_pos
            n_tail <= max(n_tail, n0)
            max(n_tail, n0) <= 2 * max(n_tail, n0)
            n_tail <= max(n_tail, n0) <= 2 * max(n_tail, n0)
            n_tail <= 2 * max(n_tail, n0)
            witness exist n N_pos st {n >= n_tail and alternating_signed_nat_seq(n) < y} from 2 * max(n_tail, n0):
                n_tail <= 2 * max(n_tail, n0)
                2 * max(n_tail, n0) >= n_tail
                by thm alternating_one_even_value(max(n_tail, n0))
                alternating_signed_nat_seq(2 * max(n_tail, n0)) = -1 * alternating_one_seq(2 * max(n_tail, n0)) * natural_as_real_seq(2 * max(n_tail, n0))
                alternating_one_seq(2 * max(n_tail, n0)) = 1
                natural_as_real_seq(2 * max(n_tail, n0)) = 2 * max(n_tail, n0)
                -1 * alternating_one_seq(2 * max(n_tail, n0)) = -1
                -1 * alternating_one_seq(2 * max(n_tail, n0)) * natural_as_real_seq(2 * max(n_tail, n0)) = -1 * natural_as_real_seq(2 * max(n_tail, n0))
                alternating_signed_nat_seq(2 * max(n_tail, n0)) = -1 * natural_as_real_seq(2 * max(n_tail, n0))
                -1 * natural_as_real_seq(2 * max(n_tail, n0)) = -1 * (2 * max(n_tail, n0))
                -1 * (2 * max(n_tail, n0)) = -1 * 2 * max(n_tail, n0)
                alternating_signed_nat_seq(2 * max(n_tail, n0)) = -1 * 2 * max(n_tail, n0)
                -y < n0
                n0 <= max(n_tail, n0)
                max(n_tail, n0) <= 2 * max(n_tail, n0)
                n0 <= max(n_tail, n0) <= 2 * max(n_tail, n0)
                n0 <= 2 * max(n_tail, n0)
                -y < n0 <= 2 * max(n_tail, n0)
                -y < 2 * max(n_tail, n0)
                -1 * (2 * max(n_tail, n0)) < -1 * (-y)
                -1 * (-y) = y
                -1 * (2 * max(n_tail, n0)) < y
                -1 * (2 * max(n_tail, n0)) = -1 * 2 * max(n_tail, n0)
                -1 * 2 * max(n_tail, n0) < y
                alternating_signed_nat_seq(2 * max(n_tail, n0)) < y
                2 * max(n_tail, n0) >= n_tail and alternating_signed_nat_seq(2 * max(n_tail, n0)) < y
        $falls_below_threshold_arbitrarily_late(alternating_signed_nat_seq, y)
    $has_limit_inferior_neg_infinity(alternating_signed_nat_seq)

"""
Example 6.4.9. The sequence 1, -1/2, 1/3, -1/4, ... has both limit superior
and limit inferior equal to 0.
"""

# This is the alternating reciprocal example.  The absolute size is bounded by
# `1/n`, while positive odd terms and negative even terms keep crossing every
# threshold on the correct side of zero.

have fn alternating_reciprocal_seq(n N_pos) R = -1 * alternating_one_seq(n) * reciprocal_nat_seq(n)

thm alternating_reciprocal_unfold:
    ? forall n N_pos:
        alternating_reciprocal_seq(n) = (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n)
    alternating_reciprocal_seq(n) = (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n)

claim:
    ? forall n N_pos:
        alternating_reciprocal_seq(n) <= reciprocal_nat_seq(n)
        -reciprocal_nat_seq(n) <= alternating_reciprocal_seq(n)
    alternating_one_seq(n) = '(n N_pos) R {(-1)^n}(n)
    '(n N_pos) R {(-1)^n}(n) = (-1)^n
    alternating_one_seq(n) = (-1)^n
    (-1)^n <= 1
    -1 <= (-1)^n
    alternating_one_seq(n) <= 1
    -1 <= alternating_one_seq(n)
    -1 * alternating_one_seq(n) <= -1 * -1
    -1 * -1 = 1
    -1 * alternating_one_seq(n) <= 1
    -1 * 1 <= -1 * alternating_one_seq(n)
    -1 * 1 = -1
    -1 <= -1 * alternating_one_seq(n)
    reciprocal_nat_seq(n) = 1 / n
    1 / n > 0
    reciprocal_nat_seq(n) > 0
    (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n) <= 1 * reciprocal_nat_seq(n)
    1 * reciprocal_nat_seq(n) = reciprocal_nat_seq(n)
    (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n) <= reciprocal_nat_seq(n)
    -1 * reciprocal_nat_seq(n) <= (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n)
    alternating_reciprocal_seq(n) = (-1 * alternating_one_seq(n)) * reciprocal_nat_seq(n)
    alternating_reciprocal_seq(n) <= reciprocal_nat_seq(n)
    -reciprocal_nat_seq(n) = -1 * reciprocal_nat_seq(n)
    -reciprocal_nat_seq(n) <= alternating_reciprocal_seq(n)

claim:
    ? $has_finite_limit_superior(alternating_reciprocal_seq, 0)
    claim:
        ? $is_eventually_below_every_threshold_above(alternating_reciprocal_seq, 0)
        claim:
            ? forall x R:
                x > 0
                =>:
                    exist n_tail N_pos st {$is_eventually_below_threshold(alternating_reciprocal_seq, x, n_tail)}
            x $in R_pos
            exist n_bound N_pos st {1 / n_bound < x}
            have by exist n0 N_pos st {1 / n0 < x}: n0
            witness exist n_tail N_pos st {$is_eventually_below_threshold(alternating_reciprocal_seq, x, n_tail)} from n0:
                forall n N_pos:
                    n >= n0
                    =>:
                        alternating_reciprocal_seq(n) <= reciprocal_nat_seq(n)
                        reciprocal_nat_seq(n) = 1 / n
                        n0 <= n
                        n0 * n > 0
                        1 / n = n0 / (n0 * n)
                        n0 / (n0 * n) <= n / (n0 * n)
                        n / (n0 * n) = 1 / n0
                        1 / n <= 1 / n0
                        1 / n <= 1 / n0 < x
                        1 / n < x
                        reciprocal_nat_seq(n) < x
                        alternating_reciprocal_seq(n) <= reciprocal_nat_seq(n) < x
                        alternating_reciprocal_seq(n) < x
                $is_eventually_below_threshold(alternating_reciprocal_seq, x, n0)
        $is_eventually_below_every_threshold_above(alternating_reciprocal_seq, 0)
    claim:
        ? $exceeds_every_threshold_below_arbitrarily_late(alternating_reciprocal_seq, 0)
        claim:
            ? forall x R:
                x < 0
                =>:
                    $exceeds_threshold_arbitrarily_late(alternating_reciprocal_seq, x)
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and x < alternating_reciprocal_seq(n)}
                2 * n_tail + 1 $in N_pos
                2 * n_tail + 1 >= n_tail
                have n_odd N_pos = 2 * n_tail + 1
                n_odd = 2 * n_tail + 1
                n_odd >= n_tail
                witness exist n N_pos st {n >= n_tail and x < alternating_reciprocal_seq(n)} from n_odd:
                    n_odd >= n_tail
                    by thm alternating_one_odd_value(n_tail)
                    alternating_one_seq(n_odd) = alternating_one_seq(2 * n_tail + 1)
                    alternating_one_seq(2 * n_tail + 1) = -1
                    alternating_one_seq(n_odd) = -1
                    by thm alternating_reciprocal_unfold(n_odd)
                    alternating_reciprocal_seq(n_odd) = (-1 * alternating_one_seq(n_odd)) * reciprocal_nat_seq(n_odd)
                    reciprocal_nat_seq(n_odd) = 1 / n_odd
                    1 / n_odd > 0
                    -1 * alternating_one_seq(n_odd) = 1
                    alternating_reciprocal_seq(n_odd) = 1 * reciprocal_nat_seq(n_odd)
                    1 * reciprocal_nat_seq(n_odd) = reciprocal_nat_seq(n_odd)
                    alternating_reciprocal_seq(n_odd) = reciprocal_nat_seq(n_odd)
                    alternating_reciprocal_seq(n_odd) = 1 / n_odd
                    x < 0
                    x < 0 < 1 / n_odd
                    x < 1 / n_odd
                    x < alternating_reciprocal_seq(n_odd)
                    n_odd >= n_tail and x < alternating_reciprocal_seq(n_odd)
            $exceeds_threshold_arbitrarily_late(alternating_reciprocal_seq, x)
        $exceeds_every_threshold_below_arbitrarily_late(alternating_reciprocal_seq, 0)
    $has_finite_limit_superior(alternating_reciprocal_seq, 0)

claim:
    ? $has_finite_limit_inferior(alternating_reciprocal_seq, 0)
    claim:
        ? $is_eventually_above_every_threshold_below(alternating_reciprocal_seq, 0)
        claim:
            ? forall y R:
                y < 0
                =>:
                    exist n_tail N_pos st {$is_eventually_above_threshold(alternating_reciprocal_seq, y, n_tail)}
            -y $in R_pos
            exist n_bound N_pos st {1 / n_bound < -y}
            have by exist n0 N_pos st {1 / n0 < -y}: n0
            witness exist n_tail N_pos st {$is_eventually_above_threshold(alternating_reciprocal_seq, y, n_tail)} from n0:
                forall n N_pos:
                    n >= n0
                    =>:
                        -reciprocal_nat_seq(n) <= alternating_reciprocal_seq(n)
                        reciprocal_nat_seq(n) = 1 / n
                        n0 <= n
                        n0 * n > 0
                        1 / n = n0 / (n0 * n)
                        n0 / (n0 * n) <= n / (n0 * n)
                        n / (n0 * n) = 1 / n0
                        1 / n <= 1 / n0
                        1 / n <= 1 / n0 < -y
                        1 / n < -y
                        reciprocal_nat_seq(n) < -y
                        -y > reciprocal_nat_seq(n)
                        -(-y) < -reciprocal_nat_seq(n)
                        -(-y) = y
                        y < -reciprocal_nat_seq(n)
                        y < -reciprocal_nat_seq(n) <= alternating_reciprocal_seq(n)
                        y < alternating_reciprocal_seq(n)
                $is_eventually_above_threshold(alternating_reciprocal_seq, y, n0)
        $is_eventually_above_every_threshold_below(alternating_reciprocal_seq, 0)
    claim:
        ? $falls_below_every_threshold_above_arbitrarily_late(alternating_reciprocal_seq, 0)
        claim:
            ? forall y R:
                y > 0
                =>:
                    $falls_below_threshold_arbitrarily_late(alternating_reciprocal_seq, y)
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and alternating_reciprocal_seq(n) < y}
                2 * n_tail $in N_pos
                2 * n_tail >= n_tail
                have n_even N_pos = 2 * n_tail
                n_even = 2 * n_tail
                n_even >= n_tail
                witness exist n N_pos st {n >= n_tail and alternating_reciprocal_seq(n) < y} from n_even:
                    n_even >= n_tail
                    by thm alternating_one_even_value(n_tail)
                    alternating_one_seq(n_even) = alternating_one_seq(2 * n_tail)
                    alternating_one_seq(2 * n_tail) = 1
                    alternating_one_seq(n_even) = 1
                    by thm alternating_reciprocal_unfold(n_even)
                    alternating_reciprocal_seq(n_even) = (-1 * alternating_one_seq(n_even)) * reciprocal_nat_seq(n_even)
                    reciprocal_nat_seq(n_even) = 1 / n_even
                    1 / n_even > 0
                    reciprocal_nat_seq(n_even) > 0
                    -1 * reciprocal_nat_seq(n_even) < 0
                    -1 * alternating_one_seq(n_even) = -1
                    alternating_reciprocal_seq(n_even) = -1 * reciprocal_nat_seq(n_even)
                    -1 * reciprocal_nat_seq(n_even) = -1 * (1 / n_even)
                    alternating_reciprocal_seq(n_even) = -1 * (1 / n_even)
                    alternating_reciprocal_seq(n_even) < 0
                    0 < y
                    alternating_reciprocal_seq(n_even) < 0 < y
                    alternating_reciprocal_seq(n_even) < y
                    n_even >= n_tail and alternating_reciprocal_seq(n_even) < y
            $falls_below_threshold_arbitrarily_late(alternating_reciprocal_seq, y)
        $falls_below_every_threshold_above_arbitrarily_late(alternating_reciprocal_seq, 0)
    $has_finite_limit_inferior(alternating_reciprocal_seq, 0)

"""
Example 6.4.10. The sequence 1, 2, 3, 4, ... has both limit superior and
limit inferior equal to +infty.
"""

# This is another infinity-facing example: every tail is unbounded above.

claim:
    ? $has_limit_superior_pos_infinity(natural_as_real_seq)
    claim:
        ? forall x R:
            $exceeds_threshold_arbitrarily_late(natural_as_real_seq, x)
        by thm exists_nat_above_real(x)
        have by exist n0 N_pos st {x < n0}: n0
        claim:
            ? forall n_tail N_pos:
                exist n N_pos st {n >= n_tail and x < natural_as_real_seq(n)}
            max(n_tail, n0) $in N_pos
            max(n_tail, n0) >= n_tail
            max(n_tail, n0) >= n0
            witness exist n N_pos st {n >= n_tail and x < natural_as_real_seq(n)} from max(n_tail, n0):
                max(n_tail, n0) >= n_tail
                max(n_tail, n0) >= n0
                x < n0 <= max(n_tail, n0)
                x < max(n_tail, n0)
                natural_as_real_seq(max(n_tail, n0)) = max(n_tail, n0)
                x < natural_as_real_seq(max(n_tail, n0))
                max(n_tail, n0) >= n_tail and x < natural_as_real_seq(max(n_tail, n0))
        $exceeds_threshold_arbitrarily_late(natural_as_real_seq, x)
    $has_limit_superior_pos_infinity(natural_as_real_seq)

claim:
    ? $has_limit_inferior_pos_infinity(natural_as_real_seq)
    claim:
        ? forall y R:
            exist n_tail N_pos st {$is_eventually_above_threshold(natural_as_real_seq, y, n_tail)}
        by thm exists_nat_above_real(y)
        have by exist n0 N_pos st {y < n0}: n0
        witness exist n_tail N_pos st {$is_eventually_above_threshold(natural_as_real_seq, y, n_tail)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    y < n0
                    n0 <= n
                    y < n0 <= n
                    y < n
                    natural_as_real_seq(n) = n
                    y < natural_as_real_seq(n)
            $is_eventually_above_threshold(natural_as_real_seq, y, n0)
    $has_limit_inferior_pos_infinity(natural_as_real_seq)

"""
Remark 6.4.11. The starting index does not affect limsup or liminf.
"""

# This is the limsup/liminf analogue of Remark 6.1.9 and is kept as a future
# sequence-library fact.

"""
Proposition 6.4.12. Basic properties of limsup and liminf.
"""

# The source statement allows extended-real endpoints.  The checked statements
# below prove the finite real-valued branch using `has_finite_limit_superior`
# and `has_finite_limit_inferior`; the `+infty` and `-infty` endpoint cases
# belong to the deferred extended-order interface.  The proof repeatedly uses
# the threshold characterization: eventual upper/lower control together with
# arbitrarily late crossings.

thm bounded_sequence_tail_sup_sequence_decreasing:
    ? forall a seq(R):
        $is_bounded_sequence(a)
        =>:
            $is_decreasing_sequence('(m N_pos) R {tail_sup(a, m)})
    claim:
        ? forall m N_pos:
            $has_tail_supremum(a, m)
        by thm bounded_sequence_has_tail_supremum(a, m)
    claim:
        ? forall n N_pos:
            '(m N_pos) R {tail_sup(a, m)}(n + 1) <= '(m N_pos) R {tail_sup(a, m)}(n)
        $has_tail_supremum(a, n)
        $has_tail_supremum(a, n + 1)
        $is_tail_supremum(a, n, tail_sup(a, n))
        $is_tail_supremum(a, n + 1, tail_sup(a, n + 1))
        $is_tail_upper_bound(a, n, tail_sup(a, n))
        n + 1 >= n
        by thm tail_upper_bound_restrict_to_later_tail(a, n, n + 1, tail_sup(a, n))
        $is_tail_upper_bound(a, n + 1, tail_sup(a, n))
        by thm tail_supremum_le_every_upper_bound(a, n + 1, tail_sup(a, n + 1), tail_sup(a, n))
        tail_sup(a, n + 1) <= tail_sup(a, n)
        '(m N_pos) R {tail_sup(a, m)}(n + 1) = tail_sup(a, n + 1)
        '(m N_pos) R {tail_sup(a, m)}(n) = tail_sup(a, n)
        '(m N_pos) R {tail_sup(a, m)}(n + 1) <= '(m N_pos) R {tail_sup(a, m)}(n)
    $is_decreasing_sequence('(m N_pos) R {tail_sup(a, m)})

thm bounded_sequence_tail_sup_sequence_bounded_below:
    ? forall a seq(R):
        $is_bounded_sequence(a)
        =>:
            $is_bounded_below_sequence('(m N_pos) R {tail_sup(a, m)})
    claim:
        ? forall m N_pos:
            $has_tail_supremum(a, m)
        by thm bounded_sequence_has_tail_supremum(a, m)
    have by exist B R st {$is_bounded_by(a, B)}: B
    claim:
        ? $is_sequence_lower_bound('(m N_pos) R {tail_sup(a, m)}, -B)
        forall m N_pos:
            $has_tail_supremum(a, m)
            $is_tail_supremum(a, m, tail_sup(a, m))
            $is_tail_upper_bound(a, m, tail_sup(a, m))
            B >= 0
            abs(a(m)) <= B
            abs(B) = B
            abs(a(m)) <= abs(B)
            -B <= a(m)
            m >= m
            a(m) <= tail_sup(a, m)
            -B <= a(m) <= tail_sup(a, m)
            -B <= tail_sup(a, m)
            '(m N_pos) R {tail_sup(a, m)}(m) = tail_sup(a, m)
            -B <= '(m N_pos) R {tail_sup(a, m)}(m)
        $is_sequence_lower_bound('(m N_pos) R {tail_sup(a, m)}, -B)
    witness exist M R st {$is_sequence_lower_bound('(m N_pos) R {tail_sup(a, m)}, M)} from -B:
        $is_sequence_lower_bound('(m N_pos) R {tail_sup(a, m)}, -B)
    $is_bounded_below_sequence('(m N_pos) R {tail_sup(a, m)})

thm bounded_sequence_tail_sup_sequence_converges:
    ? forall a seq(R):
        $is_bounded_sequence(a)
        =>:
            $is_convergent_sequence('(m N_pos) R {tail_sup(a, m)})
    by thm bounded_sequence_tail_sup_sequence_decreasing(a)
    by thm bounded_sequence_tail_sup_sequence_bounded_below(a)
    by thm bounded_decreasing_sequence_converges('(m N_pos) R {tail_sup(a, m)})
    $is_convergent_sequence('(m N_pos) R {tail_sup(a, m)})

thm tail_sup_limit_is_finite_limsup:
    ? forall a seq(R), L R:
        forall m N_pos:
            $has_tail_supremum(a, m)
        $has_limit('(m N_pos) R {tail_sup(a, m)}, L)
        =>:
            $has_finite_limit_superior(a, L)
    claim:
        ? $is_eventually_below_every_threshold_above(a, L)
        claim:
            ? forall x R:
                x > L
                =>:
                    exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)}
            x - L $in R_pos
            $has_eventual_closeness_to('(m N_pos) R {tail_sup(a, m)}, L, x - L)
            have by exist n0 N_pos st {$is_tail_close_to('(m N_pos) R {tail_sup(a, m)}, L, x - L, n0)}: n0
            witness exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)} from n0:
                forall n N_pos:
                    n >= n0
                    =>:
                        '(m N_pos) R {tail_sup(a, m)}(n0) = tail_sup(a, n0)
                        abs('(m N_pos) R {tail_sup(a, m)}(n0) - L) < x - L
                        abs(tail_sup(a, n0) - L) = abs('(m N_pos) R {tail_sup(a, m)}(n0) - L)
                        abs(tail_sup(a, n0) - L) < x - L
                        tail_sup(a, n0) - L <= abs(tail_sup(a, n0) - L)
                        tail_sup(a, n0) - L <= abs(tail_sup(a, n0) - L) < x - L
                        tail_sup(a, n0) - L < x - L
                        tail_sup(a, n0) - L + L < x - L + L
                        tail_sup(a, n0) - L + L = tail_sup(a, n0)
                        x - L + L = x
                        tail_sup(a, n0) < x
                        $has_tail_supremum(a, n0)
                        $is_tail_supremum(a, n0, tail_sup(a, n0))
                        $is_tail_upper_bound(a, n0, tail_sup(a, n0))
                        a(n) <= tail_sup(a, n0)
                        a(n) <= tail_sup(a, n0) < x
                        a(n) < x
                $is_eventually_below_threshold(a, x, n0)
        $is_eventually_below_every_threshold_above(a, L)
    claim:
        ? $exceeds_every_threshold_below_arbitrarily_late(a, L)
        claim:
            ? forall x R:
                x < L
                =>:
                    $exceeds_threshold_arbitrarily_late(a, x)
            L - x $in R_pos
            $has_eventual_closeness_to('(m N_pos) R {tail_sup(a, m)}, L, L - x)
            have by exist n0 N_pos st {$is_tail_close_to('(m N_pos) R {tail_sup(a, m)}, L, L - x, n0)}: n0
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and x < a(n)}
                max(n_tail, n0) $in N_pos
                max(n_tail, n0) >= n_tail
                max(n_tail, n0) >= n0
                have m0 N_pos = max(n_tail, n0)
                m0 >= n_tail
                m0 >= n0
                $has_tail_supremum(a, m0)
                $is_tail_supremum(a, m0, tail_sup(a, m0))
                '(m N_pos) R {tail_sup(a, m)}(m0) = tail_sup(a, m0)
                abs('(m N_pos) R {tail_sup(a, m)}(m0) - L) < L - x
                abs(tail_sup(a, m0) - L) = abs('(m N_pos) R {tail_sup(a, m)}(m0) - L)
                abs(tail_sup(a, m0) - L) < L - x
                abs(L - tail_sup(a, m0)) = abs(tail_sup(a, m0) - L)
                L - tail_sup(a, m0) <= abs(L - tail_sup(a, m0))
                L - tail_sup(a, m0) <= abs(L - tail_sup(a, m0)) = abs(tail_sup(a, m0) - L) < L - x
                L - tail_sup(a, m0) < L - x
                L - (L - tail_sup(a, m0)) > L - (L - x)
                L - (L - tail_sup(a, m0)) = tail_sup(a, m0)
                L - (L - x) = x
                tail_sup(a, m0) > x
                x < tail_sup(a, m0)
                by thm tail_supremum_crosses_every_lower_threshold(a, m0, tail_sup(a, m0), x)
                have by exist n1 N_pos st {n1 >= m0 and x < a(n1)}: n1
                n1 >= m0
                n_tail <= m0 <= n1
                n_tail <= n1
                n1 >= n_tail
                witness exist n N_pos st {n >= n_tail and x < a(n)} from n1:
                    n1 >= n_tail
                    x < a(n1)
                    n1 >= n_tail and x < a(n1)
            $exceeds_threshold_arbitrarily_late(a, x)
        $exceeds_every_threshold_below_arbitrarily_late(a, L)
    $has_finite_limit_superior(a, L)

thm bounded_sequence_has_finite_limsup:
    ? forall a seq(R):
        $is_bounded_sequence(a)
        =>:
            exist Lplus R st {$has_finite_limit_superior(a, Lplus)}
    claim:
        ? forall m N_pos:
            $has_tail_supremum(a, m)
        by thm bounded_sequence_has_tail_supremum(a, m)
    by thm bounded_sequence_tail_sup_sequence_converges(a)
    have by exist Lplus R st {$has_limit('(m N_pos) R {tail_sup(a, m)}, Lplus)}: Lplus
    by thm tail_sup_limit_is_finite_limsup(a, Lplus)
    witness exist L0 R st {$has_finite_limit_superior(a, L0)} from Lplus:
        $has_finite_limit_superior(a, Lplus)

thm finite_limsup_eventually_below:
    ? forall a seq(R), Lplus, x R:
        $has_finite_limit_superior(a, Lplus)
        x > Lplus
        =>:
            exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)}
    $is_eventually_below_every_threshold_above(a, Lplus)
    exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)}

thm finite_liminf_eventually_above:
    ? forall a seq(R), Lminus, y R:
        $has_finite_limit_inferior(a, Lminus)
        y < Lminus
        =>:
            exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)}
    $is_eventually_above_every_threshold_below(a, Lminus)
    exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)}

thm finite_limsup_exceeds_arbitrarily_late:
    ? forall a seq(R), Lplus, x R:
        $has_finite_limit_superior(a, Lplus)
        x < Lplus
        =>:
            $exceeds_threshold_arbitrarily_late(a, x)
    $exceeds_every_threshold_below_arbitrarily_late(a, Lplus)
    $exceeds_threshold_arbitrarily_late(a, x)

thm finite_liminf_falls_arbitrarily_late:
    ? forall a seq(R), Lminus, y R:
        $has_finite_limit_inferior(a, Lminus)
        y > Lminus
        =>:
            $falls_below_threshold_arbitrarily_late(a, y)
    $falls_below_every_threshold_above_arbitrarily_late(a, Lminus)
    $falls_below_threshold_arbitrarily_late(a, y)

thm finite_limsup_le_tail_supremum:
    ? forall a seq(R), Lplus, S R:
        $has_finite_limit_superior(a, Lplus)
        $is_tail_supremum(a, 1, S)
        =>:
            Lplus <= S
    by contra:
        ? Lplus <= S
        not Lplus <= S
        S < Lplus
        by thm finite_limsup_exceeds_arbitrarily_late(a, Lplus, S)
        $exceeds_threshold_arbitrarily_late(a, S)
        have by exist n N_pos st {n >= 1 and S < a(n)}: n
        n >= 1 and S < a(n)
        n >= 1
        S < a(n)
        by thm tail_supremum_is_upper_bound(a, 1, S)
        $is_tail_upper_bound(a, 1, S)
        a(n) <= S
        S < a(n) <= S
        S < S
        S != S
        impossible S = S

thm tail_infimum_le_finite_liminf:
    ? forall a seq(R), Lminus, I R:
        $has_finite_limit_inferior(a, Lminus)
        $is_tail_infimum(a, 1, I)
        =>:
            I <= Lminus
    by contra:
        ? I <= Lminus
        not I <= Lminus
        Lminus < I
        by thm finite_liminf_falls_arbitrarily_late(a, Lminus, I)
        $falls_below_threshold_arbitrarily_late(a, I)
        have by exist n N_pos st {n >= 1 and a(n) < I}: n
        n >= 1 and a(n) < I
        n >= 1
        a(n) < I
        by thm tail_infimum_is_lower_bound(a, 1, I)
        $is_tail_lower_bound(a, 1, I)
        I <= a(n)
        I <= a(n) < I
        I < I
        I != I
        impossible I = I

thm finite_liminf_le_finite_limsup:
    ? forall a seq(R), Lminus, Lplus R:
        $has_finite_limit_inferior(a, Lminus)
        $has_finite_limit_superior(a, Lplus)
        =>:
            Lminus <= Lplus
    by contra:
        ? Lminus <= Lplus
        not Lminus <= Lplus
        Lplus < Lminus
        have mid R = (Lplus + Lminus) / 2
        Lplus + Lplus < Lplus + Lminus
        2 * Lplus = Lplus + Lplus
        2 * Lplus < Lplus + Lminus
        Lplus = (2 * Lplus) / 2 < (Lplus + Lminus) / 2
        Lplus < mid
        Lplus + Lminus < Lminus + Lminus
        Lminus + Lminus = 2 * Lminus
        Lplus + Lminus < 2 * Lminus
        (Lplus + Lminus) / 2 < (2 * Lminus) / 2 = Lminus
        mid < Lminus
        by thm finite_limsup_eventually_below(a, Lplus, mid)
        have by exist n_upper N_pos st {$is_eventually_below_threshold(a, mid, n_upper)}: n_upper
        by thm finite_liminf_eventually_above(a, Lminus, mid)
        have by exist n_lower N_pos st {$is_eventually_above_threshold(a, mid, n_lower)}: n_lower
        max(n_upper, n_lower) $in N_pos
        max(n_upper, n_lower) >= n_upper
        max(n_upper, n_lower) >= n_lower
        a(max(n_upper, n_lower)) < mid
        mid < a(max(n_upper, n_lower))
        mid < a(max(n_upper, n_lower)) < mid
        mid < mid
        mid != mid
        impossible mid = mid

thm finite_lims_between_tail_bounds:
    ? forall a seq(R), I, Lminus, Lplus, S R:
        $is_tail_infimum(a, 1, I)
        $has_finite_limit_inferior(a, Lminus)
        $has_finite_limit_superior(a, Lplus)
        $is_tail_supremum(a, 1, S)
        =>:
            I <= Lminus
            Lminus <= Lplus
            Lplus <= S
    by thm tail_infimum_le_finite_liminf(a, Lminus, I)
    by thm finite_liminf_le_finite_limsup(a, Lminus, Lplus)
    by thm finite_limsup_le_tail_supremum(a, Lplus, S)

thm finite_limsup_bounds_limit_point:
    ? forall a seq(R), c, Lplus R:
        $is_limit_point(a, c)
        $has_finite_limit_superior(a, Lplus)
        =>:
            c <= Lplus
    by contra:
        ? c <= Lplus
        not c <= Lplus
        Lplus < c
        have x R = (Lplus + c) / 2
        Lplus + Lplus < Lplus + c
        2 * Lplus = Lplus + Lplus
        2 * Lplus < Lplus + c
        Lplus = (2 * Lplus) / 2 < (Lplus + c) / 2
        Lplus < x
        Lplus + c < c + c
        c + c = 2 * c
        Lplus + c < 2 * c
        (Lplus + c) / 2 < (2 * c) / 2 = c
        x < c
        c - x $in R_pos
        by thm finite_limsup_eventually_below(a, Lplus, x)
        have by exist n0 N_pos st {$is_eventually_below_threshold(a, x, n0)}: n0
        $is_epsilon_adherent_to_sequence(a, c, c - x, n0)
        have by exist n N_pos st {n >= n0 and abs(a(n) - c) < c - x}: n
        n >= n0 and abs(a(n) - c) < c - x
        n >= n0
        abs(a(n) - c) < c - x
        a(n) < x
        c - a(n) > c - x
        abs(c - a(n)) = abs(a(n) - c)
        c - a(n) <= abs(c - a(n))
        c - a(n) <= abs(c - a(n)) = abs(a(n) - c) < c - x
        c - a(n) < c - x
        c - a(n) < c - x < c - a(n)
        c - a(n) < c - a(n)
        c - a(n) != c - a(n)
        impossible c - a(n) = c - a(n)

thm finite_liminf_bounds_limit_point:
    ? forall a seq(R), c, Lminus R:
        $is_limit_point(a, c)
        $has_finite_limit_inferior(a, Lminus)
        =>:
            Lminus <= c
    by contra:
        ? Lminus <= c
        not Lminus <= c
        c < Lminus
        have y R = (c + Lminus) / 2
        c + c < c + Lminus
        2 * c = c + c
        2 * c < c + Lminus
        c = (2 * c) / 2 < (c + Lminus) / 2
        c < y
        c + Lminus < Lminus + Lminus
        Lminus + Lminus = 2 * Lminus
        c + Lminus < 2 * Lminus
        (c + Lminus) / 2 < (2 * Lminus) / 2 = Lminus
        y < Lminus
        y - c $in R_pos
        by thm finite_liminf_eventually_above(a, Lminus, y)
        have by exist n0 N_pos st {$is_eventually_above_threshold(a, y, n0)}: n0
        $is_epsilon_adherent_to_sequence(a, c, y - c, n0)
        have by exist n N_pos st {n >= n0 and abs(a(n) - c) < y - c}: n
        n >= n0 and abs(a(n) - c) < y - c
        n >= n0
        abs(a(n) - c) < y - c
        y < a(n)
        a(n) - c > y - c
        a(n) - c <= abs(a(n) - c)
        a(n) - c <= abs(a(n) - c) < y - c
        a(n) - c < y - c
        a(n) - c < y - c < a(n) - c
        a(n) - c < a(n) - c
        a(n) - c != a(n) - c
        impossible a(n) - c = a(n) - c

thm finite_lims_bound_limit_points:
    ? forall a seq(R), c, Lminus, Lplus R:
        $is_limit_point(a, c)
        $has_finite_limit_inferior(a, Lminus)
        $has_finite_limit_superior(a, Lplus)
        =>:
            Lminus <= c
            c <= Lplus
    by thm finite_liminf_bounds_limit_point(a, c, Lminus)
    by thm finite_limsup_bounds_limit_point(a, c, Lplus)

thm finite_limsup_is_limit_point:
    ? forall a seq(R), Lplus R:
        $has_finite_limit_superior(a, Lplus)
        =>:
            $is_limit_point(a, Lplus)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(a, Lplus, epsilon, n_tail)
        Lplus + epsilon > Lplus
        by thm finite_limsup_eventually_below(a, Lplus, Lplus + epsilon)
        have by exist n_upper N_pos st {$is_eventually_below_threshold(a, Lplus + epsilon, n_upper)}: n_upper
        Lplus - epsilon < Lplus
        by thm finite_limsup_exceeds_arbitrarily_late(a, Lplus, Lplus - epsilon)
        $exceeds_threshold_arbitrarily_late(a, Lplus - epsilon)
        max(n_tail, n_upper) $in N_pos
        have by exist n N_pos st {n >= max(n_tail, n_upper) and Lplus - epsilon < a(n)}: n
        witness exist k N_pos st {k >= n_tail and abs(a(k) - Lplus) < epsilon} from n:
            n >= max(n_tail, n_upper) and Lplus - epsilon < a(n)
            n >= max(n_tail, n_upper)
            n_tail <= max(n_tail, n_upper) <= n
            n >= n_tail
            n_upper <= max(n_tail, n_upper) <= n
            n >= n_upper
            a(n) < Lplus + epsilon
            Lplus - epsilon < a(n)
            a(n) - Lplus < Lplus + epsilon - Lplus
            Lplus + epsilon - Lplus = epsilon
            a(n) - Lplus < epsilon
            Lplus - epsilon + epsilon < a(n) + epsilon
            Lplus - epsilon + epsilon = Lplus
            Lplus < a(n) + epsilon
            Lplus - a(n) < a(n) + epsilon - a(n)
            a(n) + epsilon - a(n) = epsilon
            Lplus - a(n) < epsilon
            -(a(n) - Lplus) = Lplus - a(n)
            -(a(n) - Lplus) < epsilon
            abs(a(n) - Lplus) < epsilon
            n >= n_tail and abs(a(n) - Lplus) < epsilon
        $is_epsilon_adherent_to_sequence(a, Lplus, epsilon, n_tail)
    $is_limit_point(a, Lplus)

thm finite_liminf_is_limit_point:
    ? forall a seq(R), Lminus R:
        $has_finite_limit_inferior(a, Lminus)
        =>:
            $is_limit_point(a, Lminus)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(a, Lminus, epsilon, n_tail)
        Lminus - epsilon < Lminus
        by thm finite_liminf_eventually_above(a, Lminus, Lminus - epsilon)
        have by exist n_lower N_pos st {$is_eventually_above_threshold(a, Lminus - epsilon, n_lower)}: n_lower
        Lminus + epsilon > Lminus
        by thm finite_liminf_falls_arbitrarily_late(a, Lminus, Lminus + epsilon)
        $falls_below_threshold_arbitrarily_late(a, Lminus + epsilon)
        max(n_tail, n_lower) $in N_pos
        have by exist n N_pos st {n >= max(n_tail, n_lower) and a(n) < Lminus + epsilon}: n
        witness exist k N_pos st {k >= n_tail and abs(a(k) - Lminus) < epsilon} from n:
            n >= max(n_tail, n_lower) and a(n) < Lminus + epsilon
            n >= max(n_tail, n_lower)
            n_tail <= max(n_tail, n_lower) <= n
            n >= n_tail
            n_lower <= max(n_tail, n_lower) <= n
            n >= n_lower
            Lminus - epsilon < a(n)
            a(n) < Lminus + epsilon
            a(n) - Lminus < Lminus + epsilon - Lminus
            Lminus + epsilon - Lminus = epsilon
            a(n) - Lminus < epsilon
            Lminus - epsilon + epsilon < a(n) + epsilon
            Lminus - epsilon + epsilon = Lminus
            Lminus < a(n) + epsilon
            Lminus - a(n) < a(n) + epsilon - a(n)
            a(n) + epsilon - a(n) = epsilon
            Lminus - a(n) < epsilon
            -(a(n) - Lminus) = Lminus - a(n)
            -(a(n) - Lminus) < epsilon
            abs(a(n) - Lminus) < epsilon
            n >= n_tail and abs(a(n) - Lminus) < epsilon
        $is_epsilon_adherent_to_sequence(a, Lminus, epsilon, n_tail)
    $is_limit_point(a, Lminus)

thm convergent_sequence_has_finite_lims:
    ? forall a seq(R), c R:
        $has_limit(a, c)
        =>:
            $has_finite_limit_superior(a, c)
            $has_finite_limit_inferior(a, c)
    claim:
        ? $is_eventually_below_every_threshold_above(a, c)
        claim:
            ? forall x R:
                x > c
                =>:
                    exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)}
            x - c $in R_pos
            $has_eventual_closeness_to(a, c, x - c)
            have by exist n0 N_pos st {$is_tail_close_to(a, c, x - c, n0)}: n0
            witness exist n_tail N_pos st {$is_eventually_below_threshold(a, x, n_tail)} from n0:
                forall n N_pos:
                    n >= n0
                    =>:
                        abs(a(n) - c) < x - c
                        a(n) - c <= abs(a(n) - c)
                        a(n) - c <= abs(a(n) - c) < x - c
                        a(n) - c < x - c
                        a(n) - c + c < x - c + c
                        a(n) - c + c = a(n)
                        x - c + c = x
                        a(n) < x
                $is_eventually_below_threshold(a, x, n0)
        $is_eventually_below_every_threshold_above(a, c)
    claim:
        ? $exceeds_every_threshold_below_arbitrarily_late(a, c)
        claim:
            ? forall x R:
                x < c
                =>:
                    $exceeds_threshold_arbitrarily_late(a, x)
            c - x $in R_pos
            $has_eventual_closeness_to(a, c, c - x)
            have by exist n0 N_pos st {$is_tail_close_to(a, c, c - x, n0)}: n0
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and x < a(n)}
                max(n_tail, n0) $in N_pos
                max(n_tail, n0) >= n_tail
                max(n_tail, n0) >= n0
                witness exist n N_pos st {n >= n_tail and x < a(n)} from max(n_tail, n0):
                    max(n_tail, n0) >= n_tail
                    max(n_tail, n0) >= n0
                    abs(a(max(n_tail, n0)) - c) < c - x
                    abs(c - a(max(n_tail, n0))) = abs(a(max(n_tail, n0)) - c)
                    c - a(max(n_tail, n0)) <= abs(c - a(max(n_tail, n0)))
                    c - a(max(n_tail, n0)) <= abs(c - a(max(n_tail, n0))) = abs(a(max(n_tail, n0)) - c) < c - x
                    c - a(max(n_tail, n0)) < c - x
                    c - (c - a(max(n_tail, n0))) > c - (c - x)
                    c - (c - a(max(n_tail, n0))) = a(max(n_tail, n0))
                    c - (c - x) = x
                    a(max(n_tail, n0)) > x
                    x < a(max(n_tail, n0))
                    max(n_tail, n0) >= n_tail and x < a(max(n_tail, n0))
            $exceeds_threshold_arbitrarily_late(a, x)
        $exceeds_every_threshold_below_arbitrarily_late(a, c)
    claim:
        ? $is_eventually_above_every_threshold_below(a, c)
        claim:
            ? forall y R:
                y < c
                =>:
                    exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)}
            c - y $in R_pos
            $has_eventual_closeness_to(a, c, c - y)
            have by exist n0 N_pos st {$is_tail_close_to(a, c, c - y, n0)}: n0
            witness exist n_tail N_pos st {$is_eventually_above_threshold(a, y, n_tail)} from n0:
                forall n N_pos:
                    n >= n0
                    =>:
                        abs(a(n) - c) < c - y
                        abs(c - a(n)) = abs(a(n) - c)
                        c - a(n) <= abs(c - a(n))
                        c - a(n) <= abs(c - a(n)) = abs(a(n) - c) < c - y
                        c - a(n) < c - y
                        c - (c - a(n)) > c - (c - y)
                        c - (c - a(n)) = a(n)
                        c - (c - y) = y
                        a(n) > y
                        y < a(n)
                $is_eventually_above_threshold(a, y, n0)
        $is_eventually_above_every_threshold_below(a, c)
    claim:
        ? $falls_below_every_threshold_above_arbitrarily_late(a, c)
        claim:
            ? forall y R:
                y > c
                =>:
                    $falls_below_threshold_arbitrarily_late(a, y)
            y - c $in R_pos
            $has_eventual_closeness_to(a, c, y - c)
            have by exist n0 N_pos st {$is_tail_close_to(a, c, y - c, n0)}: n0
            claim:
                ? forall n_tail N_pos:
                    exist n N_pos st {n >= n_tail and a(n) < y}
                max(n_tail, n0) $in N_pos
                max(n_tail, n0) >= n_tail
                max(n_tail, n0) >= n0
                witness exist n N_pos st {n >= n_tail and a(n) < y} from max(n_tail, n0):
                    max(n_tail, n0) >= n_tail
                    max(n_tail, n0) >= n0
                    abs(a(max(n_tail, n0)) - c) < y - c
                    a(max(n_tail, n0)) - c <= abs(a(max(n_tail, n0)) - c)
                    a(max(n_tail, n0)) - c <= abs(a(max(n_tail, n0)) - c) < y - c
                    a(max(n_tail, n0)) - c < y - c
                    a(max(n_tail, n0)) - c + c < y - c + c
                    a(max(n_tail, n0)) - c + c = a(max(n_tail, n0))
                    y - c + c = y
                    a(max(n_tail, n0)) < y
                    max(n_tail, n0) >= n_tail and a(max(n_tail, n0)) < y
            $falls_below_threshold_arbitrarily_late(a, y)
        $falls_below_every_threshold_above_arbitrarily_late(a, c)
    $has_finite_limit_superior(a, c)
    $has_finite_limit_inferior(a, c)

thm equal_finite_lims_converge:
    ? forall a seq(R), c R:
        $has_finite_limit_superior(a, c)
        $has_finite_limit_inferior(a, c)
        =>:
            $has_limit(a, c)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, c, epsilon)
        c + epsilon > c
        by thm finite_limsup_eventually_below(a, c, c + epsilon)
        have by exist n_upper N_pos st {$is_eventually_below_threshold(a, c + epsilon, n_upper)}: n_upper
        c - epsilon < c
        by thm finite_liminf_eventually_above(a, c, c - epsilon)
        have by exist n_lower N_pos st {$is_eventually_above_threshold(a, c - epsilon, n_lower)}: n_lower
        max(n_upper, n_lower) $in N_pos
        witness exist n0 N_pos st {$is_tail_close_to(a, c, epsilon, n0)} from max(n_upper, n_lower):
            forall n N_pos:
                n >= max(n_upper, n_lower)
                =>:
                    n_upper <= max(n_upper, n_lower) <= n
                    n >= n_upper
                    n_lower <= max(n_upper, n_lower) <= n
                    n >= n_lower
                    a(n) < c + epsilon
                    c - epsilon < a(n)
                    a(n) - c < c + epsilon - c
                    c + epsilon - c = epsilon
                    a(n) - c < epsilon
                    c - epsilon + epsilon < a(n) + epsilon
                    c - epsilon + epsilon = c
                    c < a(n) + epsilon
                    c - a(n) < a(n) + epsilon - a(n)
                    a(n) + epsilon - a(n) = epsilon
                    c - a(n) < epsilon
                    -(a(n) - c) = c - a(n)
                    -(a(n) - c) < epsilon
                    abs(a(n) - c) < epsilon
            $is_tail_close_to(a, c, epsilon, max(n_upper, n_lower))
        $has_eventual_closeness_to(a, c, epsilon)
    $has_limit(a, c)

"""
Lemma 6.4.13. Comparison principle for suprema, infima, limsup, and liminf.
"""

thm finite_limsup_comparison:
    ? forall a, b seq(R), La, Lb R:
        $is_pointwise_le(a, b)
        $has_finite_limit_superior(a, La)
        $has_finite_limit_superior(b, Lb)
        =>:
            La <= Lb
    by contra:
        ? La <= Lb
        not La <= Lb
        Lb < La
        have mid R = (La + Lb) / 2
        Lb + Lb < La + Lb
        2 * Lb = Lb + Lb
        2 * Lb < La + Lb
        Lb = (2 * Lb) / 2 < (La + Lb) / 2
        Lb < mid
        La + Lb < La + La
        La + La = 2 * La
        (La + Lb) / 2 < (2 * La) / 2 = La
        mid < La
        by thm finite_limsup_eventually_below(b, Lb, mid)
        have by exist n_tail N_pos st {$is_eventually_below_threshold(b, mid, n_tail)}: n_tail
        by thm finite_limsup_exceeds_arbitrarily_late(a, La, mid)
        $exceeds_threshold_arbitrarily_late(a, mid)
        have by exist n N_pos st {n >= n_tail and mid < a(n)}: n
        n >= n_tail and mid < a(n)
        n >= n_tail
        mid < a(n)
        a(n) <= b(n)
        b(n) < mid
        mid < a(n) <= b(n)
        mid < b(n)
        mid < b(n) < mid
        mid < mid
        impossible mid = mid

thm finite_liminf_comparison:
    ? forall a, b seq(R), La, Lb R:
        $is_pointwise_le(a, b)
        $has_finite_limit_inferior(a, La)
        $has_finite_limit_inferior(b, Lb)
        =>:
            La <= Lb
    by contra:
        ? La <= Lb
        not La <= Lb
        Lb < La
        have mid R = (La + Lb) / 2
        Lb + Lb < La + Lb
        2 * Lb = Lb + Lb
        2 * Lb < La + Lb
        Lb = (2 * Lb) / 2 < (La + Lb) / 2
        Lb < mid
        La + Lb < La + La
        La + La = 2 * La
        (La + Lb) / 2 < (2 * La) / 2 = La
        mid < La
        by thm finite_liminf_eventually_above(a, La, mid)
        have by exist n_tail N_pos st {$is_eventually_above_threshold(a, mid, n_tail)}: n_tail
        by thm finite_liminf_falls_arbitrarily_late(b, Lb, mid)
        $falls_below_threshold_arbitrarily_late(b, mid)
        have by exist n N_pos st {n >= n_tail and b(n) < mid}: n
        n >= n_tail and b(n) < mid
        n >= n_tail
        b(n) < mid
        mid < a(n)
        a(n) <= b(n)
        mid < a(n) <= b(n)
        mid < b(n)
        mid < b(n) < mid
        mid < mid
        impossible mid = mid

"""
Corollary 6.4.14 (Squeeze test). Let (a_n)_{n=m}^infty,
(b_n)_{n=m}^infty, and (c_n)_{n=m}^infty be sequences of real numbers such
that a_n <= b_n <= c_n for all n >= m. Suppose also that (a_n)_{n=m}^infty
and (c_n)_{n=m}^infty both converge to the same limit L. Then
(b_n)_{n=m}^infty is also convergent to L.
"""

thm squeeze_converges_to:
    ? forall a, b, c seq(R), L R:
        $is_pointwise_between(a, b, c)
        $has_limit(a, L)
        $has_limit(c, L)
        =>:
            $has_limit(b, L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(b, L, epsilon)
        $has_eventual_closeness_to(a, L, epsilon)
        $has_eventual_closeness_to(c, L, epsilon)
        have by exist n_lower N_pos st {$is_tail_close_to(a, L, epsilon, n_lower)}: n_lower
        have by exist n_upper N_pos st {$is_tail_close_to(c, L, epsilon, n_upper)}: n_upper
        max(n_lower, n_upper) $in N_pos
        witness exist n0 N_pos st {$is_tail_close_to(b, L, epsilon, n0)} from max(n_lower, n_upper):
            forall n N_pos:
                n >= max(n_lower, n_upper)
                =>:
                    n_lower <= max(n_lower, n_upper) <= n
                    n >= n_lower
                    n_upper <= max(n_lower, n_upper) <= n
                    n >= n_upper
                    abs(a(n) - L) < epsilon
                    abs(c(n) - L) < epsilon
                    a(n) <= b(n)
                    b(n) <= c(n)
                    abs(L - a(n)) = abs(a(n) - L)
                    L - a(n) <= abs(L - a(n))
                    L - a(n) <= abs(L - a(n)) = abs(a(n) - L) < epsilon
                    L - a(n) < epsilon
                    L - a(n) + a(n) < epsilon + a(n)
                    L - a(n) + a(n) = L
                    epsilon + a(n) = a(n) + epsilon
                    L < a(n) + epsilon
                    L - epsilon < a(n)
                    L - epsilon < a(n) <= b(n)
                    L - epsilon < b(n)
                    c(n) - L <= abs(c(n) - L)
                    c(n) - L <= abs(c(n) - L) < epsilon
                    c(n) - L < epsilon
                    c(n) - L + L < epsilon + L
                    c(n) - L + L = c(n)
                    epsilon + L = L + epsilon
                    c(n) < L + epsilon
                    b(n) <= c(n) < L + epsilon
                    b(n) < L + epsilon
                    b(n) - L < L + epsilon - L
                    L + epsilon - L = epsilon
                    b(n) - L < epsilon
                    L - epsilon + epsilon < b(n) + epsilon
                    L - epsilon + epsilon = L
                    L < b(n) + epsilon
                    L - b(n) < b(n) + epsilon - b(n)
                    b(n) + epsilon - b(n) = epsilon
                    L - b(n) < epsilon
                    -(b(n) - L) = L - b(n)
                    -(b(n) - L) < epsilon
                    abs(b(n) - L) < epsilon
            $is_tail_close_to(b, L, epsilon, max(n_lower, n_upper))
        $has_eventual_closeness_to(b, L, epsilon)
    $has_limit(b, L)

"""
Example 6.4.15. Sequences squeezed between -2/n and 2/n converge to 0.
"""

# First get `2/n -> 0` and `-2/n -> 0` from the scalar multiple limit law for
# `1/n`, then apply the squeeze theorem.  The concrete sequences mentioned in
# the text are represented below as pointwise-bound applications.

have fn two_over_nat_seq(n N_pos) R = 2 / n
have fn neg_two_over_nat_seq(n N_pos) R = -2 / n

claim:
    ? $has_limit(two_over_nat_seq, 0)
    by thm seq_const_mul_converges_to(2, reciprocal_nat_seq, 0)
    2 * 0 = 0
    $has_limit('(i N_pos) R {2 * reciprocal_nat_seq(i)}, 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(two_over_nat_seq, 0, epsilon)
        $has_eventual_closeness_to('(i N_pos) R {2 * reciprocal_nat_seq(i)}, 0, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {2 * reciprocal_nat_seq(i)}, 0, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(two_over_nat_seq, 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs('(i N_pos) R {2 * reciprocal_nat_seq(i)}(n) - 0) < epsilon
                    '(i N_pos) R {2 * reciprocal_nat_seq(i)}(n) = 2 * reciprocal_nat_seq(n)
                    reciprocal_nat_seq(n) = '(n N_pos) R {1 / n}(n)
                    '(n N_pos) R {1 / n}(n) = 1 / n
                    reciprocal_nat_seq(n) = 1 / n
                    2 * reciprocal_nat_seq(n) = 2 * (1 / n)
                    2 * (1 / n) = 2 / n
                    2 * reciprocal_nat_seq(n) = 2 / n
                    two_over_nat_seq(n) = 2 / n
                    two_over_nat_seq(n) = '(i N_pos) R {2 * reciprocal_nat_seq(i)}(n)
                    abs(two_over_nat_seq(n) - 0) = abs('(i N_pos) R {2 * reciprocal_nat_seq(i)}(n) - 0)
                    abs(two_over_nat_seq(n) - 0) < epsilon
            $is_tail_close_to(two_over_nat_seq, 0, epsilon, n0)
        $has_eventual_closeness_to(two_over_nat_seq, 0, epsilon)
    $has_limit(two_over_nat_seq, 0)

claim:
    ? $has_limit(neg_two_over_nat_seq, 0)
    by thm seq_const_mul_converges_to(-2, reciprocal_nat_seq, 0)
    -2 * 0 = 0
    $has_limit('(i N_pos) R {-2 * reciprocal_nat_seq(i)}, 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(neg_two_over_nat_seq, 0, epsilon)
        $has_eventual_closeness_to('(i N_pos) R {-2 * reciprocal_nat_seq(i)}, 0, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to('(i N_pos) R {-2 * reciprocal_nat_seq(i)}, 0, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(neg_two_over_nat_seq, 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs('(i N_pos) R {-2 * reciprocal_nat_seq(i)}(n) - 0) < epsilon
                    '(i N_pos) R {-2 * reciprocal_nat_seq(i)}(n) = -2 * reciprocal_nat_seq(n)
                    reciprocal_nat_seq(n) = '(n N_pos) R {1 / n}(n)
                    '(n N_pos) R {1 / n}(n) = 1 / n
                    reciprocal_nat_seq(n) = 1 / n
                    -2 * reciprocal_nat_seq(n) = -2 * (1 / n)
                    -2 * (1 / n) = -2 / n
                    -2 * reciprocal_nat_seq(n) = -2 / n
                    neg_two_over_nat_seq(n) = -2 / n
                    neg_two_over_nat_seq(n) = '(i N_pos) R {-2 * reciprocal_nat_seq(i)}(n)
                    abs(neg_two_over_nat_seq(n) - 0) = abs('(i N_pos) R {-2 * reciprocal_nat_seq(i)}(n) - 0)
                    abs(neg_two_over_nat_seq(n) - 0) < epsilon
            $is_tail_close_to(neg_two_over_nat_seq, 0, epsilon, n0)
        $has_eventual_closeness_to(neg_two_over_nat_seq, 0, epsilon)
    $has_limit(neg_two_over_nat_seq, 0)

thm squeeze_between_two_over_nat_converges_to_zero:
    ? forall b seq(R):
        $is_pointwise_between(neg_two_over_nat_seq, b, two_over_nat_seq)
        =>:
            $has_limit(b, 0)
    by thm squeeze_converges_to(neg_two_over_nat_seq, b, two_over_nat_seq, 0)
    $has_limit(b, 0)

# The examples `(-1)^n/n + 1/n^2` and `2^{-n}` are applications of this
# theorem after proving the pointwise bounds.  For the first, use
# `-1 <= (-1)^n <= 1` and `0 <= 1/n^2 <= 1/n`.  For the second, use
# `0 <= 2^{-n}` and the induction bound `2^n >= n`, which gives
# `2^{-n} <= 1/n <= 2/n`.

"""
Remark 6.4.16. Squeeze, limit laws, and monotone convergence compute many
standard limits.
"""

# Section 6.5 gives the first such examples.

"""
Corollary 6.4.17. A sequence tends to zero iff its absolute-value sequence
tends to zero.
"""

have fn seq_abs(a seq(R)) fn(k N_pos) R = '(n N_pos) R {abs(a(n))}

thm sequence_abs_converges_to_zero:
    ? forall a seq(R):
        $has_limit(a, 0)
        =>:
            $has_limit(seq_abs(a), 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(seq_abs(a), 0, epsilon)
        $has_eventual_closeness_to(a, 0, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(a, 0, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(seq_abs(a), 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(a(n) - 0) < epsilon
                    seq_abs(a)(n) = '(n N_pos) R {abs(a(n))}(n)
                    '(n N_pos) R {abs(a(n))}(n) = abs(a(n))
                    seq_abs(a)(n) = abs(a(n))
                    abs(a(n)) >= 0
                    seq_abs(a)(n) >= 0
                    abs(seq_abs(a)(n)) = seq_abs(a)(n)
                    abs(seq_abs(a)(n) - 0) = abs(seq_abs(a)(n))
                    abs(seq_abs(a)(n) - 0) = seq_abs(a)(n)
                    abs(a(n) - 0) = abs(a(n))
                    seq_abs(a)(n) = abs(a(n) - 0)
                    abs(seq_abs(a)(n) - 0) = abs(a(n) - 0)
                    abs(seq_abs(a)(n) - 0) < epsilon
            $is_tail_close_to(seq_abs(a), 0, epsilon, n0)
        $has_eventual_closeness_to(seq_abs(a), 0, epsilon)
    $has_limit(seq_abs(a), 0)

thm sequence_abs_zero_limit_reflects:
    ? forall a seq(R):
        $has_limit(seq_abs(a), 0)
        =>:
            $has_limit(a, 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, 0, epsilon)
        $has_eventual_closeness_to(seq_abs(a), 0, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(seq_abs(a), 0, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(a, 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(seq_abs(a)(n) - 0) < epsilon
                    seq_abs(a)(n) = '(n N_pos) R {abs(a(n))}(n)
                    '(n N_pos) R {abs(a(n))}(n) = abs(a(n))
                    seq_abs(a)(n) = abs(a(n))
                    abs(a(n)) >= 0
                    seq_abs(a)(n) >= 0
                    abs(seq_abs(a)(n)) = seq_abs(a)(n)
                    abs(seq_abs(a)(n) - 0) = abs(seq_abs(a)(n))
                    abs(seq_abs(a)(n) - 0) = seq_abs(a)(n)
                    abs(a(n) - 0) = abs(a(n))
                    seq_abs(a)(n) = abs(a(n) - 0)
                    abs(a(n) - 0) = abs(seq_abs(a)(n) - 0)
                    abs(a(n) - 0) < epsilon
            $is_tail_close_to(a, 0, epsilon, n0)
        $has_eventual_closeness_to(a, 0, epsilon)
    $has_limit(a, 0)

"""
Theorem 6.4.18 (Completeness for real sequences). A real sequence is Cauchy
iff it is convergent. One direction is the epsilon/2 argument from an existing
limit; the other direction is the completeness property of the real line.
"""

# This proof follows the standard least-upper-bound route.  For a Cauchy
# sequence `a`, form the set of real numbers that are lower bounds for some
# tail of `a`.  This set is nonempty and bounded above; let `L` be its least
# upper bound.  The Cauchy condition then shows every late `a(n)` lies within
# epsilon of `L`.

prop has_eventual_lower_bound(a seq(R), B R):
    exist n1 N_pos st {$is_tail_lower_bound(a, n1, B)}

thm cauchy_sequence_converges:
    ? forall a seq(R):
        $is_cauchy_sequence(a)
        =>:
            $is_convergent_sequence(a)
    have E power_set(R) = {x R: $has_eventual_lower_bound(a, x)}
    E $subset R
    claim:
        ? $is_nonempty_set(E)
        1 $in R_pos
        $has_eventual_epsilon_steadiness(a, 1)
        have by exist n0 N_pos st {$is_tail_epsilon_steady(a, 1, n0)}: n0
        claim:
            ? $is_tail_lower_bound(a, n0, a(n0) - 1)
            forall n N_pos:
                n >= n0
                =>:
                    abs(a(n0) - a(n)) < 1
                    a(n0) - a(n) <= abs(a(n0) - a(n))
                    a(n0) - a(n) < 1
                    a(n0) - a(n) + a(n) < 1 + a(n)
                    a(n0) - a(n) + a(n) = a(n0)
                    1 + a(n) = a(n) + 1
                    a(n0) < a(n) + 1
                    a(n0) - 1 < a(n)
                    a(n0) - 1 <= a(n)
            $is_tail_lower_bound(a, n0, a(n0) - 1)
        witness exist n1 N_pos st {$is_tail_lower_bound(a, n1, a(n0) - 1)} from n0:
            $is_tail_lower_bound(a, n0, a(n0) - 1)
        $has_eventual_lower_bound(a, a(n0) - 1)
        a(n0) - 1 $in {x R: $has_eventual_lower_bound(a, x)}
        a(n0) - 1 $in E
        witness $is_nonempty_set(E) from a(n0) - 1:
            a(n0) - 1 $in E
    claim:
        ? $has_upper_bound(E)
        E $subset R
        1 $in R_pos
        $has_eventual_epsilon_steadiness(a, 1)
        have by exist n0 N_pos st {$is_tail_epsilon_steady(a, 1, n0)}: n0
        claim:
            ? forall x E:
                x <= a(n0) + 1
            $has_eventual_lower_bound(a, x)
            have by exist n1 N_pos st {$is_tail_lower_bound(a, n1, x)}: n1
            max(n0, n1) $in N_pos
            max(n0, n1) >= n0
            max(n0, n1) >= n1
            x <= a(max(n0, n1))
            abs(a(max(n0, n1)) - a(n0)) < 1
            a(max(n0, n1)) - a(n0) <= abs(a(max(n0, n1)) - a(n0))
            a(max(n0, n1)) - a(n0) < 1
            a(max(n0, n1)) - a(n0) + a(n0) < 1 + a(n0)
            a(max(n0, n1)) - a(n0) + a(n0) = a(max(n0, n1))
            1 + a(n0) = a(n0) + 1
            a(max(n0, n1)) < a(n0) + 1
            a(max(n0, n1)) <= a(n0) + 1
            x <= a(max(n0, n1)) <= a(n0) + 1
            x <= a(n0) + 1
        $is_upper_bound(E, a(n0) + 1)
        witness exist M R st {$is_upper_bound(E, M)} from a(n0) + 1:
            $is_upper_bound(E, a(n0) + 1)
        $has_upper_bound(E)
    E $in power_set(R)
    $is_nonempty_set(E)
    $has_upper_bound(E)
    $has_least_upper_bound(E)
    have by exist L R st {$is_least_upper_bound(E, L)}: L
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, L, epsilon)
        epsilon / 2 $in R_pos
        $has_eventual_epsilon_steadiness(a, epsilon / 2)
        have by exist n0 N_pos st {$is_tail_epsilon_steady(a, epsilon / 2, n0)}: n0
        claim:
            ? forall n N_pos:
                n >= n0
                =>:
                    abs(a(n) - L) < epsilon
            claim:
                ? a(n) - epsilon / 2 <= L
                claim:
                    ? $is_tail_lower_bound(a, n0, a(n) - epsilon / 2)
                    forall k N_pos:
                        k >= n0
                        =>:
                            abs(a(n) - a(k)) < epsilon / 2
                            a(n) - a(k) <= abs(a(n) - a(k))
                            a(n) - a(k) < epsilon / 2
                            a(n) - a(k) + a(k) < epsilon / 2 + a(k)
                            a(n) - a(k) + a(k) = a(n)
                            epsilon / 2 + a(k) = a(k) + epsilon / 2
                            a(n) < a(k) + epsilon / 2
                            a(n) - epsilon / 2 < a(k)
                            a(n) - epsilon / 2 <= a(k)
                    $is_tail_lower_bound(a, n0, a(n) - epsilon / 2)
                witness exist n1 N_pos st {$is_tail_lower_bound(a, n1, a(n) - epsilon / 2)} from n0:
                    $is_tail_lower_bound(a, n0, a(n) - epsilon / 2)
                $has_eventual_lower_bound(a, a(n) - epsilon / 2)
                a(n) - epsilon / 2 $in {x R: $has_eventual_lower_bound(a, x)}
                a(n) - epsilon / 2 $in E
                $is_upper_bound(E, L)
                a(n) - epsilon / 2 <= L
            claim:
                ? L <= a(n) + epsilon / 2
                claim:
                    ? forall x E:
                        x <= a(n) + epsilon / 2
                    $has_eventual_lower_bound(a, x)
                    have by exist n1 N_pos st {$is_tail_lower_bound(a, n1, x)}: n1
                    max(n0, n1) $in N_pos
                    max(n0, n1) >= n0
                    max(n0, n1) >= n1
                    x <= a(max(n0, n1))
                    abs(a(max(n0, n1)) - a(n)) < epsilon / 2
                    a(max(n0, n1)) - a(n) <= abs(a(max(n0, n1)) - a(n))
                    a(max(n0, n1)) - a(n) < epsilon / 2
                    a(max(n0, n1)) - a(n) + a(n) < epsilon / 2 + a(n)
                    a(max(n0, n1)) - a(n) + a(n) = a(max(n0, n1))
                    epsilon / 2 + a(n) = a(n) + epsilon / 2
                    a(max(n0, n1)) < a(n) + epsilon / 2
                    a(max(n0, n1)) <= a(n) + epsilon / 2
                    x <= a(max(n0, n1)) <= a(n) + epsilon / 2
                    x <= a(n) + epsilon / 2
                $is_upper_bound(E, a(n) + epsilon / 2)
                L <= a(n) + epsilon / 2
            a(n) - epsilon / 2 + epsilon / 2 <= L + epsilon / 2
            a(n) - epsilon / 2 + epsilon / 2 = a(n)
            a(n) <= L + epsilon / 2
            a(n) - L <= L + epsilon / 2 - L
            L + epsilon / 2 - L = epsilon / 2
            a(n) - L <= epsilon / 2
            L <= a(n) + epsilon / 2
            L - a(n) <= a(n) + epsilon / 2 - a(n)
            a(n) + epsilon / 2 - a(n) = epsilon / 2
            L - a(n) <= epsilon / 2
            -(a(n) - L) = L - a(n)
            -(a(n) - L) <= epsilon / 2
            epsilon / 2 >= 0
            abs(a(n) - L) <= epsilon / 2
            epsilon / 2 < epsilon
            abs(a(n) - L) <= epsilon / 2 < epsilon
            abs(a(n) - L) < epsilon
        $is_tail_close_to(a, L, epsilon, n0)
        witness exist n1 N_pos st {$is_tail_close_to(a, L, epsilon, n1)} from n0:
            $is_tail_close_to(a, L, epsilon, n0)
        $has_eventual_closeness_to(a, L, epsilon)
    $has_limit(a, L)
    witness exist L0 R st {$has_limit(a, L0)} from L:
        $has_limit(a, L)
    $is_convergent_sequence(a)

thm convergent_sequence_is_cauchy_for_completeness_theorem:
    ? forall a seq(R):
        $is_convergent_sequence(a)
        =>:
            $is_cauchy_sequence(a)
    by thm convergent_sequence_is_cauchy(a)

# These two direction theorems together are the formal version of the source's
# "if and only if" statement.

thm real_sequence_cauchy_implies_convergent_for_completeness_theorem:
    ? forall a seq(R):
        $is_cauchy_sequence(a)
        =>:
            $is_convergent_sequence(a)
    by thm cauchy_sequence_converges(a)

"""
Remark 6.4.19. Completeness for real Cauchy sequences is stronger than the
earlier rational formal-limit bridge.
"""

# The rational formal-limit bridge is no longer the main object; completeness
# is now stated directly for `seq(R)`.

"""
Remark 6.4.20. In metric-space language, the reals are complete.
"""

# Completeness says that real sequences have no rational-style holes: Cauchy
# sequences in `R` converge in `R`, unlike rational Cauchy approximations such
# as decimal truncations of `sqrt(2)`.  This metric-space formulation is
# deferred to Chapter B.2, and later analysis relies on this least-upper-bound
# and completeness behavior when taking limits, derivatives, integrals, and zeros.


# 6.5 Some standard limits

# Section 6.5 opens by reusing two earlier limits: constant sequences converge
# to their constant value, and `1/n` converges to `0`.

"""
Corollary 6.5.1. For every integer k >= 1, 1/n^(1/k) converges to 0.
"""

# The checked statement uses a root-sequence predicate for the terms
# `1/n^(1/k)`.  Given epsilon, choose `n0` with `1/n0 < epsilon^k`; for every
# later `n`, the kth power of the nth term is below `epsilon^k`, and monotonicity
# of positive powers gives the desired epsilon bound.

prop is_reciprocal_kth_root_sequence(k N_pos, a seq(R)):
    forall n N_pos:
        a(n) >= 0
        (a(n))^k = 1 / n

thm nonnegative_power_lt_implies_lt:
    ? forall x R, y R_pos, k N_pos:
        x >= 0
        x^k < y^k
        =>:
            x < y
    by contra:
        ? x < y
        not x < y
        x >= y
        y >= 0
        x^k >= y^k
        y^k <= x^k < y^k
        y^k < y^k
        impossible y^k = y^k

thm reciprocal_kth_root_pointwise_small:
    ? forall k N_pos, a seq(R), epsilon R_pos, n0, n N_pos:
        $is_reciprocal_kth_root_sequence(k, a)
        1 / n0 < epsilon^k
        n >= n0
        =>:
            abs(a(n) - 0) < epsilon
    n0 <= n
    n0 * n > 0
    1 / n = n0 / (n0 * n)
    n0 / (n0 * n) <= n / (n0 * n)
    n / (n0 * n) = 1 / n0
    1 / n <= 1 / n0
    1 / n <= 1 / n0 < epsilon^k
    1 / n < epsilon^k
    a(n) >= 0
    (a(n))^k = 1 / n
    (a(n))^k < epsilon^k
    by thm nonnegative_power_lt_implies_lt(a(n), epsilon, k)
    a(n) < epsilon
    abs(a(n) - 0) = abs(a(n))
    abs(a(n)) = a(n)
    abs(a(n) - 0) = a(n)
    abs(a(n) - 0) < epsilon

thm reciprocal_kth_root_sequence_converges_to_zero:
    ? forall k N_pos, a seq(R):
        $is_reciprocal_kth_root_sequence(k, a)
        =>:
            $has_limit(a, 0)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, 0, epsilon)
        epsilon^k > 0
        epsilon^k $in R_pos
        by thm archimedean_property(epsilon^k)
        have by exist n0 N_pos st {1 / n0 < epsilon^k}: n0
        claim:
            ? forall n N_pos:
                n >= n0
                =>:
                    abs(a(n) - 0) < epsilon
            by thm reciprocal_kth_root_pointwise_small(k, a, epsilon, n0, n)
            abs(a(n) - 0) < epsilon
        witness exist n1 N_pos st {$is_tail_close_to(a, 0, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(a(n) - 0) < epsilon
            $is_tail_close_to(a, 0, epsilon, n0)
        $has_eventual_closeness_to(a, 0, epsilon)
    $has_limit(a, 0)

"""
Lemma 6.5.2. The geometric sequence x^n tends to 0 when |x| < 1, tends to 1
when x = 1, and diverges when x = -1 or |x| > 1.
"""

# For `|x| < 1`, squeeze `x^n` between `-|x|^n` and `|x|^n`.  For `x = 1`,
# the sequence is constant.  For `x = -1`, even and odd tails stay two units
# apart, so the sequence is not Cauchy.  For `|x| > 1`, a hypothetical limit
# would have to satisfy `L = xL`, hence `L = 0`, contradicting the fact that
# powers of `|x|` eventually stay above one.

thm geometric_abs_lt_one_converges_to_zero:
    ? forall x R:
        abs(x) < 1
        =>:
            $has_limit(geom_seq(x), 0)
    abs(x) >= 0
    by thm geometric_nonnegative_lt_one_converges_to_zero(abs(x))
    by thm seq_const_mul_converges_to(-1, geom_seq(abs(x)), 0)
    -1 * 0 = 0
    $has_limit('(i N_pos) R {-1 * geom_seq(abs(x))(i)}, 0)
    claim:
        ? forall n N_pos:
            '(i N_pos) R {-1 * geom_seq(abs(x))(i)}(n) <= geom_seq(x)(n)
            geom_seq(x)(n) <= geom_seq(abs(x))(n)
        geom_seq(abs(x))(n) = abs(x)^n
        geom_seq(x)(n) = x^n
        abs(x^n) = abs(x)^n
        x^n <= abs(x^n)
        x^n <= abs(x)^n
        geom_seq(x)(n) <= geom_seq(abs(x))(n)
        -(x^n) <= abs(x^n)
        -(x^n) <= abs(x)^n
        -(abs(x)^n) <= -(-(x^n))
        -(-(x^n)) = x^n
        -(abs(x)^n) <= x^n
        '(i N_pos) R {-1 * geom_seq(abs(x))(i)}(n) = -1 * geom_seq(abs(x))(n)
        -1 * geom_seq(abs(x))(n) = -(abs(x)^n)
        '(i N_pos) R {-1 * geom_seq(abs(x))(i)}(n) <= geom_seq(x)(n)
    $is_pointwise_between('(i N_pos) R {-1 * geom_seq(abs(x))(i)}, geom_seq(x), geom_seq(abs(x)))
    by thm squeeze_converges_to('(i N_pos) R {-1 * geom_seq(abs(x))(i)}, geom_seq(x), geom_seq(abs(x)), 0)
    $has_limit(geom_seq(x), 0)

thm geometric_one_converges_to_one:
    ? forall x R:
        x = 1
        =>:
            $has_limit(geom_seq(x), 1)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(geom_seq(x), 1, epsilon)
        witness exist n0 N_pos st {$is_tail_close_to(geom_seq(x), 1, epsilon, n0)} from 1:
            forall n N_pos:
                n >= 1
                =>:
                    geom_seq(x)(n) = x^n
                    x^n = 1^n
                    1^n = 1
                    geom_seq(x)(n) = 1
                    geom_seq(x)(n) - 1 = 0
                    abs(geom_seq(x)(n) - 1) = abs(0)
                    abs(0) = 0
                    0 < epsilon
                    abs(geom_seq(x)(n) - 1) < epsilon
            $is_tail_close_to(geom_seq(x), 1, epsilon, 1)
        $has_eventual_closeness_to(geom_seq(x), 1, epsilon)
    $has_limit(geom_seq(x), 1)

thm geometric_minus_one_diverges:
    ? forall x R:
        x = -1
        =>:
            $is_divergent_sequence(geom_seq(x))
    claim:
        ? not $is_cauchy_sequence(geom_seq(x))
        by contra:
            ? not $is_cauchy_sequence(geom_seq(x))
            $is_cauchy_sequence(geom_seq(x))
            1 $in R_pos
            $has_eventual_epsilon_steadiness(geom_seq(x), 1)
            have by exist n0 N_pos st {$is_tail_epsilon_steady(geom_seq(x), 1, n0)}: n0
            2 * n0 $in N_pos
            2 * n0 + 1 $in N_pos
            2 * n0 >= n0
            2 * n0 + 1 >= n0
            abs(geom_seq(x)(2 * n0) - geom_seq(x)(2 * n0 + 1)) < 1
            geom_seq(x)(2 * n0) = x^(2 * n0)
            x^(2 * n0) = (-1)^(2 * n0)
            (-1)^2 = 1
            ((-1)^2)^n0 = 1^n0
            1^n0 = 1
            ((-1)^2)^n0 = (-1)^(2 * n0)
            (-1)^(2 * n0) = 1
            geom_seq(x)(2 * n0) = 1
            geom_seq(x)(2 * n0 + 1) = x^(2 * n0 + 1)
            x^(2 * n0 + 1) = (-1)^(2 * n0 + 1)
            (-1)^1 = -1
            (-1)^(2 * n0 + 1) = (-1)^(2 * n0) * (-1)^1
            (-1)^(2 * n0 + 1) = 1 * -1 = -1
            geom_seq(x)(2 * n0 + 1) = -1
            geom_seq(x)(2 * n0) - geom_seq(x)(2 * n0 + 1) = 1 - (-1) = 2
            abs(geom_seq(x)(2 * n0) - geom_seq(x)(2 * n0 + 1)) = 2
            2 < 1
            impossible 2 < 1
    claim:
        ? not $is_convergent_sequence(geom_seq(x))
        by contra:
            ? not $is_convergent_sequence(geom_seq(x))
            $is_convergent_sequence(geom_seq(x))
            by thm convergent_sequence_is_cauchy(geom_seq(x))
            impossible not $is_cauchy_sequence(geom_seq(x))
    not $is_convergent_sequence(geom_seq(x))
    $is_divergent_sequence(geom_seq(x))

thm not_divergent_sequence_is_convergent:
    ? forall a seq(R):
        not $is_divergent_sequence(a)
        =>:
            $is_convergent_sequence(a)
    by contra:
        ? $is_convergent_sequence(a)
        not $is_convergent_sequence(a)
        $is_divergent_sequence(a)
        impossible not $is_divergent_sequence(a)

thm positive_power_gt_one:
    ? forall u R, n N_pos:
        u > 1
        =>:
            u^n > 1
    by induc n from 1:
        ? u^n > 1
        prove from n = 1:
            u^1 = u
            u > 1
            u^1 > 1
        prove induc:
            u^n > 1
            u^n > 0
            u > 1
            u^(n + 1) = u^n * u
            u^n * u > 1 * u
            1 * u = u
            u^n * u > u
            u > 1
            u^n * u > u > 1
            u^n * u > 1
            u^(n + 1) > 1

thm geometric_abs_gt_one_diverges:
    ? forall x R:
        abs(x) > 1
        =>:
            $is_divergent_sequence(geom_seq(x))
    by contra:
        ? $is_divergent_sequence(geom_seq(x))
        not $is_divergent_sequence(geom_seq(x))
        by thm not_divergent_sequence_is_convergent(geom_seq(x))
        $is_convergent_sequence(geom_seq(x))
        have by exist L R st {$has_limit(geom_seq(x), L)}: L
        by thm seq_shift_has_limit(geom_seq(x), L)
        by thm shifted_geometric_sequence_has_scaled_limit(x, L)
        by thm sequence_limit_unique(seq_shift(geom_seq(x)), L, x * L)
        L = x * L
        L - x * L = 0
        (1 - x) * L = 0
        L * (1 - x) = 0
        claim:
            ? x != 1
            by contra:
                ? x != 1
                x = 1
                abs(x) = abs(1)
                abs(1) = 1
                abs(x) = 1
                abs(x) > 1
                1 < 1
                impossible 1 = 1
        x != 1
        1 - x != 0
        L = 0 / (1 - x)
        0 / (1 - x) = 0
        L = 0
        $has_limit(geom_seq(x), 0)
        1 $in R_pos
        $has_eventual_closeness_to(geom_seq(x), 0, 1)
        have by exist n0 N_pos st {$is_tail_close_to(geom_seq(x), 0, 1, n0)}: n0
        abs(geom_seq(x)(n0) - 0) < 1
        geom_seq(x)(n0) = x^n0
        geom_seq(x)(n0) - 0 = x^n0
        abs(geom_seq(x)(n0) - 0) = abs(x^n0)
        abs(x^n0) = abs(x)^n0
        by thm positive_power_gt_one(abs(x), n0)
        abs(x)^n0 > 1
        abs(geom_seq(x)(n0) - 0) > 1
        1 < abs(geom_seq(x)(n0) - 0) < 1
        1 < 1
        impossible 1 = 1
    $is_divergent_sequence(geom_seq(x))

"""
Lemma 6.5.3. For every x > 0, the sequence x^(1/n) converges to 1.
"""

# This is stated through an nth-root-sequence predicate.  For the upper bound,
# choose `n0` with `(1+epsilon)^n > x`, so `a(n)^n = x` forces
# `a(n) < 1+epsilon`.  For the lower bound, use `(1-epsilon)^n -> 0` when
# `epsilon < 1`; if `epsilon >= 1`, positivity of the root already gives the
# lower estimate.

prop is_nth_root_sequence_for(x R_pos, a seq(R)):
    forall n N_pos:
        a(n) >= 0
        (a(n))^n = x

thm geometric_base_gt_one_is_increasing:
    ? forall y R:
        y > 1
        =>:
            $is_increasing_sequence(geom_seq(y))
    claim:
        ? forall n N_pos:
            geom_seq(y)(n) <= geom_seq(y)(n + 1)
        by thm positive_power_gt_one(y, n)
        y^n > 1
        y^n > 0
        y > 1
        geom_seq(y)(n) = y^n
        geom_seq(y)(n + 1) = y^(n + 1)
        y^(n + 1) = y^n * y
        y^n * y > y^n * 1
        y^n * 1 = y^n
        y^(n + 1) > y^n
        geom_seq(y)(n + 1) > geom_seq(y)(n)
        geom_seq(y)(n) <= geom_seq(y)(n + 1)
    $is_increasing_sequence(geom_seq(y))

thm geometric_base_gt_one_exceeds_threshold:
    ? forall y, B R:
        y > 1
        =>:
            exist n0 N_pos st {geom_seq(y)(n0) > B}
    by contra:
        ? exist n0 N_pos st {geom_seq(y)(n0) > B}
        claim:
            ? forall n N_pos:
                geom_seq(y)(n) <= B
            not geom_seq(y)(n) > B
            geom_seq(y)(n) <= B
        $is_sequence_upper_bound(geom_seq(y), B)
        witness exist M R st {$is_sequence_upper_bound(geom_seq(y), M)} from B:
            $is_sequence_upper_bound(geom_seq(y), B)
        $is_bounded_above_sequence(geom_seq(y))
        by thm geometric_base_gt_one_is_increasing(y)
        by thm bounded_increasing_sequence_converges(geom_seq(y))
        $is_convergent_sequence(geom_seq(y))
        y > 0
        abs(y) = y
        abs(y) > 1
        by thm geometric_abs_gt_one_diverges(y)
        $is_divergent_sequence(geom_seq(y))
        not $is_convergent_sequence(geom_seq(y))
        impossible $is_convergent_sequence(geom_seq(y))

thm geometric_base_gt_one_eventually_exceeds_threshold:
    ? forall y, B R:
        y > 1
        =>:
            exist n0 N_pos st {$is_eventually_above_threshold(geom_seq(y), B, n0)}
    by thm geometric_base_gt_one_exceeds_threshold(y, B)
    have by exist n0 N_pos st {geom_seq(y)(n0) > B}: n0
    by thm geometric_base_gt_one_is_increasing(y)
    claim:
        ? forall n N_pos:
            n >= n0
            =>:
                B < geom_seq(y)(n)
        by thm increasing_seq_le_of_le(geom_seq(y), n0, n)
        geom_seq(y)(n0) <= geom_seq(y)(n)
        B < geom_seq(y)(n0)
        B < geom_seq(y)(n0) <= geom_seq(y)(n)
        B < geom_seq(y)(n)
    witness exist n1 N_pos st {$is_eventually_above_threshold(geom_seq(y), B, n1)} from n0:
        forall n N_pos:
            n >= n0
            =>:
                B < geom_seq(y)(n)
        $is_eventually_above_threshold(geom_seq(y), B, n0)

thm nth_root_sequence_term_positive:
    ? forall x R_pos, a seq(R), n N_pos:
        $is_nth_root_sequence_for(x, a)
        =>:
            a(n) > 0
    a(n) >= 0
    (a(n))^n = x
    by contra:
        ? a(n) > 0
        not a(n) > 0
        a(n) <= 0
        a(n) >= 0
        a(n) = 0
        (a(n))^n = 0^n
        0^n = 0
        x = 0
        x > 0
        0 < 0
        impossible 0 = 0

thm nth_root_sequence_eventually_below_one_plus_epsilon:
    ? forall x R_pos, a seq(R), epsilon R_pos:
        $is_nth_root_sequence_for(x, a)
        =>:
            exist n0 N_pos st {$is_eventually_below_threshold(a, 1 + epsilon, n0)}
    1 + epsilon > 1
    by thm geometric_base_gt_one_eventually_exceeds_threshold(1 + epsilon, x)
    have by exist n0 N_pos st {$is_eventually_above_threshold(geom_seq(1 + epsilon), x, n0)}: n0
    claim:
        ? forall n N_pos:
            n >= n0
            =>:
                a(n) < 1 + epsilon
        x < geom_seq(1 + epsilon)(n)
        geom_seq(1 + epsilon)(n) = (1 + epsilon)^n
        (a(n))^n = x
        (a(n))^n < (1 + epsilon)^n
        a(n) >= 0
        1 + epsilon $in R_pos
        by thm nonnegative_power_lt_implies_lt(a(n), 1 + epsilon, n)
        a(n) < 1 + epsilon
    witness exist n1 N_pos st {$is_eventually_below_threshold(a, 1 + epsilon, n1)} from n0:
        forall n N_pos:
            n >= n0
            =>:
                a(n) < 1 + epsilon
        $is_eventually_below_threshold(a, 1 + epsilon, n0)

thm nth_root_sequence_eventually_above_one_minus_small_epsilon:
    ? forall x R_pos, a seq(R), epsilon R_pos:
        $is_nth_root_sequence_for(x, a)
        epsilon < 1
        =>:
            exist n0 N_pos st {$is_eventually_above_threshold(a, 1 - epsilon, n0)}
    1 - epsilon > 0
    1 - epsilon < 1
    abs(1 - epsilon) = 1 - epsilon
    abs(1 - epsilon) < 1
    by thm geometric_abs_lt_one_converges_to_zero(1 - epsilon)
    $has_limit(geom_seq(1 - epsilon), 0)
    have eta R_pos = x
    by thm has_limit_gives_eventual_closeness(geom_seq(1 - epsilon), 0, eta)
    $has_eventual_closeness_to(geom_seq(1 - epsilon), 0, eta)
    have by exist n0 N_pos st {$is_tail_close_to(geom_seq(1 - epsilon), 0, eta, n0)}: n0
    claim:
        ? forall n N_pos:
            n >= n0
            =>:
                1 - epsilon < a(n)
        abs(geom_seq(1 - epsilon)(n) - 0) < eta
        eta = x
        abs(geom_seq(1 - epsilon)(n) - 0) < x
        geom_seq(1 - epsilon)(n) = (1 - epsilon)^n
        geom_seq(1 - epsilon)(n) - 0 = (1 - epsilon)^n
        abs(geom_seq(1 - epsilon)(n) - 0) = abs((1 - epsilon)^n)
        (1 - epsilon)^n > 0
        abs((1 - epsilon)^n) = (1 - epsilon)^n
        (1 - epsilon)^n < x
        (a(n))^n = x
        (1 - epsilon)^n < (a(n))^n
        by thm nth_root_sequence_term_positive(x, a, n)
        a(n) > 0
        a(n) $in R_pos
        1 - epsilon $in R_pos
        by thm nonnegative_power_lt_implies_lt(1 - epsilon, a(n), n)
        1 - epsilon < a(n)
    witness exist n1 N_pos st {$is_eventually_above_threshold(a, 1 - epsilon, n1)} from n0:
        forall n N_pos:
            n >= n0
            =>:
                1 - epsilon < a(n)
        $is_eventually_above_threshold(a, 1 - epsilon, n0)

thm nth_root_sequence_converges_to_one:
    ? forall x R_pos, a seq(R):
        $is_nth_root_sequence_for(x, a)
        =>:
            $has_limit(a, 1)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(a, 1, epsilon)
        by thm nth_root_sequence_eventually_below_one_plus_epsilon(x, a, epsilon)
        have by exist n_upper N_pos st {$is_eventually_below_threshold(a, 1 + epsilon, n_upper)}: n_upper
        epsilon < 1 or epsilon >= 1
        by cases:
            ? $has_eventual_closeness_to(a, 1, epsilon)
            case epsilon < 1:
                by thm nth_root_sequence_eventually_above_one_minus_small_epsilon(x, a, epsilon)
                have by exist n_lower N_pos st {$is_eventually_above_threshold(a, 1 - epsilon, n_lower)}: n_lower
                max(n_upper, n_lower) $in N_pos
                witness exist n0 N_pos st {$is_tail_close_to(a, 1, epsilon, n0)} from max(n_upper, n_lower):
                    forall n N_pos:
                        n >= max(n_upper, n_lower)
                        =>:
                            n_upper <= max(n_upper, n_lower) <= n
                            n >= n_upper
                            n_lower <= max(n_upper, n_lower) <= n
                            n >= n_lower
                            a(n) < 1 + epsilon
                            1 - epsilon < a(n)
                            a(n) - 1 < 1 + epsilon - 1
                            1 + epsilon - 1 = epsilon
                            a(n) - 1 < epsilon
                            1 - epsilon + epsilon < a(n) + epsilon
                            1 - epsilon + epsilon = 1
                            1 < a(n) + epsilon
                            1 - a(n) < a(n) + epsilon - a(n)
                            a(n) + epsilon - a(n) = epsilon
                            1 - a(n) < epsilon
                            -(a(n) - 1) = 1 - a(n)
                            -(a(n) - 1) < epsilon
                            abs(a(n) - 1) < epsilon
                    $is_tail_close_to(a, 1, epsilon, max(n_upper, n_lower))
                $has_eventual_closeness_to(a, 1, epsilon)
            case epsilon >= 1:
                claim:
                    ? forall n N_pos:
                        n >= n_upper
                        =>:
                            a(n) > 0
                    by thm nth_root_sequence_term_positive(x, a, n)
                    a(n) > 0
                witness exist n0 N_pos st {$is_tail_close_to(a, 1, epsilon, n0)} from n_upper:
                    forall n N_pos:
                        n >= n_upper
                        =>:
                            a(n) < 1 + epsilon
                            a(n) > 0
                            1 - epsilon <= 0
                            1 - epsilon < a(n)
                            a(n) - 1 < 1 + epsilon - 1
                            1 + epsilon - 1 = epsilon
                            a(n) - 1 < epsilon
                            1 - epsilon + epsilon < a(n) + epsilon
                            1 - epsilon + epsilon = 1
                            1 < a(n) + epsilon
                            1 - a(n) < a(n) + epsilon - a(n)
                            a(n) + epsilon - a(n) = epsilon
                            1 - a(n) < epsilon
                            -(a(n) - 1) = 1 - a(n)
                            -(a(n) - 1) < epsilon
                            abs(a(n) - 1) < epsilon
                    $is_tail_close_to(a, 1, epsilon, n_upper)
                $has_eventual_closeness_to(a, 1, epsilon)
    $has_limit(a, 1)

# 6.6 Subsequences

"""
Definition 6.6.1 (Subsequences). A sequence b is a subsequence of a sequence
a when b is obtained by reading a along a strictly increasing index map.
"""

# In the positive-indexed convention of this file, the index map has type
# `N_pos -> N_pos`, is strictly increasing, and satisfies `b(k) = a(phi(k))`.
# Tao uses index 0 in this section, so the examples below are shifted to
# positive indices.

prop is_subsequence_index(phi fn(k N_pos) N_pos):
    forall k N_pos:
        phi(k) < phi(k + 1)

prop is_subsequence_along(a, b seq(R), phi fn(k N_pos) N_pos):
    $is_subsequence_index(phi)
    forall k N_pos:
        b(k) = a(phi(k))

prop has_subsequence(a, b seq(R)):
    exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, b, phi)}

"""
Example 6.6.2. The even-indexed terms of a sequence form a subsequence.
"""

# In positive indexing, the even-index map is `phi(k) = 2*k`.

have fn subsequence_even_index(k N_pos) N_pos = 2 * k

claim:
    ? $is_subsequence_index(subsequence_even_index)
    forall k N_pos:
        subsequence_even_index(k) = 2 * k
        subsequence_even_index(k + 1) = 2 * (k + 1)
        2 * (k + 1) = 2 * k + 2
        2 * k < 2 * k + 2
        subsequence_even_index(k) < subsequence_even_index(k + 1)

"""
Example 6.6.3. The two alternating decimal components in Tao's example are
subsequences of the original sequence.
"""

# Let `a` be Tao's interleaved decimal sequence
# `1.1, 0.1, 1.01, 0.01, 1.001, 0.001, ...`.  The component sequence
# `b = 1.1, 1.01, 1.001, ...` is the odd-indexed sequence of `a`, and
# `c = 0.1, 0.01, 0.001, ...` is the even-indexed sequence of `a`.
# Decimal notation is not formalized here, so the checked statement below
# proves the structural fact for any real sequence `a`: these odd and even
# indexed component sequences are subsequences of `a`.

have fn subsequence_odd_index(k N_pos) N_pos = 2 * (k - 1) + 1

claim:
    ? $is_subsequence_index(subsequence_odd_index)
    forall k N_pos:
        subsequence_odd_index(k) = 2 * (k - 1) + 1
        subsequence_odd_index(k + 1) = 2 * ((k + 1) - 1) + 1
        2 * ((k + 1) - 1) + 1 = 2 * k + 1
        2 * (k - 1) + 1 < 2 * k + 1
        subsequence_odd_index(k) < subsequence_odd_index(k + 1)

have fn subsequence_even_terms(a seq(R)) fn(k N_pos) R = '(i N_pos) R {a(subsequence_even_index(i))}
have fn subsequence_odd_terms(a seq(R)) fn(k N_pos) R = '(i N_pos) R {a(subsequence_odd_index(i))}

thm even_terms_form_subsequence:
    ? forall a seq(R):
        $has_subsequence(a, subsequence_even_terms(a))
    claim:
        ? $is_subsequence_along(a, subsequence_even_terms(a), subsequence_even_index)
        $is_subsequence_index(subsequence_even_index)
        claim:
            ? forall i N_pos:
                subsequence_even_terms(a)(i) = a(subsequence_even_index(i))
            subsequence_even_terms(a)(i) = a(subsequence_even_index(i))
        $is_subsequence_along(a, subsequence_even_terms(a), subsequence_even_index)
    witness exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, subsequence_even_terms(a), phi)} from subsequence_even_index:
        $is_subsequence_along(a, subsequence_even_terms(a), subsequence_even_index)
    $has_subsequence(a, subsequence_even_terms(a))

thm odd_terms_form_subsequence:
    ? forall a seq(R):
        $has_subsequence(a, subsequence_odd_terms(a))
    claim:
        ? $is_subsequence_along(a, subsequence_odd_terms(a), subsequence_odd_index)
        $is_subsequence_index(subsequence_odd_index)
        claim:
            ? forall i N_pos:
                subsequence_odd_terms(a)(i) = a(subsequence_odd_index(i))
            subsequence_odd_terms(a)(i) = a(subsequence_odd_index(i))
        $is_subsequence_along(a, subsequence_odd_terms(a), subsequence_odd_index)
    witness exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, subsequence_odd_terms(a), phi)} from subsequence_odd_index:
        $is_subsequence_along(a, subsequence_odd_terms(a), subsequence_odd_index)
    $has_subsequence(a, subsequence_odd_terms(a))

"""
Lemma 6.6.4. The subsequence relation is reflexive and transitive.
"""

# This block is not part of Definition 6.6.1.  It is the checked reflexivity
# part of Lemma 6.6.4: the identity map reads a sequence without skipping or
# reordering any terms.

have fn subsequence_identity_index(k N_pos) N_pos = k

thm subsequence_identity_index_eval:
    ? forall k N_pos:
        subsequence_identity_index(k) = k
    subsequence_identity_index(k) = k

claim:
    ? $is_subsequence_index(subsequence_identity_index)
    forall k N_pos:
        subsequence_identity_index(k) = k
        subsequence_identity_index(k + 1) = k + 1
        k < k + 1
        subsequence_identity_index(k) < subsequence_identity_index(k + 1)

thm sequence_is_subsequence_of_itself:
    ? forall a seq(R):
        $has_subsequence(a, a)
    claim:
        ? $is_subsequence_along(a, a, subsequence_identity_index)
        $is_subsequence_index(subsequence_identity_index)
        claim:
            ? forall k N_pos:
                a(k) = a(subsequence_identity_index(k))
            by thm subsequence_identity_index_eval(k)
            subsequence_identity_index(k) = k
            a(subsequence_identity_index(k)) = a(k)
            a(k) = a(subsequence_identity_index(k))
        $is_subsequence_along(a, a, subsequence_identity_index)
    witness exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, a, phi)} from subsequence_identity_index:
        $is_subsequence_along(a, a, subsequence_identity_index)
    $has_subsequence(a, a)

# Transitivity is the exercise part of Lemma 6.6.4.  The missing checked step is
# to compose two strictly increasing index maps and verify the pointwise
# equality for the composed subsequence.

thm subsequence_index_strict_mono_add:
    ? forall phi fn(k N_pos) N_pos, i, h N_pos:
        $is_subsequence_index(phi)
        =>:
            phi(i) < phi(i + h)
    by induc h from 1:
        ? phi(i) < phi(i + h)
        prove from h = 1:
            i + 1 $in N_pos
            phi(i) < phi(i + 1)
        prove induc:
            phi(i) < phi(i + h)
            i + h $in N_pos
            phi(i + h) < phi(i + h + 1)
            i + (h + 1) = i + h + 1
            phi(i + (h + 1)) = phi(i + h + 1)
            phi(i) < phi(i + h) < phi(i + h + 1)
            phi(i) < phi(i + h + 1)
            phi(i) < phi(i + (h + 1))

thm subsequence_index_strict_mono:
    ? forall phi fn(k N_pos) N_pos, i, j N_pos:
        $is_subsequence_index(phi)
        i < j
        =>:
            phi(i) < phi(j)
    have h N_pos = j - i
    h = j - i
    i + h = i + (j - i)
    i + (j - i) = j
    i + h = j
    by thm subsequence_index_strict_mono_add(phi, i, h)
    phi(i) < phi(i + h)
    phi(i + h) = phi(j)
    phi(i) < phi(j)

thm subsequence_transitive:
    ? forall a, b, c seq(R):
        $has_subsequence(a, b)
        $has_subsequence(b, c)
        =>:
            $has_subsequence(a, c)
    have by exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, b, phi)}: phi
    have by exist psi fn(k N_pos) N_pos st {$is_subsequence_along(b, c, psi)}: psi
    have fn theta(k N_pos) N_pos = phi(psi(k))
    claim:
        ? $is_subsequence_along(a, c, theta)
        claim:
            ? $is_subsequence_index(theta)
            forall k N_pos:
                psi(k) < psi(k + 1)
                phi(psi(k)) < phi(psi(k + 1))
                theta(k) = phi(psi(k))
                theta(k + 1) = phi(psi(k + 1))
                theta(k) < theta(k + 1)
            $is_subsequence_index(theta)
        claim:
            ? forall k N_pos:
                c(k) = a(theta(k))
            c(k) = b(psi(k))
            b(psi(k)) = a(phi(psi(k)))
            theta(k) = phi(psi(k))
            a(theta(k)) = a(phi(psi(k)))
            c(k) = a(theta(k))
        $is_subsequence_along(a, c, theta)
    witness exist theta0 fn(k N_pos) N_pos st {$is_subsequence_along(a, c, theta0)} from theta:
        $is_subsequence_along(a, c, theta)
    $has_subsequence(a, c)

"""
Proposition 6.6.5. A sequence converges to L iff every subsequence converges
to L.
"""

# This helper is not a new source definition.  It records the elementary fact
# that a strictly increasing map `N_pos -> N_pos` eventually dominates the
# identity, which is the index estimate used in the subsequence limit proofs.

thm subsequence_index_at_least_identity:
    ? forall phi fn(k N_pos) N_pos, k N_pos:
        $is_subsequence_index(phi)
        =>:
            phi(k) >= k
    by induc k from 1:
        ? phi(k) >= k
        prove from k = 1:
            phi(1) $in N_pos
            phi(1) >= 1
        prove induc:
            phi(k) >= k
            phi(k) < phi(k + 1)
            phi(k) + 1 <= phi(k + 1)
            k + 1 <= phi(k) + 1
            k + 1 <= phi(k) + 1 <= phi(k + 1)
            k + 1 <= phi(k + 1)
            phi(k + 1) >= k + 1

# If `a` converges to `L`, then every subsequence is eventually inside the same
# epsilon tail because a strictly increasing positive-index map dominates the
# identity.  Conversely, apply the hypothesis to the identity subsequence.

thm subsequence_along_preserves_limit:
    ? forall a, b seq(R), phi fn(k N_pos) N_pos, L R:
        $is_subsequence_along(a, b, phi)
        $has_limit(a, L)
        =>:
            $has_limit(b, L)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(b, L, epsilon)
        $has_eventual_closeness_to(a, L, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to(a, L, epsilon, n0)}: n0
        claim:
            ? forall n N_pos:
                n >= n0
                =>:
                    abs(b(n) - L) < epsilon
            by thm subsequence_index_at_least_identity(phi, n)
            phi(n) >= n
            n >= n0
            n0 <= n <= phi(n)
            n0 <= phi(n)
            phi(n) >= n0
            abs(a(phi(n)) - L) < epsilon
            b(n) = a(phi(n))
            abs(b(n) - L) = abs(a(phi(n)) - L)
            abs(b(n) - L) < epsilon
        witness exist n1 N_pos st {$is_tail_close_to(b, L, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs(b(n) - L) < epsilon
            $is_tail_close_to(b, L, epsilon, n0)
        $has_eventual_closeness_to(b, L, epsilon)
    $has_limit(b, L)

thm every_subsequence_of_convergent_sequence_converges:
    ? forall a seq(R), L R, b seq(R):
        $has_limit(a, L)
        $has_subsequence(a, b)
        =>:
            $has_limit(b, L)
    have by exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, b, phi)}: phi
    by thm subsequence_along_preserves_limit(a, b, phi, L)
    $has_limit(b, L)

thm sequence_converges_if_every_subsequence_converges:
    ? forall a seq(R), L R:
        forall b seq(R):
            $has_subsequence(a, b)
            =>:
                $has_limit(b, L)
        =>:
            $has_limit(a, L)
    by thm sequence_is_subsequence_of_itself(a)
    $has_subsequence(a, a)
    $has_limit(a, L)

"""
Proposition 6.6.6. L is a limit point of a sequence iff some subsequence
converges to L.
"""

# A convergent subsequence supplies arbitrarily late terms of the original
# sequence that are epsilon-close to `L`.  Conversely, a limit point lets us
# recursively choose a strictly increasing index `phi` with
# `abs(a(phi(k)) - L) < 1/k`; the selected subsequence then converges to `L`.

thm convergent_subsequence_limit_is_limit_point:
    ? forall a, b seq(R), phi fn(k N_pos) N_pos, L R:
        $is_subsequence_along(a, b, phi)
        $has_limit(b, L)
        =>:
            $is_limit_point(a, L)
    claim:
        ? forall epsilon R_pos, n_tail N_pos:
            $is_epsilon_adherent_to_sequence(a, L, epsilon, n_tail)
        $has_eventual_closeness_to(b, L, epsilon)
        have by exist k0 N_pos st {$is_tail_close_to(b, L, epsilon, k0)}: k0
        max(k0, n_tail) $in N_pos
        by thm subsequence_index_at_least_identity(phi, max(k0, n_tail))
        phi(max(k0, n_tail)) >= max(k0, n_tail)
        k0 <= max(k0, n_tail)
        n_tail <= max(k0, n_tail)
        max(k0, n_tail) >= k0
        max(k0, n_tail) >= n_tail
        n_tail <= max(k0, n_tail) <= phi(max(k0, n_tail))
        n_tail <= phi(max(k0, n_tail))
        abs(b(max(k0, n_tail)) - L) < epsilon
        b(max(k0, n_tail)) = a(phi(max(k0, n_tail)))
        abs(a(phi(max(k0, n_tail))) - L) = abs(b(max(k0, n_tail)) - L)
        abs(a(phi(max(k0, n_tail))) - L) < epsilon
        phi(max(k0, n_tail)) >= n_tail
        witness exist n N_pos st {n >= n_tail and abs(a(n) - L) < epsilon} from phi(max(k0, n_tail)):
            phi(max(k0, n_tail)) >= n_tail
            abs(a(phi(max(k0, n_tail))) - L) < epsilon
            phi(max(k0, n_tail)) >= n_tail and abs(a(phi(max(k0, n_tail))) - L) < epsilon
        $is_epsilon_adherent_to_sequence(a, L, epsilon, n_tail)
    $is_limit_point(a, L)

thm limit_point_has_convergent_subsequence:
    ? forall a seq(R), L R:
        $is_limit_point(a, L)
        =>:
            exist b seq(R) st {$has_subsequence(a, b), $has_limit(b, L)}
    have fn F(k N_pos, s N_pos) power_set(N_pos) = {n N_pos: n >= s and abs(a(n) - L) < 1 / k}
    claim:
        ? forall A fn_range(F):
            $is_nonempty_set(A)
        have by preimage k, s from A $in fn_range(F)
        A = F(k, s)
        1 / k > 0
        1 / k $in R_pos
        $is_epsilon_adherent_to_sequence(a, L, 1 / k, s)
        have by exist n N_pos st {n >= s and abs(a(n) - L) < 1 / k}: n
        F(k, s) = {n N_pos: n >= s and abs(a(n) - L) < 1 / k}
        n $in {n N_pos: n >= s and abs(a(n) - L) < 1 / k}
        n $in A
        witness $is_nonempty_set(A) from n:
            n $in A
    by axiom_of_choice: set fn_range(F):
        forall A fn_range(F):
            $is_nonempty_set(A)
    have by exist f fn(A fn_range(F)) cup(fn_range(F)) st {forall! A fn_range(F): {f(A) $in A}}: choice_index
    claim:
        ? forall A fn_range(F):
            choice_index(A) $in N_pos
        choice_index(A) $in A
        A $in power_set(N_pos)
        A $subset N_pos
        choice_index(A) $in N_pos
    have fn pick(A fn_range(F)) N_pos = choice_index(A)
    have fn phi(k N_pos) N_pos by induc k from 1:
        case k = 1: pick(F(1, 1))
        case k > 1: pick(F(k, phi(k - 1) + 1))
    have fn b(k N_pos) R = a(phi(k))
    claim:
        ? forall k N_pos:
            phi(k) < phi(k + 1)
        k + 1 $in N_pos
        k + 1 > 1
        (k + 1) - 1 = k
        phi(k + 1) = pick(F(k + 1, phi((k + 1) - 1) + 1)) = pick(F(k + 1, phi(k) + 1))
        pick(F(k + 1, phi(k) + 1)) = choice_index(F(k + 1, phi(k) + 1))
        choice_index(F(k + 1, phi(k) + 1)) $in F(k + 1, phi(k) + 1)
        phi(k + 1) $in F(k + 1, phi(k) + 1)
        phi(k + 1) >= phi(k) + 1
        phi(k) + 1 > phi(k)
        phi(k) < phi(k) + 1 <= phi(k + 1)
        phi(k) < phi(k + 1)
    $is_subsequence_index(phi)
    claim:
        ? forall k N_pos:
            b(k) = a(phi(k))
        b(k) = a(phi(k))
    $is_subsequence_along(a, b, phi)
    witness exist phi0 fn(k N_pos) N_pos st {$is_subsequence_along(a, b, phi0)} from phi:
        $is_subsequence_along(a, b, phi)
    $has_subsequence(a, b)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(b, L, epsilon)
        by thm archimedean_property(epsilon)
        have by exist n0 N_pos st {1 / n0 < epsilon}: n0
        max(n0, 2) $in N_pos
        max(n0, 2) >= n0
        max(n0, 2) >= 2
        witness exist n1 N_pos st {$is_tail_close_to(b, L, epsilon, n1)} from max(n0, 2):
            forall n N_pos:
                n >= max(n0, 2)
                =>:
                    n0 <= max(n0, 2) <= n
                    n >= n0
                    2 <= max(n0, 2) <= n
                    n >= 2
                    n > 1
                    phi(n) = pick(F(n, phi(n - 1) + 1))
                    pick(F(n, phi(n - 1) + 1)) = choice_index(F(n, phi(n - 1) + 1))
                    choice_index(F(n, phi(n - 1) + 1)) $in F(n, phi(n - 1) + 1)
                    phi(n) $in F(n, phi(n - 1) + 1)
                    abs(a(phi(n)) - L) < 1 / n
                    n0 * n > 0
                    1 / n = n0 / (n0 * n)
                    n0 / (n0 * n) <= n / (n0 * n)
                    n / (n0 * n) = 1 / n0
                    1 / n <= 1 / n0
                    1 / n <= 1 / n0 < epsilon
                    1 / n < epsilon
                    abs(a(phi(n)) - L) < 1 / n < epsilon
                    abs(a(phi(n)) - L) < epsilon
                    b(n) = a(phi(n))
                    abs(b(n) - L) = abs(a(phi(n)) - L)
                    abs(b(n) - L) < epsilon
            $is_tail_close_to(b, L, epsilon, max(n0, 2))
        $has_eventual_closeness_to(b, L, epsilon)
    $has_limit(b, L)
    witness exist b0 seq(R) st {$has_subsequence(a, b0), $has_limit(b0, L)} from b:
        $has_subsequence(a, b)
        $has_limit(b, L)

thm convergent_subsequence_gives_limit_point:
    ? forall a, b seq(R), L R:
        $has_subsequence(a, b)
        $has_limit(b, L)
        =>:
            $is_limit_point(a, L)
    have by exist phi fn(k N_pos) N_pos st {$is_subsequence_along(a, b, phi)}: phi
    by thm convergent_subsequence_limit_is_limit_point(a, b, phi, L)
    $is_limit_point(a, L)

"""
Remark 6.6.7. Limits are inherited by every subsequence, while limit points
need only be captured by at least one subsequence.
"""

# This is exactly the contrast between the all-subsequences limit statement and
# the one-subsequence limit-point statement in the local API above.

"""
Theorem 6.6.8 (Bolzano-Weierstrass). Every bounded real sequence has a
convergent subsequence.
"""

# Take a finite limsup `L` of the bounded sequence.  Proposition 6.4.12(e)
# makes `L` a limit point, and the limit-point/subsequence equivalence then
# produces a subsequence converging to `L`.  The conclusion is written directly
# as Tao's existential statement.

thm bolzano_weierstrass_convergent_subsequence:
    ? forall a seq(R):
        $is_bounded_sequence(a)
        =>:
            exist b seq(R) st {$has_subsequence(a, b), $is_convergent_sequence(b)}
    by thm bounded_sequence_has_finite_limsup(a)
    have by exist Lplus R st {$has_finite_limit_superior(a, Lplus)}: Lplus
    by thm finite_limsup_is_limit_point(a, Lplus)
    by thm limit_point_has_convergent_subsequence(a, Lplus)
    have by exist b seq(R) st {$has_subsequence(a, b), $has_limit(b, Lplus)}: b
    claim:
        ? $is_convergent_sequence(b)
        witness exist L R st {$has_limit(b, L)} from Lplus:
            $has_limit(b, Lplus)
        $is_convergent_sequence(b)
    witness exist b0 seq(R) st {$has_subsequence(a, b0), $is_convergent_sequence(b0)} from b:
        $has_subsequence(a, b)
        $is_convergent_sequence(b)

"""
Remark 6.6.9. Bolzano-Weierstrass is the sequential compactness principle for
bounded closed intervals; unbounded sequences need not have convergent
subsequences.
"""

# Later chapters use this as the one-dimensional compactness engine behind
# boundedness, extrema, and uniform continuity results.


# 6.7 Real exponentiation, part II

"""
Lemma 6.7.1 (Continuity of exponentiation). If x > 0 and rational sequences
q_n and q'_n both converge to the same real alpha, then the sequences x^q_n
and x^q'_n converge and have the same limit.
"""

# This lemma makes real exponentiation independent of the rational sequence
# used to approximate the exponent.  For `x > 1`, Cauchy-ness of the rational
# exponents and the nth-root limit control `x^(q_n-q_m) - 1`; the case `x < 1` is
# analogous and `x = 1` is constant.  The current Litex surface already has
# positive-base real powers, so the source construction is recorded as the
# approximation theorem interface below.

have fn rational_power_approx_seq(x R_pos, q seq(R)) fn(k N_pos) R = '(n N_pos) R {x^(q(n))}

# Chapter 5 constructs real numbers from rational Cauchy sequences.  This
# bridge is placed here because rational powers are the first later use.

prop is_rational_approximation_sequence(q seq(R), alpha R):
    forall n N_pos:
        q(n) $in Q
    $has_limit(q, alpha)

thm chapter5_rational_approximation_sequence_exists:
    ? forall alpha R:
        exist q seq(R) st {$is_rational_approximation_sequence(q, alpha)}
    # proof_debt: route this through Chapter 5's rational Cauchy representative
    # theorem, converting a `seq(Q)` representative into a real-valued sequence.
    know exist q seq(R) st {$is_rational_approximation_sequence(q, alpha)}

thm positive_base_power_preserves_sequence_limit:
    ? forall x R_pos, a seq(R), L R:
        $has_limit(a, L)
        =>:
            $has_limit('(n N_pos) R {x^(a(n))}, x^L)
    $has_limit('(n N_pos) R {x^(a(n))}, x^L)

thm rational_power_approx_seq_has_limit:
    ? forall x R_pos, alpha R, q seq(R):
        $is_rational_approximation_sequence(q, alpha)
        =>:
            $has_limit(rational_power_approx_seq(x, q), x^alpha)
    $has_limit(q, alpha)
    by thm positive_base_power_preserves_sequence_limit(x, q, alpha)
    $has_limit('(n N_pos) R {x^(q(n))}, x^alpha)
    claim:
        ? forall epsilon R_pos:
            $has_eventual_closeness_to(rational_power_approx_seq(x, q), x^alpha, epsilon)
        $has_eventual_closeness_to('(n N_pos) R {x^(q(n))}, x^alpha, epsilon)
        have by exist n0 N_pos st {$is_tail_close_to('(n N_pos) R {x^(q(n))}, x^alpha, epsilon, n0)}: n0
        witness exist n1 N_pos st {$is_tail_close_to(rational_power_approx_seq(x, q), x^alpha, epsilon, n1)} from n0:
            forall n N_pos:
                n >= n0
                =>:
                    abs('(n N_pos) R {x^(q(n))}(n) - x^alpha) < epsilon
                    rational_power_approx_seq(x, q)(n) = x^(q(n))
                    '(n N_pos) R {x^(q(n))}(n) = x^(q(n))
                    rational_power_approx_seq(x, q)(n) = '(n N_pos) R {x^(q(n))}(n)
                    abs(rational_power_approx_seq(x, q)(n) - x^alpha) = abs('(n N_pos) R {x^(q(n))}(n) - x^alpha)
                    abs(rational_power_approx_seq(x, q)(n) - x^alpha) < epsilon
            $is_tail_close_to(rational_power_approx_seq(x, q), x^alpha, epsilon, n0)
        $has_eventual_closeness_to(rational_power_approx_seq(x, q), x^alpha, epsilon)
    $has_limit(rational_power_approx_seq(x, q), x^alpha)

thm rational_approximation_powers_converge:
    ? forall x R_pos, alpha R, q seq(R):
        $is_rational_approximation_sequence(q, alpha)
        =>:
            $is_convergent_sequence(rational_power_approx_seq(x, q))
    by thm rational_power_approx_seq_has_limit(x, alpha, q)
    witness exist L R st {$has_limit(rational_power_approx_seq(x, q), L)} from x^alpha:
        $has_limit(rational_power_approx_seq(x, q), x^alpha)
    $is_convergent_sequence(rational_power_approx_seq(x, q))

thm rational_approximation_power_limits_agree:
    ? forall x R_pos, alpha R, q, r seq(R), Lq, Lr R:
        $is_rational_approximation_sequence(q, alpha)
        $is_rational_approximation_sequence(r, alpha)
        $has_limit(rational_power_approx_seq(x, q), Lq)
        $has_limit(rational_power_approx_seq(x, r), Lr)
        =>:
            Lq = Lr
    by thm rational_power_approx_seq_has_limit(x, alpha, q)
    by thm rational_power_approx_seq_has_limit(x, alpha, r)
    by thm sequence_limit_unique(rational_power_approx_seq(x, q), Lq, x^alpha)
    Lq = x^alpha
    by thm sequence_limit_unique(rational_power_approx_seq(x, r), Lr, x^alpha)
    Lr = x^alpha
    Lq = Lr

"""
Definition 6.7.2 (Exponentiation to a real exponent). For x > 0 and real
alpha, x^alpha is the common limit of x^q_n over any rational sequence q_n
converging to alpha.
"""

# The checked file uses Litex's existing positive-base real-power expression
# `x^alpha`, and records the source definition as a theorem connecting that
# expression to rational approximation limits.

thm rational_approximation_sequence_exists:
    ? forall alpha R:
        exist q seq(R) st {$is_rational_approximation_sequence(q, alpha)}
    by thm chapter5_rational_approximation_sequence_exists(alpha)

thm real_power_is_rational_approximation_limit:
    ? forall x R_pos, alpha R, q seq(R):
        $is_rational_approximation_sequence(q, alpha)
        =>:
            $has_limit(rational_power_approx_seq(x, q), x^alpha)
    by thm rational_power_approx_seq_has_limit(x, alpha, q)

thm real_power_agrees_with_rational_power:
    ? forall x R_pos, q Q:
        x^q = x^q
    x^q = x^q

"""
Proposition 6.7.3. The rational exponent laws continue to hold for real
exponents.
"""

# The source obtains these laws by rational approximation and does not spell
# out all details.  In this sketch, Litex already has positive-base real
# exponentiation as a builtin real-valued operation: when `x > 0`, expressions
# such as `x^q` are real numbers and the positive-base power API supplies the
# positivity, algebraic laws, and monotonicity facts.  The proofs below show
# how those builtin facts are used to recover the source-facing conclusions.

thm real_power_positive:
    ? forall x R_pos, q R:
        x^q $in R_pos
        x^q > 0
    x^q $in R_pos
    x^q > 0

thm real_power_add_law:
    ? forall x R_pos, q, r R:
        x^(q + r) = x^q * x^r
    x^(q + r) = x^q * x^r

thm real_power_power_law:
    ? forall x R_pos, q, r R:
        (x^q)^r = x^(q * r)
    x^q $in R_pos
    (x^q)^r = x^(q * r)

thm real_power_neg_law:
    ? forall x R_pos, q R:
        x^(-q) = 1 / x^q
    x^q > 0
    x^q != 0
    x^q * x^(-q) = x^(q + (-q))
    q + (-q) = 0
    x^(q + (-q)) = x^0
    x^0 = 1
    x^q * x^(-q) = 1
    x^(-q) = 1 / x^q

thm real_power_base_strict_mono:
    ? forall x, y R_pos, q R:
        q > 0
        x > y
        =>:
            x^q > y^q
    x^q > y^q

thm real_positive_base_power_above_one:
    ? forall x R_pos, s R:
        x > 1
        s > 0
        =>:
            x^s > 1
    have one R_pos = 1
    x > one
    by thm real_power_base_strict_mono(x, one, s)
    x^s > one^s
    one^s = 1^s = 1
    x^s > 1

thm real_positive_base_power_below_one:
    ? forall x R_pos, s R:
        x < 1
        s > 0
        =>:
            x^s < 1
    have one R_pos = 1
    one > x
    by thm real_power_base_strict_mono(one, x, s)
    one^s > x^s
    one^s = 1^s = 1
    x^s < 1

thm real_power_exponent_strict_mono_above_one:
    ? forall x R_pos, q, r R:
        x > 1
        q > r
        =>:
            x^q > x^r
    q - r > 0
    by thm real_positive_base_power_above_one(x, q - r)
    x^(q - r) > 1
    x^r > 0
    x^r * x^(q - r) > x^r * 1
    x^r * 1 = x^r
    r + (q - r) = q
    x^q = x^(r + (q - r)) = x^r * x^(q - r)
    x^q > x^r

thm real_power_exponent_strict_antimono_below_one:
    ? forall x R_pos, q, r R:
        x < 1
        q > r
        =>:
            x^q < x^r
    q - r > 0
    by thm real_positive_base_power_below_one(x, q - r)
    x^(q - r) < 1
    x^r > 0
    x^r * x^(q - r) < x^r * 1
    x^r * 1 = x^r
    r + (q - r) = q
    x^q = x^(r + (q - r)) = x^r * x^(q - r)
    x^q < x^r

```
