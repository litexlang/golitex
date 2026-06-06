# Case Studies

Larger proof developments and mathematical case studies that combine several Litex features.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `Hilbert_axioms_on_Euclidean_geometry`

- Category: `case study`
- System surface: `Hilbert-style geometry axioms`
- Purpose: Shows an axiomatic geometry development using abstract props.

```litex
"""
This is a current Litex version of a Hilbert-style axiomatization sketch for
Euclidean geometry.

Compared with the older draft, this version follows the current style:
primitive geometric relations are introduced with `abstract_prop`, while
uniquely determined geometric objects such as `line_of(A, B)` and
`plane_of(A, B, C)` are introduced from `forall ... exist! ...` facts.
"""

# Primitive domains.
have point nonempty_set
have line nonempty_set
have plane nonempty_set

# Lines and planes are sets of points.
know:
    forall l line:
        l $in power_set(point)

    forall alpha plane:
        alpha $in power_set(point)

# Primitive relations.
abstract_prop line_through(A, B, l)
abstract_prop plane_through(A, B, C, alpha)
abstract_prop plane_through_point_and_line(A, l, alpha)
abstract_prop between(A, B, C)
abstract_prop line_intersects_segment(l, A, B)
abstract_prop on_ray(A, B, C)
abstract_prop same_side_of_line(P1, P2, l)
abstract_prop segment_congruent(A, B, C, D)
abstract_prop angle_congruent(A, B, C, D, E, F)
abstract_prop parallel_line(l1, l2)
abstract_prop archimedes_number(A, B, C, D, n)

# Derived predicates.
prop collinear(A, B, C point):
    exist l line st {A $in l, B $in l, C $in l}

prop noncollinear(A, B, C point):
    A != B
    A != C
    B != C
    not $collinear(A, B, C)

prop line_on_plane(l line, alpha plane):
    forall P l:
        P $in alpha

prop four_points_not_coplanar(A, B, C, D point):
    A != B
    A != C
    A != D
    B != C
    B != D
    C != D
    forall alpha plane:
        not A $in alpha or not B $in alpha or not C $in alpha or not D $in alpha

# I1: unique line through two distinct points.
know:
    forall A, B point:
        A != B
        =>:
            exist! l line st {$line_through(A, B, l)}

    forall A, B point, l line:
        $line_through(A, B, l)
        =>:
            A $in l
            B $in l

have fn line_of as set:
    prove:
        forall A, B point:
            A != B
            =>:
                exist! l line st {$line_through(A, B, l)}

know:
    forall A, B point:
        A != B
        =>:
            $line_through(A, B, line_of(A, B))
            A $in line_of(A, B)
            B $in line_of(A, B)

# I2: every line contains at least two distinct points.
know:
    forall l line:
        exist A, B point st {A != B, A $in l, B $in l}

# I3: there exist three noncollinear points.
know:
    exist A, B, C point st {$noncollinear(A, B, C)}

# I4: unique plane through three noncollinear points.
know:
    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            exist! alpha plane st {$plane_through(A, B, C, alpha)}

    forall A, B, C point, alpha plane:
        $plane_through(A, B, C, alpha)
        =>:
            A $in alpha
            B $in alpha
            C $in alpha

have fn plane_of as set:
    prove:
        forall A, B, C point:
            $noncollinear(A, B, C)
            =>:
                exist! alpha plane st {$plane_through(A, B, C, alpha)}

know:
    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            $plane_through(A, B, C, plane_of(A, B, C))
            A $in plane_of(A, B, C)
            B $in plane_of(A, B, C)
            C $in plane_of(A, B, C)

# I5: every plane contains three noncollinear points.
know:
    forall alpha plane:
        exist A, B, C point st {A $in alpha, B $in alpha, C $in alpha, $noncollinear(A, B, C)}

# I6: if two points of a line lie in a plane, the whole line lies in the plane.
know:
    forall A, B point, alpha plane:
        A != B
        A $in alpha
        B $in alpha
        =>:
            $line_on_plane(line_of(A, B), alpha)

# I7: two planes with one common point have a second common point.
know:
    forall A point, alpha, beta plane:
        A $in alpha
        A $in beta
        =>:
            exist B point st {B != A, B $in alpha, B $in beta}

# I8: there exist four points not lying in one plane.
know:
    exist A, B, C, D point st {$four_points_not_coplanar(A, B, C, D)}

# B1: betweenness symmetry and collinearity.
know:
    forall A, B, C point:
        $between(A, B, C)
        =>:
            $between(C, B, A)
            A != B
            A != C
            B != C
            $collinear(A, B, C)

# B2: given A != C, C lies between A and some B on the extension of AC.
know:
    forall A, C point:
        A != C
        =>:
            exist B point st {$between(A, C, B)}

# B3: among three distinct collinear points, at most one lies between the other two.
know:
    forall A, B, C point:
        A != B
        A != C
        B != C
        $collinear(A, B, C)
        $between(A, B, C)
        =>:
            not $between(B, A, C)
            not $between(A, C, B)

# Pasch's axiom in a segment-intersection form.
know:
    forall A, B, C point, l line:
        $noncollinear(A, B, C)
        $line_on_plane(l, plane_of(A, B, C))
        not A $in l
        not B $in l
        not C $in l
        $line_intersects_segment(l, A, B)
        =>:
            $line_intersects_segment(l, B, C) or $line_intersects_segment(l, A, C)

# C1: segment copying on a chosen ray.
know:
    forall A, B point, A2, side_point point:
        A != B
        A2 != side_point
        =>:
            exist B2 point st {$on_ray(A2, side_point, B2), $segment_congruent(A, B, A2, B2)}

# C2: segment congruence is reflexive, symmetric, and transitive.
know:
    forall A, B point:
        A != B
        =>:
            $segment_congruent(A, B, A, B)

    forall A, B, C, D point:
        $segment_congruent(A, B, C, D)
        =>:
            $segment_congruent(C, D, A, B)

    forall A, B, C, D, E, F point:
        $segment_congruent(A, B, C, D)
        $segment_congruent(C, D, E, F)
        =>:
            $segment_congruent(A, B, E, F)

# C3: addition of congruent segments.
know:
    forall A, B, C, A2, B2, C2 point:
        $between(A, B, C)
        $between(A2, B2, C2)
        $segment_congruent(A, B, A2, B2)
        $segment_congruent(B, C, B2, C2)
        =>:
            $segment_congruent(A, C, A2, C2)

# C4 and C5: angle copying and transitivity.
know:
    forall A, B, C point, D, E, side_point point, alpha plane:
        $noncollinear(A, B, C)
        D != E
        D $in alpha
        E $in alpha
        side_point $in alpha
        not side_point $in line_of(D, E)
        =>:
            exist F point st {F $in alpha, $same_side_of_line(F, side_point, line_of(D, E)), $angle_congruent(A, B, C, D, E, F)}

    forall A, B, C point:
        $noncollinear(A, B, C)
        =>:
            $angle_congruent(A, B, C, A, B, C)

    forall A, B, C, D, E, F point:
        $angle_congruent(A, B, C, D, E, F)
        =>:
            $angle_congruent(D, E, F, A, B, C)

    forall A, B, C, D, E, F, G, H, I point:
        $angle_congruent(A, B, C, D, E, F)
        $angle_congruent(D, E, F, G, H, I)
        =>:
            $angle_congruent(A, B, C, G, H, I)

# C6: SAS triangle congruence consequence.
know:
    forall A, B, C, A2, B2, C2 point:
        $noncollinear(A, B, C)
        $noncollinear(A2, B2, C2)
        $segment_congruent(A, B, A2, B2)
        $segment_congruent(A, C, A2, C2)
        $angle_congruent(B, A, C, B2, A2, C2)
        =>:
            $angle_congruent(A, B, C, A2, B2, C2)
            $angle_congruent(A, C, B, A2, C2, B2)

# A unique plane through a line and an external point.
know:
    forall A point, l line:
        not A $in l
        =>:
            exist! alpha plane st {$plane_through_point_and_line(A, l, alpha)}

    forall A point, l line, alpha plane:
        $plane_through_point_and_line(A, l, alpha)
        =>:
            A $in alpha
            $line_on_plane(l, alpha)

have fn plane_of_point_and_line as set:
    prove:
        forall A point, l line:
            not A $in l
            =>:
                exist! alpha plane st {$plane_through_point_and_line(A, l, alpha)}

# P1: Playfair's axiom.
know:
    forall l1, l2 line:
        $parallel_line(l1, l2)
        =>:
            l1 != l2

    forall l1, l2 line:
        $parallel_line(l1, l2)
        =>:
            $parallel_line(l2, l1)

    forall A point, l line:
        not A $in l
        =>:
            exist! l1 line st {A $in l1, $line_on_plane(l1, plane_of_point_and_line(A, l)), $parallel_line(l1, l)}

# Ct1: Archimedes' axiom in abstract form.
know:
    forall A, B, C, D point:
        A != B
        C != D
        =>:
            exist n N_pos st {$archimedes_number(A, B, C, D, n)}
```

## 2. `R_is_infinite_set`

- Category: `case study`
- System surface: `infinite set`
- Purpose: Shows an infinity argument for R.

```litex
by contra not $is_finite_set(R):
    forall x 0...count(R):
        x $in Z
        x $in R

    0...count(R) $subset R

    count(R) + 1 = count(R) - 0 + 1 = count(0...count(R)) <= count(R)

    impossible count(R) + 1 <= count(R)
```

## 3. `cantor_schroeder_bernstein`

- Category: `case study`
- System surface: `Cantor-Schroeder-Bernstein`
- Purpose: Shows a high-level CSB construction with abstract partition facts.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

# The CSB construction partitions S into the part reached by f-g chains.
abstract_prop csb_left_part(S, T, f, g, x)
abstract_prop csb_right_part(S, T, f, g, x)

prop csb_g_inv_value(S, T set, g fn(x T) S, x S, y T):
    g(y) = x

know forall S, T set, f fn(x S) T, g fn(x T) S, g_inv fn(x S) T, h fn(x S) T:
    $injective_fn(S, T, f)
    $injective_fn(T, S, g)
    forall x S:
        $csb_right_part(S, T, f, g, x)
        =>:
            g(g_inv(x)) = x
    forall x S:
        $csb_left_part(S, T, f, g, x)
        =>:
            h(x) = f(x)
    forall x S:
        $csb_right_part(S, T, f, g, x)
        =>:
            h(x) = g_inv(x)
    =>:
        $bijective_fn(S, T, h)

claim:
    prove:
        forall S, T set:
            exist f fn(x S) T st {$injective_fn(S, T, f)}
            exist g fn(x T) S st {$injective_fn(T, S, g)}
            =>:
                exist h fn(x S) T st {$bijective_fn(S, T, h)}

    have by exist f fn(x S) T st {$injective_fn(S, T, f)}: f
    have by exist g fn(x T) S st {$injective_fn(T, S, g)}: g

    know forall x S:
        exist! y T st {$csb_g_inv_value(S, T, g, x, y)}

    have fn g_inv as set:
        prove:
            forall x S:
                exist! y T st {$csb_g_inv_value(S, T, g, x, y)}

    have fn h(x S) T by cases:
        case $csb_left_part(S, T, f, g, x): f(x)
        case $csb_right_part(S, T, f, g, x): g_inv(x)

    $injective_fn(S, T, f)
    $injective_fn(T, S, g)
    claim:
        prove:
            forall x S:
                $csb_right_part(S, T, f, g, x)
                =>:
                    g(g_inv(x)) = x
        $csb_g_inv_value(S, T, g, x, g_inv(x))
        g(g_inv(x)) = x
    claim:
        prove:
            forall x S:
                $csb_left_part(S, T, f, g, x)
                =>:
                    h(x) = f(x)
        h(x) = f(x)
    claim:
        prove:
            forall x S:
                $csb_right_part(S, T, f, g, x)
                =>:
                    h(x) = g_inv(x)
        h(x) = g_inv(x)
    know $bijective_fn(S, T, h)
    $bijective_fn(S, T, h)
    witness exist h2 fn(x S) T st {$bijective_fn(S, T, h2)} from h
```

## 4. `detailed_there_exists_infinite_number_of_prime_numbers`

- Category: `case study`
- System surface: `infinite primes`
- Purpose: Detailed Euclid-style proof that there are arbitrarily large primes.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

claim:
    prove:
        forall a N_pos:
            product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

    by induc a from 1:
        prove:
            product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

        product(1, 1, 'N_pos(x){x}) = 1
        1 <= product(1, 1, 'N_pos(x){x})

        claim:
            prove:
                forall k Z:
                    k >= 1
                    product(1, k, 'N_pos(x){x}) % k = 0 and k <= product(1, k, 'N_pos(x){x})
                    =>:
                        product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0 and k + 1 <= product(1, k + 1, 'N_pos(x){x})

            product(1, k + 1, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * (k + 1)
            witness exist t Z st {product(1, k + 1, 'N_pos(x){x}) = t * (k + 1)} from product(1, k, 'N_pos(x){x})
            product(1, k + 1, 'N_pos(x){x}) % (k + 1) = 0
            k + 1 <= product(1, k + 1, 'N_pos(x){x})

claim:
    prove:
        forall a, k N_pos:
            k <= a
            =>:
                product(1, a, 'N_pos(x){x}) % k = 0

    by cases:
        prove:
            product(1, a, 'N_pos(x){x}) % k = 0
        case k = a:
            product(1, a, 'N_pos(x){x}) % a = 0
            product(1, a, 'N_pos(x){x}) % k = product(1, a, 'N_pos(x){x}) % a = 0
        case k < a:
            product(1, a, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * product(k + 1, a, 'N_pos(x){x})
            product(1, k, 'N_pos(x){x}) % k = 0
            have by exist r Z st {product(1, k, 'N_pos(x){x}) = r * k}: r
            witness exist t Z st {product(1, a, 'N_pos(x){x}) = t * k} from r * product(k + 1, a, 'N_pos(x){x}):
                product(1, a, 'N_pos(x){x}) = product(1, k, 'N_pos(x){x}) * product(k + 1, a, 'N_pos(x){x}) = (r * k) * product(k + 1, a, 'N_pos(x){x}) = (r * product(k + 1, a, 'N_pos(x){x})) * k
            product(1, a, 'N_pos(x){x}) % k = 0

claim:
    prove:
        forall a N_pos:
            a <= product(1, a, 'N_pos(x){x})

    product(1, a, 'N_pos(x){x}) % a = 0 and a <= product(1, a, 'N_pos(x){x})

claim:
    prove:
        forall a N_pos:
            2 <= a
            =>:
                exist k N_pos st {$prime(k), a % k = 0}

    by strong_induc x from 2:
        prove:
            exist k N_pos st {$prime(k), x % k = 0}

        claim:
            prove:
                forall b N_pos:
                    2 <= b < 2
                    =>:
                        2 % b != 0
            by contra 2 % b != 0:
                impossible b < 2
        $prime(2)

        witness exist t Z st {2 = t * 2} from 1
        2 % 2 = 0
        witness exist k N_pos st {$prime(k), 2 % k = 0} from 2

        claim:
            prove:
                forall n Z:
                    n >= 2
                    forall m Z:
                        2 <= m
                        m <= n
                        =>:
                            exist k N_pos st {$prime(k), m % k = 0}
                    =>:
                        exist k N_pos st {$prime(k), (n + 1) % k = 0}

            by cases exist k N_pos st {$prime(k), (n + 1) % k = 0}:
                case $prime(n+1):
                    witness exist t Z st {n + 1 = t * (n + 1)} from 1
                    (n + 1) % (n + 1) = 0
                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from n+1
                case not $prime(n+1):
                    by contra:
                        prove:
                            not forall b N_pos:
                                2 <= b < n + 1
                                =>:
                                    (n + 1) % b != 0
                        2 <= n + 1
                        $prime(n+1)
                        impossible $prime(n+1)

                    have by exist b N_pos st {2 <= b < n+1, not (n + 1) % b != 0}: c

                    2 <= c < n+1

                    (n+1) % c = 0
                    c <= n or c >= n + 1
                    by cases:
                        prove:
                            c <= n
                        case c <= n:
                            ...
                        case c >= n + 1:
                            impossible c < n + 1

                    have by exist k N_pos st {$prime(k), c % k = 0}: d

                    have by exist k Z st {(n+1) = k * c}: e

                    have by exist k Z st {c = k * d}: f

                    witness exist t Z st {e * f * d = t * d} from e * f
                    (e * f * d) % d = 0

                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from d:
                        n + 1 = e * c = e * (f * d) = (e * f) * d
                        (n + 1) % d = ((e * f) * d) % d = 0

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

## 5. `euclid_algorithm`

- Category: `case study`
- System surface: `Euclidean algorithm`
- Purpose: Large checked development of division, gcd, and extended gcd.

```litex
claim:
    prove:
        forall x, y R:
            0 <= x
            0 <= y
            x^2 < y^2
            =>:
                x < y

    by contra:
        prove:
            x < y
        y <= x
        y^2 <= x^2
        impossible x^2 < y^2

claim:
    prove:
        forall n, d Z:
            n * d < 0
            =>:
                abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

    0 < -(n * d)
    0 < 8
    0 < 8 * (-(n * d))
    8 * (-(n * d)) = -8 * n * d
    0 < -8 * n * d
    (2 * (n + d) - d)^2 < (2 * (n + d) - d)^2 + (-8 * n * d) = (2 * n - d)^2
    abs(2 * (n + d) - d)^2 = (2 * (n + d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d < 0
            =>:
                abs(2 * (n + d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n + d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d >= 0
            0 < d * (n - d)
            =>:
                abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

    0 < 8
    0 < 8 * (d * (n - d))
    8 * (d * (n - d)) = 8 * d * (n - d)
    0 < 8 * d * (n - d)
    (2 * (n - d) - d)^2 < (2 * (n - d) - d)^2 + 8 * d * (n - d) = (2 * n - d)^2
    abs(2 * (n - d) - d)^2 = (2 * (n - d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    prove:
        forall n, d Z:
            n * d >= 0
            0 < d * (n - d)
            =>:
                abs(2 * (n - d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n - d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

have fn fmod(n Z, d Z) Z by induc abs(2 * n - d) from 0:
    case n * d < 0: fmod(n + d, d)
    case n * d >= 0:
        case 0 < d * (n - d): fmod(n - d, d)
        case 0 >= d * (n - d):
            case n = d: 0
            case n != d: n

have fn fdiv(n Z, d Z) Z by induc abs(2 * n - d) from 0:
    case n * d < 0: fdiv(n + d, d) - 1
    case n * d >= 0:
        case 0 < d * (n - d): fdiv(n - d, d) + 1
        case 0 >= d * (n - d):
            case n = d: 1
            case n != d: 0

prop fmod_add_fdiv_at_measure(m Z):
    forall u, v Z:
        abs(2 * u - v) = m
        =>:
            fmod(u, v) + v * fdiv(u, v) = u

claim:
    prove:
        forall n, d Z:
            abs(2 * n - d) = 0
            =>:
                fmod(n, d) + d * fdiv(n, d) = n

    by cases:
        prove:
            fmod(n, d) + d * fdiv(n, d) = n
        case n * d < 0:
            abs(2 * (n + d) - d) < abs(2 * n - d) = 0
            0 <= abs(2 * (n + d) - d)
            impossible abs(2 * (n + d) - d) < 0
        case n * d >= 0:
            by cases:
                prove:
                    fmod(n, d) + d * fdiv(n, d) = n
                case 0 < d * (n - d):
                    abs(2 * (n - d) - d) < abs(2 * n - d) = 0
                    0 <= abs(2 * (n - d) - d)
                    impossible abs(2 * (n - d) - d) < 0
                case 0 >= d * (n - d):
                    by cases:
                        prove:
                            fmod(n, d) + d * fdiv(n, d) = n
                        case n = d:
                            fmod(n, d) = 0
                            fdiv(n, d) = 1
                            fmod(n, d) + d * fdiv(n, d) = 0 + d * 1 = d = n
                        case n != d:
                            fmod(n, d) = n
                            fdiv(n, d) = 0
                            fmod(n, d) + d * fdiv(n, d) = n + d * 0 = n

$fmod_add_fdiv_at_measure(0)

claim:
    prove:
        forall m Z:
            m >= 0
            forall y Z:
                y >= 0
                y <= m
                =>:
                    $fmod_add_fdiv_at_measure(y)
            =>:
                $fmod_add_fdiv_at_measure(m + 1)

    claim:
        prove:
            forall n, d Z:
                abs(2 * n - d) = m + 1
                =>:
                    fmod(n, d) + d * fdiv(n, d) = n

        by cases:
            prove:
                fmod(n, d) + d * fdiv(n, d) = n
            case n * d < 0:
                abs(2 * (n + d) - d) >= 0
                abs(2 * (n + d) - d) < abs(2 * n - d) = m + 1
                abs(2 * (n + d) - d) <= m or abs(2 * (n + d) - d) >= m + 1
                by cases:
                    prove:
                        abs(2 * (n + d) - d) <= m
                    case abs(2 * (n + d) - d) <= m:
                        do_nothing
                    case abs(2 * (n + d) - d) >= m + 1:
                        impossible abs(2 * (n + d) - d) < m + 1
                $fmod_add_fdiv_at_measure(abs(2 * (n + d) - d))
                n + d $in Z
                abs(2 * (n + d) - d) = abs(2 * (n + d) - d)
                fmod(n + d, d) + d * fdiv(n + d, d) = n + d
                fmod(n, d) = fmod(n + d, d)
                fdiv(n, d) = fdiv(n + d, d) - 1
                fmod(n, d) + d * fdiv(n, d) = fmod(n + d, d) + d * (fdiv(n + d, d) - 1) = fmod(n + d, d) + d * fdiv(n + d, d) - d = n + d - d = n
            case n * d >= 0:
                by cases:
                    prove:
                        fmod(n, d) + d * fdiv(n, d) = n
                    case 0 < d * (n - d):
                        abs(2 * (n - d) - d) >= 0
                        abs(2 * (n - d) - d) < abs(2 * n - d) = m + 1
                        abs(2 * (n - d) - d) <= m or abs(2 * (n - d) - d) >= m + 1
                        by cases:
                            prove:
                                abs(2 * (n - d) - d) <= m
                            case abs(2 * (n - d) - d) <= m:
                                do_nothing
                            case abs(2 * (n - d) - d) >= m + 1:
                                impossible abs(2 * (n - d) - d) < m + 1
                        $fmod_add_fdiv_at_measure(abs(2 * (n - d) - d))
                        n - d $in Z
                        abs(2 * (n - d) - d) = abs(2 * (n - d) - d)
                        fmod(n - d, d) + d * fdiv(n - d, d) = n - d
                        fmod(n, d) = fmod(n - d, d)
                        fdiv(n, d) = fdiv(n - d, d) + 1
                        fmod(n, d) + d * fdiv(n, d) = fmod(n - d, d) + d * (fdiv(n - d, d) + 1) = fmod(n - d, d) + d * fdiv(n - d, d) + d = n - d + d = n
                    case 0 >= d * (n - d):
                        by cases:
                            prove:
                                fmod(n, d) + d * fdiv(n, d) = n
                            case n = d:
                                fmod(n, d) = 0
                                fdiv(n, d) = 1
                                fmod(n, d) + d * fdiv(n, d) = 0 + d * 1 = d = n
                            case n != d:
                                fmod(n, d) = n
                                fdiv(n, d) = 0
                                fmod(n, d) + d * fdiv(n, d) = n + d * 0 = n

    $fmod_add_fdiv_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $fmod_add_fdiv_at_measure(m)

    prove from m = 0:
        $fmod_add_fdiv_at_measure(0)

    prove strong_induc:
        $fmod_add_fdiv_at_measure(m + 1)

claim:
    prove:
        forall n, d Z:
            fmod(n, d) + d * fdiv(n, d) = n

    forall n1, d1 Z:
        abs(2 * n1 - d1) >= 0
        $fmod_add_fdiv_at_measure(abs(2 * n1 - d1))
        fmod(n1, d1) + d1 * fdiv(n1, d1) = n1

claim:
    prove:
        forall x, y Z:
            0 < y
            x * y >= 0
            =>:
                0 <= x

    by contra:
        prove:
            0 <= x
        x < 0
        x * y < 0
        impossible x * y >= 0

claim:
    prove:
        forall x, y Z:
            0 < y
            0 >= y * (x - y)
            =>:
                x <= y

    by contra:
        prove:
            x <= y
        y < x
        0 < x - y
        0 < y * (x - y)
        impossible 0 >= y * (x - y)

claim:
    prove:
        forall x, y Z:
            x <= y
            x != y
            =>:
                x < y

    by contra:
        prove:
            x < y
        x >= y
        x = y
        impossible x != y

prop fmod_bound_at_measure(m Z):
    forall u, v Z:
        abs(2 * u - v) = m
        0 < v
        =>:
            abs(fmod(u, v)) < abs(v)

claim:
    prove:
        forall a, b Z:
            abs(2 * a - b) = 0
            0 < b
            =>:
                abs(fmod(a, b)) < abs(b)

    by cases:
        prove:
            abs(fmod(a, b)) < abs(b)
        case a * b < 0:
            abs(2 * (a + b) - b) < abs(2 * a - b) = 0
            0 <= abs(2 * (a + b) - b)
            impossible abs(2 * (a + b) - b) < 0
        case a * b >= 0:
            by cases:
                prove:
                    abs(fmod(a, b)) < abs(b)
                case 0 < b * (a - b):
                    abs(2 * (a - b) - b) < abs(2 * a - b) = 0
                    0 <= abs(2 * (a - b) - b)
                    impossible abs(2 * (a - b) - b) < 0
                case 0 >= b * (a - b):
                    by cases:
                        prove:
                            abs(fmod(a, b)) < abs(b)
                        case a = b:
                            fmod(a, b) = 0
                            abs(fmod(a, b)) = abs(0) = 0
                            abs(b) = b
                            0 < abs(b)
                            abs(fmod(a, b)) < abs(b)
                        case a != b:
                            fmod(a, b) = a
                            by contra:
                                prove:
                                    0 <= a
                                a < 0
                                a * b < 0
                                impossible a * b >= 0
                            by contra:
                                prove:
                                    a <= b
                                b < a
                                0 < a - b
                                0 < b * (a - b)
                                impossible 0 >= b * (a - b)
                            by contra:
                                prove:
                                    a < b
                                a >= b
                                a = b
                                impossible a != b
                            abs(a) = a
                            abs(b) = b
                            0 <= fmod(a, b)
                            abs(fmod(a, b)) = fmod(a, b) = a < b = abs(b)

$fmod_bound_at_measure(0)

claim:
    prove:
        forall m Z:
            m >= 0
            forall y Z:
                y >= 0
                y <= m
                =>:
                    $fmod_bound_at_measure(y)
            =>:
                $fmod_bound_at_measure(m + 1)

    claim:
        prove:
            forall a, b Z:
                abs(2 * a - b) = m + 1
                0 < b
                =>:
                    abs(fmod(a, b)) < abs(b)

        by cases:
            prove:
                abs(fmod(a, b)) < abs(b)
            case a * b < 0:
                abs(2 * (a + b) - b) >= 0
                abs(2 * (a + b) - b) < abs(2 * a - b) = m + 1
                abs(2 * (a + b) - b) <= m or abs(2 * (a + b) - b) >= m + 1
                by cases:
                    prove:
                        abs(2 * (a + b) - b) <= m
                    case abs(2 * (a + b) - b) <= m:
                        do_nothing
                    case abs(2 * (a + b) - b) >= m + 1:
                        impossible abs(2 * (a + b) - b) < m + 1
                $fmod_bound_at_measure(abs(2 * (a + b) - b))
                a + b $in Z
                abs(2 * (a + b) - b) = abs(2 * (a + b) - b)
                abs(fmod(a + b, b)) < abs(b)
                fmod(a, b) = fmod(a + b, b)
                fmod(a, b) - fmod(a + b, b) = 0
                abs(fmod(a, b)) - abs(fmod(a + b, b)) <= abs(fmod(a, b) - fmod(a + b, b)) = abs(0) = 0
                abs(fmod(a, b)) <= abs(fmod(a + b, b))
                abs(fmod(a, b)) <= abs(fmod(a + b, b)) < abs(b)
                abs(fmod(a, b)) < abs(b)
            case a * b >= 0:
                by cases:
                    prove:
                        abs(fmod(a, b)) < abs(b)
                    case 0 < b * (a - b):
                        abs(2 * (a - b) - b) >= 0
                        abs(2 * (a - b) - b) < abs(2 * a - b) = m + 1
                        abs(2 * (a - b) - b) <= m or abs(2 * (a - b) - b) >= m + 1
                        by cases:
                            prove:
                                abs(2 * (a - b) - b) <= m
                            case abs(2 * (a - b) - b) <= m:
                                do_nothing
                            case abs(2 * (a - b) - b) >= m + 1:
                                impossible abs(2 * (a - b) - b) < m + 1
                        $fmod_bound_at_measure(abs(2 * (a - b) - b))
                        a - b $in Z
                        abs(2 * (a - b) - b) = abs(2 * (a - b) - b)
                        abs(fmod(a - b, b)) < abs(b)
                        fmod(a, b) = fmod(a - b, b)
                        fmod(a, b) - fmod(a - b, b) = 0
                        abs(fmod(a, b)) - abs(fmod(a - b, b)) <= abs(fmod(a, b) - fmod(a - b, b)) = abs(0) = 0
                        abs(fmod(a, b)) <= abs(fmod(a - b, b))
                        abs(fmod(a, b)) <= abs(fmod(a - b, b)) < abs(b)
                        abs(fmod(a, b)) < abs(b)
                    case 0 >= b * (a - b):
                        by cases:
                            prove:
                                abs(fmod(a, b)) < abs(b)
                            case a = b:
                                fmod(a, b) = 0
                                abs(fmod(a, b)) = abs(0) = 0
                                abs(b) = b
                                0 < abs(b)
                                abs(fmod(a, b)) < abs(b)
                            case a != b:
                                fmod(a, b) = a
                                by contra:
                                    prove:
                                        0 <= a
                                    a < 0
                                    a * b < 0
                                    impossible a * b >= 0
                                by contra:
                                    prove:
                                        a <= b
                                    b < a
                                    0 < a - b
                                    0 < b * (a - b)
                                    impossible 0 >= b * (a - b)
                                by contra:
                                    prove:
                                        a < b
                                    a >= b
                                    a = b
                                    impossible a != b
                                abs(a) = a
                                abs(b) = b
                                0 <= fmod(a, b)
                                abs(fmod(a, b)) = fmod(a, b) = a < b = abs(b)

    $fmod_bound_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $fmod_bound_at_measure(m)

    prove from m = 0:
        $fmod_bound_at_measure(0)

    prove strong_induc:
        $fmod_bound_at_measure(m + 1)

claim:
    prove:
        forall a, b Z:
            0 < b
            =>:
                abs(fmod(a, b)) < abs(b)

    forall a1, b1 Z:
        0 < b1
        =>:
            abs(2 * a1 - b1) >= 0
            $fmod_bound_at_measure(abs(2 * a1 - b1))
            abs(fmod(a1, b1)) < abs(b1)

claim:
    prove:
        forall a, b Z:
            b < 0
            =>:
                abs(fmod(a, -b)) < abs(b)

    0 < -b
    -b $in Z
    abs(fmod(a, -b)) < abs(-b)
    b <= 0
    abs(b) = -b
    abs(-b) = -b
    abs(-b) = abs(b)
    abs(fmod(a, -b)) < abs(b)

have fn gcd(a Z, b Z) Z by induc abs(b) from 0:
    case 0 < b: gcd(b, fmod(a, b))
    case 0 >= b:
        case b < 0: gcd(b, fmod(a, -b))
        case b >= 0:
            case 0 <= a: a
            case 0 > a: -a

have fn egcd_pair(a Z, b Z) cart(Z, Z) by induc abs(b) from 0:
    case 0 < b: (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])
    case 0 >= b:
        case b < 0: (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])
        case b >= 0:
            case 0 <= a: (1, 0)
            case 0 > a: (-1, 0)

have fn egcd_l(a Z, b Z) Z = egcd_pair(a, b)[1]

have fn egcd_r(a Z, b Z) Z = egcd_pair(a, b)[2]

prop egcd_identity_at_measure(m Z):
    forall u, v Z:
        abs(v) = m
        =>:
            egcd_l(u, v) * u + egcd_r(u, v) * v = gcd(u, v)

claim:
    prove:
        forall a, b Z:
            abs(b) = 0
            =>:
                egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

    b = 0
    0 >= b
    b >= 0
    by cases:
        prove:
            egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
        case 0 <= a:
            egcd_pair(a, b) = (1, 0)
            egcd_l(a, b) = egcd_pair(a, b)[1] = (1, 0)[1] = 1
            egcd_r(a, b) = egcd_pair(a, b)[2] = (1, 0)[2] = 0
            gcd(a, b) = a
            egcd_l(a, b) * a + egcd_r(a, b) * b = 1 * a + 0 * b = a = gcd(a, b)
        case 0 > a:
            egcd_pair(a, b) = (-1, 0)
            egcd_l(a, b) = egcd_pair(a, b)[1] = (-1, 0)[1] = -1
            egcd_r(a, b) = egcd_pair(a, b)[2] = (-1, 0)[2] = 0
            gcd(a, b) = -a
            egcd_l(a, b) * a + egcd_r(a, b) * b = -1 * a + 0 * b = -a = gcd(a, b)

$egcd_identity_at_measure(0)

claim:
    prove:
        forall m Z:
            m >= 0
            forall y Z:
                y >= 0
                y <= m
                =>:
                    $egcd_identity_at_measure(y)
            =>:
                $egcd_identity_at_measure(m + 1)

    claim:
        prove:
            forall a, b Z:
                abs(b) = m + 1
                =>:
                    egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

        by cases:
            prove:
                egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
            case 0 < b:
                abs(fmod(a, b)) >= 0
                abs(fmod(a, b)) < abs(b) = m + 1
                abs(fmod(a, b)) <= m or abs(fmod(a, b)) >= m + 1
                by cases:
                    prove:
                        abs(fmod(a, b)) <= m
                    case abs(fmod(a, b)) <= m:
                        do_nothing
                    case abs(fmod(a, b)) >= m + 1:
                        impossible abs(fmod(a, b)) < m + 1
                $egcd_identity_at_measure(abs(fmod(a, b)))
                fmod(a, b) $in Z
                abs(fmod(a, b)) = abs(fmod(a, b))
                egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * fmod(a, b) = gcd(b, fmod(a, b))
                egcd_pair(a, b) = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])
                egcd_l(a, b) = egcd_pair(a, b)[1] = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])[1] = egcd_pair(b, fmod(a, b))[2]
                egcd_r(b, fmod(a, b)) = egcd_pair(b, fmod(a, b))[2]
                egcd_l(a, b) = egcd_r(b, fmod(a, b))
                egcd_r(a, b) = egcd_pair(a, b)[2] = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])[2] = egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2]
                egcd_l(b, fmod(a, b)) = egcd_pair(b, fmod(a, b))[1]
                egcd_pair(b, fmod(a, b))[1] = egcd_l(b, fmod(a, b))
                egcd_pair(b, fmod(a, b))[2] = egcd_r(b, fmod(a, b))
                egcd_r(a, b) = egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2] = egcd_l(b, fmod(a, b)) - fdiv(a, b) * egcd_r(b, fmod(a, b))
                fmod(a, b) + b * fdiv(a, b) = a
                a = fmod(a, b) + b * fdiv(a, b)
                a - b * fdiv(a, b) = fmod(a, b) + b * fdiv(a, b) - b * fdiv(a, b) = fmod(a, b)
                gcd(a, b) = gcd(b, fmod(a, b))
                egcd_l(a, b) * a + egcd_r(a, b) * b = egcd_r(b, fmod(a, b)) * a + (egcd_l(b, fmod(a, b)) - fdiv(a, b) * egcd_r(b, fmod(a, b))) * b = egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * (a - b * fdiv(a, b)) = egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * fmod(a, b) = gcd(b, fmod(a, b)) = gcd(a, b)
            case 0 >= b:
                by cases:
                    prove:
                        egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
                    case b < 0:
                        abs(fmod(a, -b)) >= 0
                        abs(fmod(a, -b)) < abs(b) = m + 1
                        abs(fmod(a, -b)) <= m or abs(fmod(a, -b)) >= m + 1
                        by cases:
                            prove:
                                abs(fmod(a, -b)) <= m
                            case abs(fmod(a, -b)) <= m:
                                do_nothing
                            case abs(fmod(a, -b)) >= m + 1:
                                impossible abs(fmod(a, -b)) < m + 1
                        $egcd_identity_at_measure(abs(fmod(a, -b)))
                        fmod(a, -b) $in Z
                        abs(fmod(a, -b)) = abs(fmod(a, -b))
                        egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * fmod(a, -b) = gcd(b, fmod(a, -b))
                        egcd_pair(a, b) = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])
                        egcd_l(a, b) = egcd_pair(a, b)[1] = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])[1] = egcd_pair(b, fmod(a, -b))[2]
                        egcd_r(b, fmod(a, -b)) = egcd_pair(b, fmod(a, -b))[2]
                        egcd_l(a, b) = egcd_r(b, fmod(a, -b))
                        egcd_r(a, b) = egcd_pair(a, b)[2] = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])[2] = egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2]
                        egcd_l(b, fmod(a, -b)) = egcd_pair(b, fmod(a, -b))[1]
                        egcd_pair(b, fmod(a, -b))[1] = egcd_l(b, fmod(a, -b))
                        egcd_pair(b, fmod(a, -b))[2] = egcd_r(b, fmod(a, -b))
                        egcd_r(a, b) = egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2] = egcd_l(b, fmod(a, -b)) + fdiv(a, -b) * egcd_r(b, fmod(a, -b))
                        fmod(a, -b) + (-b) * fdiv(a, -b) = a
                        a = fmod(a, -b) + (-b) * fdiv(a, -b)
                        a + b * fdiv(a, -b) = fmod(a, -b) + (-b) * fdiv(a, -b) + b * fdiv(a, -b) = fmod(a, -b)
                        gcd(a, b) = gcd(b, fmod(a, -b))
                        egcd_l(a, b) * a + egcd_r(a, b) * b = egcd_r(b, fmod(a, -b)) * a + (egcd_l(b, fmod(a, -b)) + fdiv(a, -b) * egcd_r(b, fmod(a, -b))) * b = egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * (a + b * fdiv(a, -b)) = egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * fmod(a, -b) = gcd(b, fmod(a, -b)) = gcd(a, b)
                    case b >= 0:
                        b = 0
                        by cases:
                            prove:
                                egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
                            case 0 <= a:
                                egcd_pair(a, b) = (1, 0)
                                egcd_l(a, b) = egcd_pair(a, b)[1] = (1, 0)[1] = 1
                                egcd_r(a, b) = egcd_pair(a, b)[2] = (1, 0)[2] = 0
                                gcd(a, b) = a
                                egcd_l(a, b) * a + egcd_r(a, b) * b = 1 * a + 0 * b = a = gcd(a, b)
                            case 0 > a:
                                egcd_pair(a, b) = (-1, 0)
                                egcd_l(a, b) = egcd_pair(a, b)[1] = (-1, 0)[1] = -1
                                egcd_r(a, b) = egcd_pair(a, b)[2] = (-1, 0)[2] = 0
                                gcd(a, b) = -a
                                egcd_l(a, b) * a + egcd_r(a, b) * b = -1 * a + 0 * b = -a = gcd(a, b)

    $egcd_identity_at_measure(m + 1)

by strong_induc m from 0:
    prove:
        $egcd_identity_at_measure(m)

    prove from m = 0:
        $egcd_identity_at_measure(0)

    prove strong_induc:
        $egcd_identity_at_measure(m + 1)

claim:
    prove:
        forall a, b Z:
            egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

    forall a1, b1 Z:
        abs(b1) >= 0
        $egcd_identity_at_measure(abs(b1))
        egcd_l(a1, b1) * a1 + egcd_r(a1, b1) * b1 = gcd(a1, b1)
```

## 6. `exist_N^2_to_N_bijection`

- Category: `case study`
- System surface: `countability pairing`
- Purpose: Shows a bijection between N^2 and N.

```litex
prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

prop exist_bijection(S, T set):
    exist f fn(x S) T st {$bijective_fn(S, T, f)}

claim:
    prove:
        forall n N:
            exist! y N st {2 * y = n * (n + 1)}

    by cases:
        prove:
            n * (n + 1) % 2 = 0
        case n % 2 = 0:
            n * (n + 1) % 2 = (n % 2) * ((n + 1) % 2) % 2 = 0 * ((n + 1) % 2) % 2 = 0 % 2 = 0
        case n % 2 = 1:
            (n + 1) % 2 = (n % 2 + 1 % 2) % 2 = 0
            n * (n + 1) % 2 = (n % 2) * ((n + 1) % 2) % 2 = 1 * 0 % 2 = 0 % 2 = 0
    have by exist r N st {n * (n + 1) = 2 * r}: r
    witness exist y N st {2 * y = n * (n + 1)} from r:
        n * (n + 1) = 2 * r
        2 * r = n * (n + 1)
    forall y1, y2 N:
        2 * y1 = n * (n + 1)
        2 * y2 = n * (n + 1)
        =>:
            y1 = n * (n + 1) / 2 = y2
    exist! y N st {2 * y = n * (n + 1)}

have fn tri as set:
    prove:
        forall n N:
            exist! y N st {2 * y = n * (n + 1)}

claim:
    prove:
        tri(0) = 0
    2 * tri(0) = 0 * (0 + 1)
    tri(0) = (2 * tri(0)) / 2 = (0 * (0 + 1)) / 2 = 0

claim:
    prove:
        forall n N:
            tri(n + 1) = tri(n) + n + 1
    2 * tri(n + 1) = (n + 1) * ((n + 1) + 1) = (n + 1) * (n + 2)
    2 * tri(n) = n * (n + 1)
    2 * (tri(n) + n + 1) = 2 * tri(n) + 2 * n + 2 = n * (n + 1) + 2 * n + 2 = (n + 1) * (n + 2)
    tri(n + 1) = (2 * tri(n + 1)) / 2 = ((n + 1) * (n + 2)) / 2 = (2 * (tri(n) + n + 1)) / 2 = tri(n) + n + 1

prop triangular_interval(n, s N):
    tri(s) <= n
    n < tri(s + 1)

have fn diagonal_index(u cart(N, N)) N = tri(u[1]) + u[2]

claim:
    prove:
        forall u cart(N, N):
            u[2] <= u[1]
            =>:
                tri(u[1]) <= diagonal_index(u)
                diagonal_index(u) < tri(u[1] + 1)
    tri(u[1]) <= tri(u[1]) + u[2] = diagonal_index(u)
    diagonal_index(u) = tri(u[1]) + u[2] <= tri(u[1]) + u[1] < tri(u[1]) + u[1] + 1 = tri(u[1] + 1)

claim:
    prove:
        forall a, b N:
            a < b
            =>:
                tri(a + 1) <= tri(b)
    a + 1 <= b
    2 * tri(a + 1) = (a + 1) * ((a + 1) + 1) <= b * (b + 1) = 2 * tri(b)
    tri(a + 1) = (2 * tri(a + 1)) / 2 <= (2 * tri(b)) / 2 = tri(b)

claim:
    prove:
        forall u, v cart(N, N):
            u[2] <= u[1]
            v[2] <= v[1]
            u[1] < v[1]
            =>:
                diagonal_index(u) < diagonal_index(v)
    diagonal_index(u) < tri(u[1] + 1) <= tri(v[1]) <= diagonal_index(v)

# If two valid diagonal positions have the same number, they are on the same diagonal.
claim:
    prove:
        forall u, v cart(N, N):
            u[2] <= u[1]
            v[2] <= v[1]
            diagonal_index(u) = diagonal_index(v)
            =>:
                u[1] = v[1]
    by contra:
        prove:
            not u[1] < v[1]
        diagonal_index(u) < diagonal_index(v)
        impossible diagonal_index(u) = diagonal_index(v)
    by contra:
        prove:
            not v[1] < u[1]
        diagonal_index(v) < diagonal_index(u)
        impossible diagonal_index(u) = diagonal_index(v)
    u[1] = v[1]

have fn cantor_pair(t cart(N, N)) N = tri(t[1] + t[2]) + t[2]

# On one diagonal, the offset determines the position.
claim:
    prove:
        forall u, v cart(N, N):
            u[1] = v[1]
            diagonal_index(u) = diagonal_index(v)
            =>:
                u[2] = v[2]
    tri(u[1]) + u[2] = diagonal_index(u) = diagonal_index(v) = tri(v[1]) + v[2]
    u[2] = (tri(u[1]) + u[2]) - tri(u[1]) = (tri(v[1]) + v[2]) - tri(v[1]) = v[2]

claim:
    prove:
        forall t1, t2 cart(N, N):
            cantor_pair(t1) = cantor_pair(t2)
            =>:
                t1 = t2
    have u cart(N, N) = (t1[1] + t1[2], t1[2])
    have v cart(N, N) = (t2[1] + t2[2], t2[2])
    u[2] = t1[2] <= t1[1] + t1[2] = u[1]
    v[2] = t2[2] <= t2[1] + t2[2] = v[1]
    diagonal_index(u) = tri(t1[1] + t1[2]) + t1[2] = cantor_pair(t1)
    diagonal_index(v) = tri(t2[1] + t2[2]) + t2[2] = cantor_pair(t2)
    u[1] = v[1]
    u[2] = v[2]
    t1[2] = u[2] = v[2] = t2[2]
    t1[1] = (t1[1] + t1[2]) - t1[2] = u[1] - u[2] = v[1] - v[2] = (t2[1] + t2[2]) - t2[2] = t2[1]
    t1 = (t1[1], t1[2]) = (t2[1], t2[2]) = t2

claim:
    prove:
        forall a, b N:
            b <= a
            =>:
                a - b $in N
    a - b >= 0
    a - b $in Z
    a - b $in N

claim:
    prove:
        forall n, s N:
            $triangular_interval(n, s)
            =>:
                n - tri(s) <= s
    n < tri(s + 1) = tri(s) + s + 1
    n <= (tri(s) + s + 1) - 1 = tri(s) + s
    n - tri(s) <= (tri(s) + s) - tri(s) = s

by induc n from 0:
    prove:
        exist s N st {$triangular_interval(n, s)}

    prove from n = 0:
        tri(0) <= 0
        tri(0 + 1) = tri(0) + 0 + 1 = 1
        0 < 1 = tri(0 + 1)
        witness exist s N st {$triangular_interval(0, s)} from 0:
            $triangular_interval(0, 0)

    prove induc:
        have by exist s N st {$triangular_interval(n, s)}: s
        by cases:
            prove:
                exist t N st {$triangular_interval(n + 1, t)}
            case n + 1 < tri(s + 1):
                tri(s) <= n <= n + 1
                witness exist t N st {$triangular_interval(n + 1, t)} from s:
                    $triangular_interval(n + 1, s)
            case n + 1 >= tri(s + 1):
                tri((s + 1) + 1) = tri(s + 1) + (s + 1) + 1 = tri(s + 1) + s + 2
                n + 1 < n + 2 <= tri(s + 1) + s + 2 = tri((s + 1) + 1)
                witness exist t N st {$triangular_interval(n + 1, t)} from s + 1:
                    $triangular_interval(n + 1, s + 1)

claim:
    prove:
        forall n N:
            exist t cart(N, N) st {n = cantor_pair(t)}
    have by exist s N st {$triangular_interval(n, s)}: s
    have b N = n - tri(s)
    n - tri(s) <= s
    have a N = s - b
    a + b = (s - b) + b = s
    have p cart(N, N) = (a, b)
    cantor_pair(p) = tri(p[1] + p[2]) + p[2] = tri(a + b) + b = tri(s) + b = tri(s) + (n - tri(s)) = n
    witness exist t cart(N, N) st {n = cantor_pair(t)} from p:
        n = cantor_pair(p)

claim:
    prove:
        $exist_bijection(cart(N, N), N)
    witness exist f fn(x cart(N, N)) N st {$bijective_fn(cart(N, N), N, f)} from cantor_pair
```

## 7. `integer_is_odd_or_even`

- Category: `case study`
- System surface: `integer parity`
- Purpose: Shows an integer parity proof.

```litex
claim:
    prove:
        forall n Z:
            n % 2 = 0 or n % 2 = 1
    by induc n from 0:
        prove:
            n % 2 = 0 or n % 2 = 1
        0 % 2 = 0
        0 % 2 = 0 or 0 % 2 = 1

        claim:
            prove:
                forall x Z:
                    x >= 0
                    x % 2 = 0 or x % 2 = 1
                    =>:
                        (x + 1) % 2 = 0 or (x + 1) % 2 = 1

            by cases:
                prove:
                    (x + 1) % 2 = 0 or (x + 1) % 2 = 1
                case x % 2 = 0:
                    (x + 1) % 2 = (x % 2 + 1 % 2) % 2 = (0 + 1) % 2 = 1
                case x % 2 = 1:
                    (x + 1) % 2 = (x % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0
    by cases:
        prove:
            n % 2 = 0 or n % 2 = 1
        case n >= 0:
            do_nothing
        case n < 0:
            -n >= 0
            (-n) % 2 = 0 or (-n) % 2 = 1
            by cases:
                prove:
                    (n) % 2 = 0 or (n) % 2 = 1
                case -n % 2 = 0:
                    (n) % 2 = (-(-n)) % 2 = (2 - ((-n) % 2)) % 2 = (2 - 0) % 2 = 0
                case -n % 2 = 1:
                    (n) % 2 = (-(-n)) % 2 = (2 - (-n) % 2) % 2 = (2 - 1) % 2 = 1
```

## 8. `mod_2_equal_to_one_or_zero`

- Category: `case study`
- System surface: `modulo parity`
- Purpose: Shows residue cases modulo 2.

```litex
claim:
    prove:
        forall x Z:
            0 <= x
            =>:
                x % 2 = 0 or x % 2 = 1

    by induc x from 0:
        prove:
            x % 2 = 0 or x % 2 = 1

        0 % 2 = 0

        claim:
            prove:
                forall y Z:
                    0 <= y
                    y % 2 = 0 or y % 2 = 1
                    =>:
                        (y + 1) % 2 = 0 or (y + 1) % 2 = 1

            by cases:
                prove:
                    (y + 1) % 2 = 0 or (y + 1) % 2 = 1
                case y % 2 = 0:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (0 + 1) % 2 = 1
                case y % 2 = 1:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0
```

## 9. `sum_induc`

- Category: `case study`
- System surface: `summation induction`
- Purpose: Shows induction for a finite summation identity.

```litex
claim:
    prove:
        forall n N_pos:
            sum(0, n, 'R(x){x}) = n * (n + 1) / 2

    by induc n from 1:
        prove:
            sum(0, n, 'R(x){x}) = n * (n + 1) / 2

        prove from n = 1:
            sum(0, 0, 'R(x){x}) = 0
            sum(0, 1, 'R(x){x}) = sum(0, 0, 'R(x){x}) + 'R(x){x}(1)
            'R(x){x}(1) = 1
            sum(0, 1, 'R(x){x}) = sum(0, 0, 'R(x){x}) + 1 = 0 + 1 = 1 = 1 * (1 + 1) / 2

        prove induc:
            sum(0, n + 1, 'R(x){x}) = sum(0, n, 'R(x){x}) + 'R(x){x}(n + 1)
            'R(x){x}(n + 1) = n + 1
            sum(0, n + 1, 'R(x){x}) = sum(0, n, 'R(x){x}) + (n + 1) = n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2 = (n + 1) * ((n + 1) + 1) / 2
```
