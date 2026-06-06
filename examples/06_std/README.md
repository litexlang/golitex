# Standard Library

Smoke examples for public standard-library interfaces.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `c`

- Category: `std interface`
- System surface: `C`
- Purpose: Smoke test for complex-number std interfaces.

```litex
import C

(1, 2) $in &C::C
have z &C::C = (3, 4)

&C::C{z}.re = 3
&C::C{z}.im = 4

C::add((1, 2), (3, 4)) = (1 + 3, 2 + 4) = (4, 6)
C::neg((1, 2)) = (-1 * 1, -1 * 2)
C::sub((5, 7), (2, 3)) = (5 - 2, 7 - 3) = (3, 4)
C::mul((1, 2), (3, 4)) = (1 * 3 - 2 * 4, 1 * 4 + 2 * 3) = (-5, 10)
C::conj((3, 5)) = (3, -1 * 5)

C::normSq(z) = 3^2 + 4^2 = 25
C::norm(z) = 5
C::I = (0, 1)
C::ofReal(2) = (2, 0)
```

## 2. `int`

- Category: `std interface`
- System surface: `Int`
- Purpose: Smoke test for integer divisibility, gcd, floor, and ceiling APIs.

```litex
import Int

witness exist k Z st {12 = 3 * k} from 4:
    12 = 3 * 4
$Int::Dvd(3, 12)

witness exist k Z st {-4 = 2 * k} from -2:
    -4 = 2 * -2
$Int::Even(-4)

witness exist k Z st {-3 = 2 * k + 1} from -2:
    -3 = 2 * -2 + 1
$Int::Odd(-3)

$Int::ModEq(5, 11, 1)

by thm Int::gcd_def(4, -6)
Int::gcd(4, -6) = Nat::gcd(Int::natAbs(4), Int::natAbs(-6))

by thm Int::gcd_eq_gcd_ab(56, 35)
Int::gcd(56, 35) = 56 * Int::gcdA(56, 35) + 35 * Int::gcdB(56, 35)

by thm Int::gcd_dvd_left(56, 35)
$Int::Dvd(Int::gcd(56, 35), 56)

by thm Int::gcd_dvd_right(56, 35)
$Int::Dvd(Int::gcd(56, 35), 35)

by thm Int::floor_le(3 / 2)
Int::floor(3 / 2) <= 3 / 2

by thm Int::le_ceil(3 / 2)
3 / 2 <= Int::ceil(3 / 2)
```

## 3. `nat`

- Category: `std interface`
- System surface: `Nat`
- Purpose: Smoke test for natural-number arithmetic, primes, and well-ordering APIs.

```litex
import Nat

witness exist k N st {4 = 2 * k} from 2:
    4 = 2 * 2
$Nat::Even(4)

witness exist k N st {5 = 2 * k + 1} from 2:
    5 = 2 * 2 + 1
$Nat::Odd(5)

witness exist k N st {12 = 3 * k} from 4:
    12 = 3 * 4
$Nat::Dvd(3, 12)

$Nat::ModEq(4, 11, 3)

by thm Nat::euclidean_division(17, 5)
exist m, r N st {$Nat::EuclideanDivision(17, 5, m, r)}

by thm Nat::Prime_two(0)
$Nat::Prime(2)

by thm Nat::Prime_one_lt(2)
1 < 2

by thm Nat::gcd_comm(4, 6)
Nat::gcd(4, 6) = Nat::gcd(6, 4)

by thm Nat::gcd_dvd_left(4, 6)
$Nat::Dvd(Nat::gcd(4, 6), 4)

by thm Nat::one_coprime(4)
$Nat::Coprime(1, 4)

by thm Nat::exists_prime_and_dvd(91)
exist p N st {$Nat::Prime(p), $Nat::Dvd(p, 91)}

Nat::choose_fn(5, 0) = 1
Nat::sqrt_nat(9)^2 <= 9

$is_nonempty_set({2, 5})
by thm Nat::well_ordering_principle({2, 5})
exist! m N st {$Nat::LeastElementOfNSubset({2, 5}, m)}

by thm Nat::least_of_N_subset_is_least({2, 5})
$Nat::LeastElementOfNSubset({2, 5}, Nat::least_of_N_subset({2, 5}))
Nat::least_of_N_subset({2, 5}) $in {2, 5}
```

## 4. `rat`

- Category: `std interface`
- System surface: `Rat`
- Purpose: Smoke test for rational-number std interfaces.

```litex
import Rat

Rat::den(3 / 2) != 0
Rat::num(3 / 2) $in Z

by thm Rat::den_nz(3 / 2)
Rat::den(3 / 2) != 0

by thm Rat::num_div_den(3 / 2)
3 / 2 = Rat::num(3 / 2) / Rat::den(3 / 2)

by thm Rat::exists_rat_between(1, 2)
exist q Q st {1 < q < 2}

by thm Rat::num_den_coprime(3 / 2)
$Nat::Coprime(Int::natAbs(Rat::num(3 / 2)), Rat::den(3 / 2))
```

## 5. `real`

- Category: `std interface`
- System surface: `Real`
- Purpose: Smoke test for real-number std interfaces.

```litex
import Real

sqrt(4) = 2
Real::logb(2, 8) = 3
pi = pi

by thm Real::exists_rat_between(1, 2)
exist q Q st {1 < q < 2}

by thm Real::exists_real_between(1, 2)
exist x R st {1 < x < 2}

by thm Real::exists_nat_inv_lt(1 / 10)
exist n N_pos st {1 / n < 1 / 10}

by thm Real::exists_nat_ge(3 / 2)
exist n N_pos st {3 / 2 <= n}

by thm Real::exists_nat_mul_gt(3, 1 / 2)
exist n N_pos st {n * (1 / 2) > 3}

by thm Real::exists_positive_rat_le(3 / 2)
exist r Q_pos st {r <= 3 / 2}

by thm Real::positive_rational_power_strict_mono(2, 1, 1 / 2)
2^(1 / 2) > 1^(1 / 2)

by thm Real::exists_rat_seq_converging_to_real(sqrt(2))
exist a seq(Q) st {$Real::rat_seq_converges(a, sqrt(2)), $Real::rat_seq_cauchy(a)}

by thm Real::exists_seq_converging_to_real(sqrt(2))
exist b seq(R) st {$Real::seq_converges(b, sqrt(2)), $Real::cauchy(b)}

have E set

know:
    $Real::nonempty_subset(E)
    $Real::has_upper_bound(E)

by thm Real::exists_least_upper_bound(E)
$Real::has_least_upper_bound(E)
```

## 6. `trig`

- Category: `std interface`
- System surface: `Trig`
- Purpose: Smoke test for trigonometric std interfaces.

```litex
import Trig

Trig::sin(0) = 0
Trig::cos(0) = 1
(2 * pi / 3 - pi / 2) / pi = 1 / 6

Trig::cos(2 * pi / 3) != 0
```

## 7. `zmod`

- Category: `std interface`
- System surface: `Zmod`
- Purpose: Smoke test for modular arithmetic std interfaces.

```litex
import ZMod

by thm ZMod::value_ZMod(5)
$ZMod::value(5, ZMod::ZMod(5))

1 < 5
1 $in ZMod::ZMod(5)

ZMod::repr(6, 5) = 1
ZMod::add(5, 3, 4) = 2
ZMod::mul(5, 3, 4) = 2

$ZMod::congruent(5, 6, 1)
```
