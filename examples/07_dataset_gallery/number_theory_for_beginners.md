# Weil Number Theory for Beginners

Number-theory examples using the public std/Nat interface for divisibility, gcd, coprimality, primes, modular arithmetic, and related witnesses.

Each item gives the mathematical idea first, then the Litex code that checks it.

## 1. `choose_and_sqrt_interfaces`

```yaml
id: "choose_and_sqrt_interfaces"
source: "Weil Number Theory for Beginners"
topic: "binomial and sqrt"
difficulty: "intro"
natural_language_idea: "Check two small standard-library interfaces for choose and integer square root."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::choose_zero_right(5)
Nat::choose_fn(5, 0) = 1
by thm Nat::choose_self(5)
Nat::choose_fn(5, 5) = 1
by thm Nat::sqrt_sq_le(9)
Nat::sqrt_nat(9)^2 <= 9
```

## 2. `coprime_1_4`

```yaml
id: "coprime_1_4"
source: "Weil Number Theory for Beginners"
topic: "coprimality"
difficulty: "intro"
natural_language_idea: "Use the theorem that 1 is coprime to every natural."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::one_coprime(4)
$Nat::Coprime(1, 4)
```

## 3. `coprime_4_1`

```yaml
id: "coprime_4_1"
source: "Weil Number Theory for Beginners"
topic: "coprimality"
difficulty: "intro"
natural_language_idea: "Use the theorem that every natural is coprime to 1 on the right."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::coprime_one_right(4)
$Nat::Coprime(4, 1)
```

## 4. `coprime_symmetry`

```yaml
id: "coprime_symmetry"
source: "Weil Number Theory for Beginners"
topic: "coprimality"
difficulty: "intro"
natural_language_idea: "Turn coprimality around using symmetry."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::coprime_one_right(4)
$Nat::Coprime(4, 1)
by thm Nat::Coprime_symm(4, 1)
$Nat::Coprime(1, 4)
```

## 5. `division_with_remainder_17_5`

```yaml
id: "division_with_remainder_17_5"
source: "Weil Number Theory for Beginners"
topic: "division algorithm"
difficulty: "chapter 2"
natural_language_idea: "Use quotient 3 and remainder 2 for division of 17 by 5."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

$Nat::EuclideanDivision(17, 5, 3, 2)
by thm Nat::euclidean_division(17, 5)
exist m, r N st {$Nat::EuclideanDivision(17, 5, m, r)}
```

## 6. `dvd_3_12`

```yaml
id: "dvd_3_12"
source: "Weil Number Theory for Beginners"
topic: "divisibility"
difficulty: "intro"
natural_language_idea: "Check that 3 divides 12 by giving quotient 4."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

witness exist k N st {12 = 3 * k} from 4:
    12 = 3 * 4
$Nat::Dvd(3, 12)
```

## 7. `dvd_gcd_from_two_divisibilities`

```yaml
id: "dvd_gcd_from_two_divisibilities"
source: "Weil Number Theory for Beginners"
topic: "gcd"
difficulty: "intro"
natural_language_idea: "Combine two divisibility facts into a divisibility of the gcd."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

witness exist k N st {12 = 3 * k} from 4:
    12 = 3 * 4
$Nat::Dvd(3, 12)
witness exist k N st {18 = 3 * k} from 6:
    18 = 3 * 6
$Nat::Dvd(3, 18)
by thm Nat::dvd_gcd(12, 18, 3)
$Nat::Dvd(3, Nat::gcd(12, 18))
```

## 8. `dvd_refl_12`

```yaml
id: "dvd_refl_12"
source: "Weil Number Theory for Beginners"
topic: "divisibility"
difficulty: "intro"
natural_language_idea: "Use reflexivity of divisibility for 12."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::dvd_refl(12)
$Nat::Dvd(12, 12)
```

## 9. `even_8`

```yaml
id: "even_8"
source: "Weil Number Theory for Beginners"
topic: "parity"
difficulty: "intro"
natural_language_idea: "Check the Nat-library even predicate by giving the witness 4."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

witness exist k N st {8 = 2 * k} from 4:
    8 = 2 * 4
$Nat::Even(8)
```

## 10. `gcd_comm_6_9`

```yaml
id: "gcd_comm_6_9"
source: "Weil Number Theory for Beginners"
topic: "gcd"
difficulty: "intro"
natural_language_idea: "Apply gcd commutativity to swap the arguments 6 and 9."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::gcd_comm(6, 9)
Nat::gcd(6, 9) = Nat::gcd(9, 6)
```

## 11. `gcd_dvd_left_6_9`

```yaml
id: "gcd_dvd_left_6_9"
source: "Weil Number Theory for Beginners"
topic: "gcd"
difficulty: "intro"
natural_language_idea: "Use the theorem that gcd divides the left argument."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::gcd_dvd_left(6, 9)
$Nat::Dvd(Nat::gcd(6, 9), 6)
```

## 12. `gcd_dvd_right_6_9`

```yaml
id: "gcd_dvd_right_6_9"
source: "Weil Number Theory for Beginners"
topic: "gcd"
difficulty: "intro"
natural_language_idea: "Use the theorem that gcd divides the right argument."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::gcd_dvd_right(6, 9)
$Nat::Dvd(Nat::gcd(6, 9), 9)
```

## 13. `mod_eq_17_2_mod_5`

```yaml
id: "mod_eq_17_2_mod_5"
source: "Weil Number Theory for Beginners"
topic: "modular arithmetic"
difficulty: "intro"
natural_language_idea: "Record that 17 and 2 are congruent modulo 5."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

17 % 5 = 2
2 % 5 = 2
$Nat::ModEq(5, 17, 2)
```

## 14. `mod_eq_symmetry`

```yaml
id: "mod_eq_symmetry"
source: "Weil Number Theory for Beginners"
topic: "modular arithmetic"
difficulty: "intro"
natural_language_idea: "Use symmetry of modular congruence."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

$Nat::ModEq(5, 17, 2)
by thm Nat::ModEq_symm(5, 17, 2)
$Nat::ModEq(5, 2, 17)
```

## 15. `not_prime_one`

```yaml
id: "not_prime_one"
source: "Weil Number Theory for Beginners"
topic: "primes"
difficulty: "chapter 4"
natural_language_idea: "Use the std theorem that 1 is not prime."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::not_prime_one(0)
not $Nat::Prime(1)
```

## 16. `not_prime_zero`

```yaml
id: "not_prime_zero"
source: "Weil Number Theory for Beginners"
topic: "primes"
difficulty: "chapter 4"
natural_language_idea: "Use the std theorem that 0 is not prime."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::not_prime_zero(0)
not $Nat::Prime(0)
```

## 17. `odd_9`

```yaml
id: "odd_9"
source: "Weil Number Theory for Beginners"
topic: "parity"
difficulty: "intro"
natural_language_idea: "Check the Nat-library odd predicate by giving the witness 4."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

witness exist k N st {9 = 2 * k + 1} from 4:
    9 = 2 * 4 + 1
$Nat::Odd(9)
```

## 18. `prime_2`

```yaml
id: "prime_2"
source: "Weil Number Theory for Beginners"
topic: "primes"
difficulty: "chapter 4"
natural_language_idea: "Use the std theorem that 2 is prime."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::Prime_two(0)
$Nat::Prime(2)
```

## 19. `prime_2_one_lt`

```yaml
id: "prime_2_one_lt"
source: "Weil Number Theory for Beginners"
topic: "primes"
difficulty: "chapter 4"
natural_language_idea: "Use primality of 2 to derive 1 < 2."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

by thm Nat::Prime_two(0)
$Nat::Prime(2)
by thm Nat::Prime_one_lt(2)
1 < 2
```

## 20. `prime_divisor_witness_91`

```yaml
id: "prime_divisor_witness_91"
source: "Weil Number Theory for Beginners"
topic: "primes"
difficulty: "chapter 4"
natural_language_idea: "Use the existence theorem for a prime divisor of any natural number at least 2."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example using the public std/Nat interface."
```

```litex
import Nat

2 <= 91
by thm Nat::exists_prime_and_dvd(91)
exist p N st {$Nat::Prime(p), $Nat::Dvd(p, 91)}
```
