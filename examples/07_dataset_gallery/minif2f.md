# miniF2F

Finished theorem-proving examples with contest algebra, inequalities, number theory, induction, and olympiad-style reasoning.

Each item gives the mathematical idea first, then the Litex code that checks it.

## 1. `aime_1994_p3`

```yaml
id: "aime_1994_p3"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall f fn(n Z) Z:
            forall n Z:
                f(n) + f(n - 1) = n^2
            f(19) = 94
            =>:
                f(94) % 1000 = 561

    f(20) + f(19) = 20^2
    f(20) = 20^2 - f(19) = 306
    f(21) + f(20) = 21^2
    f(21) = 21^2 - f(20) = 135
    f(22) + f(21) = 22^2
    f(22) = 22^2 - f(21) = 349
    f(23) + f(22) = 23^2
    f(23) = 23^2 - f(22) = 180
    f(24) + f(23) = 24^2
    f(24) = 24^2 - f(23) = 396
    f(25) + f(24) = 25^2
    f(25) = 25^2 - f(24) = 229
    f(26) + f(25) = 26^2
    f(26) = 26^2 - f(25) = 447
    f(27) + f(26) = 27^2
    f(27) = 27^2 - f(26) = 282
    f(28) + f(27) = 28^2
    f(28) = 28^2 - f(27) = 502
    f(29) + f(28) = 29^2
    f(29) = 29^2 - f(28) = 339
    f(30) + f(29) = 30^2
    f(30) = 30^2 - f(29) = 561
    f(31) + f(30) = 31^2
    f(31) = 31^2 - f(30) = 400
    f(32) + f(31) = 32^2
    f(32) = 32^2 - f(31) = 624
    f(33) + f(32) = 33^2
    f(33) = 33^2 - f(32) = 465
    f(34) + f(33) = 34^2
    f(34) = 34^2 - f(33) = 691
    f(35) + f(34) = 35^2
    f(35) = 35^2 - f(34) = 534
    f(36) + f(35) = 36^2
    f(36) = 36^2 - f(35) = 762
    f(37) + f(36) = 37^2
    f(37) = 37^2 - f(36) = 607
    f(38) + f(37) = 38^2
    f(38) = 38^2 - f(37) = 837
    f(39) + f(38) = 39^2
    f(39) = 39^2 - f(38) = 684
    f(40) + f(39) = 40^2
    f(40) = 40^2 - f(39) = 916
    f(41) + f(40) = 41^2
    f(41) = 41^2 - f(40) = 765
    f(42) + f(41) = 42^2
    f(42) = 42^2 - f(41) = 999
    f(43) + f(42) = 43^2
    f(43) = 43^2 - f(42) = 850
    f(44) + f(43) = 44^2
    f(44) = 44^2 - f(43) = 1086
    f(45) + f(44) = 45^2
    f(45) = 45^2 - f(44) = 939
    f(46) + f(45) = 46^2
    f(46) = 46^2 - f(45) = 1177
    f(47) + f(46) = 47^2
    f(47) = 47^2 - f(46) = 1032
    f(48) + f(47) = 48^2
    f(48) = 48^2 - f(47) = 1272
    f(49) + f(48) = 49^2
    f(49) = 49^2 - f(48) = 1129
    f(50) + f(49) = 50^2
    f(50) = 50^2 - f(49) = 1371
    f(51) + f(50) = 51^2
    f(51) = 51^2 - f(50) = 1230
    f(52) + f(51) = 52^2
    f(52) = 52^2 - f(51) = 1474
    f(53) + f(52) = 53^2
    f(53) = 53^2 - f(52) = 1335
    f(54) + f(53) = 54^2
    f(54) = 54^2 - f(53) = 1581
    f(55) + f(54) = 55^2
    f(55) = 55^2 - f(54) = 1444
    f(56) + f(55) = 56^2
    f(56) = 56^2 - f(55) = 1692
    f(57) + f(56) = 57^2
    f(57) = 57^2 - f(56) = 1557
    f(58) + f(57) = 58^2
    f(58) = 58^2 - f(57) = 1807
    f(59) + f(58) = 59^2
    f(59) = 59^2 - f(58) = 1674
    f(60) + f(59) = 60^2
    f(60) = 60^2 - f(59) = 1926
    f(61) + f(60) = 61^2
    f(61) = 61^2 - f(60) = 1795
    f(62) + f(61) = 62^2
    f(62) = 62^2 - f(61) = 2049
    f(63) + f(62) = 63^2
    f(63) = 63^2 - f(62) = 1920
    f(64) + f(63) = 64^2
    f(64) = 64^2 - f(63) = 2176
    f(65) + f(64) = 65^2
    f(65) = 65^2 - f(64) = 2049
    f(66) + f(65) = 66^2
    f(66) = 66^2 - f(65) = 2307
    f(67) + f(66) = 67^2
    f(67) = 67^2 - f(66) = 2182
    f(68) + f(67) = 68^2
    f(68) = 68^2 - f(67) = 2442
    f(69) + f(68) = 69^2
    f(69) = 69^2 - f(68) = 2319
    f(70) + f(69) = 70^2
    f(70) = 70^2 - f(69) = 2581
    f(71) + f(70) = 71^2
    f(71) = 71^2 - f(70) = 2460
    f(72) + f(71) = 72^2
    f(72) = 72^2 - f(71) = 2724
    f(73) + f(72) = 73^2
    f(73) = 73^2 - f(72) = 2605
    f(74) + f(73) = 74^2
    f(74) = 74^2 - f(73) = 2871
    f(75) + f(74) = 75^2
    f(75) = 75^2 - f(74) = 2754
    f(76) + f(75) = 76^2
    f(76) = 76^2 - f(75) = 3022
    f(77) + f(76) = 77^2
    f(77) = 77^2 - f(76) = 2907
    f(78) + f(77) = 78^2
    f(78) = 78^2 - f(77) = 3177
    f(79) + f(78) = 79^2
    f(79) = 79^2 - f(78) = 3064
    f(80) + f(79) = 80^2
    f(80) = 80^2 - f(79) = 3336
    f(81) + f(80) = 81^2
    f(81) = 81^2 - f(80) = 3225
    f(82) + f(81) = 82^2
    f(82) = 82^2 - f(81) = 3499
    f(83) + f(82) = 83^2
    f(83) = 83^2 - f(82) = 3390
    f(84) + f(83) = 84^2
    f(84) = 84^2 - f(83) = 3666
    f(85) + f(84) = 85^2
    f(85) = 85^2 - f(84) = 3559
    f(86) + f(85) = 86^2
    f(86) = 86^2 - f(85) = 3837
    f(87) + f(86) = 87^2
    f(87) = 87^2 - f(86) = 3732
    f(88) + f(87) = 88^2
    f(88) = 88^2 - f(87) = 4012
    f(89) + f(88) = 89^2
    f(89) = 89^2 - f(88) = 3909
    f(90) + f(89) = 90^2
    f(90) = 90^2 - f(89) = 4191
    f(91) + f(90) = 91^2
    f(91) = 91^2 - f(90) = 4090
    f(92) + f(91) = 92^2
    f(92) = 92^2 - f(91) = 4374
    f(93) + f(92) = 93^2
    f(93) = 93^2 - f(92) = 4275
    f(94) + f(93) = 94^2
    f(94) = 94^2 - f(93) = 4561
    f(94) % 1000 = 4561 % 1000 = 561
```

## 2. `algebra_absapbon1pabsapbleqsumabsaon1pabsa`

```yaml
id: "algebra_absapbon1pabsapbleqsumabsaon1pabsa"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall t R:
            1 + abs(t) != 0

    0 <= abs(t)
    1 <= 1 + abs(t)
    1 + abs(t) > 0
    1 + abs(t) != 0

claim:
    prove:
        forall a, b R:
            abs(a + b) / (1 + abs(a + b)) <= abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b))

    abs(a + b) <= abs(a) + abs(b)
    0 <= abs(a) * abs(b) * (2 + abs(a) + abs(b))
    0 <= abs(a) + abs(b)
    1 <= 1 + abs(a) + abs(b)
    1 + abs(a) + abs(b) > 0
    1 + abs(a) + abs(b) != 0
    0 < (1 + abs(a)) * (1 + abs(b)) * (1 + abs(a) + abs(b))
    0 <= (abs(a) * abs(b) * (2 + abs(a) + abs(b))) / ((1 + abs(a)) * (1 + abs(b)) * (1 + abs(a) + abs(b)))
    abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - (abs(a) + abs(b)) / (1 + abs(a) + abs(b)) = (abs(a) * abs(b) * (2 + abs(a) + abs(b))) / ((1 + abs(a)) * (1 + abs(b)) * (1 + abs(a) + abs(b)))
    0 <= abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - (abs(a) + abs(b)) / (1 + abs(a) + abs(b))
    0 <= abs(a) + abs(b) - abs(a + b)
    0 < (1 + abs(a + b)) * (1 + abs(a) + abs(b))
    0 <= (abs(a) + abs(b) - abs(a + b)) / ((1 + abs(a + b)) * (1 + abs(a) + abs(b)))
    (abs(a) + abs(b)) / (1 + abs(a) + abs(b)) - abs(a + b) / (1 + abs(a + b)) = (abs(a) + abs(b) - abs(a + b)) / ((1 + abs(a + b)) * (1 + abs(a) + abs(b)))
    0 <= (abs(a) + abs(b)) / (1 + abs(a) + abs(b)) - abs(a + b) / (1 + abs(a + b))
    0 <= (abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - (abs(a) + abs(b)) / (1 + abs(a) + abs(b))) + ((abs(a) + abs(b)) / (1 + abs(a) + abs(b)) - abs(a + b) / (1 + abs(a + b)))
    (abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - (abs(a) + abs(b)) / (1 + abs(a) + abs(b))) + ((abs(a) + abs(b)) / (1 + abs(a) + abs(b)) - abs(a + b) / (1 + abs(a + b))) = abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - abs(a + b) / (1 + abs(a + b))
    0 <= abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b)) - abs(a + b) / (1 + abs(a + b))
    abs(a + b) / (1 + abs(a + b)) <= abs(a) / (1 + abs(a)) + abs(b) / (1 + abs(b))
```

## 3. `algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3`

```yaml
id: "algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall a, b, c R:
            a <= b
            b <= c
            a + b + c = 2
            a * b + b * c + c * a = 1
            =>:
                0 <= a and a <= 1 / 3 and 1 / 3 <= b and b <= 1 and 1 <= c and c <= 4 / 3

    a <= b <= c
    a <= c
    b + c = a + b + c - a = 2 - a
    a + c = a + b + c - b = 2 - b
    a + b = a + b + c - c = 2 - c
    a * (b + c) + b * c = a * b + a * c + b * c = a * b + b * c + c * a = 1
    b * (a + c) + a * c = a * b + b * c + c * a = 1
    c * (a + b) + a * b = a * b + b * c + c * a = 1
    b * c + a * (b + c) = 1
    a * c + b * (a + c) = 1
    a * b + c * (a + b) = 1
    b * c = 1 - a * (b + c) = 1 - a * (2 - a) = (1 - a)^2
    a * c = 1 - b * (a + c) = 1 - b * (2 - b) = (1 - b)^2
    a * b = 1 - c * (a + b) = 1 - c * (2 - c) = (1 - c)^2
    (b - c)^2 >= 0
    (a - c)^2 >= 0
    (a - b)^2 >= 0
    (b + c)^2 - 4 * b * c = (b - c)^2
    (a + c)^2 - 4 * a * c = (a - c)^2
    (a + b)^2 - 4 * a * b = (a - b)^2
    (2 - a)^2 - 4 * (1 - a)^2 = a * (4 - 3 * a)
    (2 - b)^2 - 4 * (1 - b)^2 = b * (4 - 3 * b)
    (2 - c)^2 - 4 * (1 - c)^2 = c * (4 - 3 * c)
    (b + c)^2 = (2 - a)^2
    4 * (b * c) = 4 * (1 - a)^2
    (a + c)^2 = (2 - b)^2
    4 * (a * c) = 4 * (1 - b)^2
    (a + b)^2 = (2 - c)^2
    4 * (a * b) = 4 * (1 - c)^2
    (b - c)^2 = (b + c)^2 - 4 * b * c = (2 - a)^2 - 4 * (1 - a)^2 = a * (4 - 3 * a)
    (a - c)^2 = (a + c)^2 - 4 * a * c = (2 - b)^2 - 4 * (1 - b)^2 = b * (4 - 3 * b)
    (a - b)^2 = (a + b)^2 - 4 * a * b = (2 - c)^2 - 4 * (1 - c)^2 = c * (4 - 3 * c)
    0 <= (b - c)^2 = a * (4 - 3 * a)
    0 <= (a - c)^2 = b * (4 - 3 * b)
    0 <= (a - b)^2 = c * (4 - 3 * c)
    a - b <= 0
    a - c <= 0
    b - c <= 0
    0 <= (a - b) * (a - c)
    (b - a) * (c - b) >= 0
    0 <= (c - a) * (c - b)
    (a - b) * (a - c) = a^2 - a * (b + c) + b * c
    a^2 - a * (b + c) + b * c = a^2 - a * (2 - a) + (1 - a)^2 = (3 * a - 1) * (a - 1)
    (b - a) * (c - b) = b * (a + c) - b^2 - a * c
    b * (a + c) - b^2 - a * c = b * (2 - b) - b^2 - (1 - b)^2 = (3 * b - 1) * (1 - b)
    (c - a) * (c - b) = c^2 - c * (a + b) + a * b
    c^2 - c * (a + b) + a * b = c^2 - c * (2 - c) + (1 - c)^2 = (3 * c - 1) * (c - 1)
    (a - b) * (a - c) = (3 * a - 1) * (a - 1)
    (b - a) * (c - b) = (3 * b - 1) * (1 - b)
    (c - a) * (c - b) = (3 * c - 1) * (c - 1)
    3 * a = a + a + a <= a + b + c = 2
    a = (3 * a) / 3 <= 2 / 3
    3 * a <= 2
    4 - 3 * a = 4 - (3 * a) >= 4 - 2 = 2
    4 - 3 * a > 0
    a = (a * (4 - 3 * a)) / (4 - 3 * a) >= 0 / (4 - 3 * a) = 0
    2 = a + b + c <= c + c + c = 3 * c
    2 / 3 <= (3 * c) / 3 = c
    0 < 2 / 3
    0 < 2 / 3 <= c
    0 < c
    4 - 3 * c = (c * (4 - 3 * c)) / c >= 0 / c = 0
    4 - 3 * c >= 0
    3 * c <= 4
    c = (3 * c) / 3 <= 4 / 3
    3 * c - 1 >= 1
    3 * c - 1 > 0
    c - 1 = ((3 * c - 1) * (c - 1)) / (3 * c - 1) >= 0 / (3 * c - 1) = 0
    1 <= c
    a - 1 <= 2 / 3 - 1 = -1 / 3
    -1 / 3 < 0
    a - 1 <= -1 / 3 < 0
    a - 1 < 0
    3 * a - 1 = ((3 * a - 1) * (a - 1)) / (a - 1) <= 0 / (a - 1) = 0
    3 * a - 1 <= 0
    3 * a <= 1
    a = (3 * a) / 3 <= 1 / 3
    b = a + b + c - a - c = 2 - a - c
    2 - a - c >= 2 - 1 / 3 - c
    2 - 1 / 3 - c >= 2 - 1 / 3 - 4 / 3 = 1 / 3
    b = 2 - a - c >= 2 - 1 / 3 - c >= 2 - 1 / 3 - 4 / 3 = 1 / 3
    2 - a - c <= 2 - 0 - c
    2 - 0 - c <= 2 - 0 - 1 = 1
    b = 2 - a - c <= 2 - 0 - c <= 2 - 0 - 1 = 1
    0 <= a and a <= 1 / 3 and 1 / 3 <= b and b <= 1 and 1 <= c and c <= 4 / 3
```

## 4. `algebra_sqineq_unitcircatbpabsamblt1`

```yaml
id: "algebra_sqineq_unitcircatbpabsamblt1"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall a, b R:
            a^2 + b^2 = 1
            =>:
                a * b + abs(a - b) <= 1

    0 <= a^2
    0 <= b^2
    a^2 <= a^2 + b^2 = 1
    b^2 <= a^2 + b^2 = 1

    0 <= (a - 1)^2
    (a - 1)^2 = a^2 - 2 * a + 1 <= 1 - 2 * a + 1 = 2 - 2 * a
    0 <= (a - 1)^2 <= 2 - 2 * a
    0 <= 2 - 2 * a
    2 * a <= 2
    a = (2 * a) / 2 <= 2 / 2 = 1

    0 <= (b + 1)^2
    (b + 1)^2 = b^2 + 2 * b + 1 <= 1 + 2 * b + 1 = 2 * b + 2
    0 <= (b + 1)^2 <= 2 * b + 2
    0 <= 2 * b + 2
    -2 = -2 + 0 <= -2 + (2 * b + 2) = 2 * b
    -1 = -2 / 2 <= (2 * b) / 2 = b
    -1 <= b

    0 <= (a + 1)^2
    (a + 1)^2 = a^2 + 2 * a + 1 <= 1 + 2 * a + 1 = 2 * a + 2
    0 <= (a + 1)^2 <= 2 * a + 2
    0 <= 2 * a + 2
    -2 = -2 + 0 <= -2 + (2 * a + 2) = 2 * a
    -1 = -2 / 2 <= (2 * a) / 2 = a
    -1 <= a

    0 <= (b - 1)^2
    (b - 1)^2 = b^2 - 2 * b + 1 <= 1 - 2 * b + 1 = 2 - 2 * b
    0 <= (b - 1)^2 <= 2 - 2 * b
    0 <= 2 - 2 * b
    2 * b <= 2
    b = (2 * b) / 2 <= 2 / 2 = 1

    by cases:
        prove:
            a * b + abs(a - b) <= 1
        case a - b >= 0:
            abs(a - b) = a - b
            0 <= 1 - a
            0 = 1 + -1 <= 1 + b
            0 <= (1 - a) * (1 + b)
            (1 - a) * (1 + b) = 1 - (a * b + (a - b))
            0 <= 1 - (a * b + (a - b))
            a * b + abs(a - b) = a * b + (a - b)
            a * b + (a - b) = a * b + (a - b) + 0 <= a * b + (a - b) + (1 - (a * b + (a - b))) = 1
        case a - b < 0:
            abs(a - b) = -(a - b) = b - a
            0 = 1 + -1 <= 1 + a
            0 <= 1 - b
            0 <= (1 + a) * (1 - b)
            (1 + a) * (1 - b) = 1 - (a * b + (b - a))
            0 <= 1 - (a * b + (b - a))
            a * b + abs(a - b) = a * b + (b - a)
            a * b + (b - a) = a * b + (b - a) + 0 <= a * b + (b - a) + (1 - (a * b + (b - a))) = 1
```

## 5. `amc12_2000_p15`

```yaml
id: "amc12_2000_p15"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
# Natural-language idea:
# From f(x / 3) = x^2 + x + 1, substitute x = 9z to get
# f(3z) = 81z^2 + 9z + 1.  The equation f(3z)=7 becomes
# 27z^2 + 3z - 2 = 0, which factors as (9z-2)(3z+1)=0.
# Thus the z-values are 2/9 and -1/3, and their sum is -1/9.

claim:
    prove:
        forall z R, f fn(x R) R:
            forall x R:
                f(x / 3) = x^2 + x + 1
            f(3 * z) = 7
            =>:
                z = 2 / 9 or z = -1 / 3
    f(3 * z) = f((9 * z) / 3) = (9 * z)^2 + 9 * z + 1
    (9 * z)^2 + 9 * z + 1 = 7
    (9 * z)^2 + 9 * z + 1 - 7 = 0
    (9 * z)^2 = 81 * z^2
    (9 * z)^2 + 9 * z + 1 - 7 = 81 * z^2 + 9 * z - 6
    81 * z^2 + 9 * z - 6 = 0
    3 * (27 * z^2 + 3 * z - 2) = 81 * z^2 + 9 * z - 6 = 0
    27 * z^2 + 3 * z - 2 = 0 / 3 = 0
    (9 * z - 2) * (3 * z + 1) = 27 * z^2 + 3 * z - 2 = 0
    by cases:
        prove:
            z = 2 / 9 or z = -1 / 3
        case 9 * z - 2 = 0:
            9 * z = 2
            z = 2 / 9
            z = 2 / 9 or z = -1 / 3
        case 9 * z - 2 != 0:
            3 * z + 1 = 0 / (9 * z - 2) = 0
            3 * z = -1
            z = -1 / 3
            z = 2 / 9 or z = -1 / 3

claim:
    prove:
        forall f fn(x R) R:
            forall x R:
                f(x / 3) = x^2 + x + 1
            =>:
                f(3 * (2 / 9)) = 7
                f(3 * (-1 / 3)) = 7
                2 / 9 > -1 / 3
                2 / 9 + (-1 / 3) = -1 / 9
    f(3 * (2 / 9)) = f((9 * (2 / 9)) / 3) = (9 * (2 / 9))^2 + 9 * (2 / 9) + 1 = 7
    f(3 * (-1 / 3)) = f((9 * (-1 / 3)) / 3) = (9 * (-1 / 3))^2 + 9 * (-1 / 3) + 1 = 7
    2 / 9 > -1 / 3
    2 / 9 + (-1 / 3) = -1 / 9
```

## 6. `amc12_2001_p9`

```yaml
id: "amc12_2001_p9"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
# Natural-language idea:
# Use the functional equation with x = 500 and y = 600/500.  Since
# 500 * (600/500) = 600 and f(500)=3, f(600)=3/(600/500)=5/2.

claim:
    prove:
        forall f fn(x R) R:
            forall x, y R:
                x > 0
                y > 0
                =>:
                    f(x * y) = f(x) / y
            f(500) = 3
            =>:
                f(600) = 5 / 2
    500 > 0
    600 / 500 > 0
    500 * (600 / 500) = 600
    f(600) = f(500 * (600 / 500)) = f(500) / (600 / 500) = 3 / (600 / 500) = 5 / 2
```

## 7. `amc12a_2008_p8`

```yaml
id: "amc12a_2008_p8"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
have fn cube_surface(x R) R = 6 * x^2
have fn cube_volume(x R) R = x^3

claim:
    prove:
        cube_volume(1) = 1 and cube_surface(1) = 6 and cube_surface(sqrt(2)) = 2 * cube_surface(1) and cube_volume(sqrt(2)) = 2 * sqrt(2)
    cube_volume(1) = 1
    cube_surface(1) = 6
    cube_surface(sqrt(2)) = 12
    cube_surface(sqrt(2)) = 2 * cube_surface(1)
    cube_volume(sqrt(2)) = sqrt(2)^3
    sqrt(2)^3 = sqrt(2)^2 * sqrt(2)
    sqrt(2)^2 = 2
    sqrt(2)^2 * sqrt(2) = 2 * sqrt(2)
    cube_volume(sqrt(2)) = sqrt(2)^3 = sqrt(2)^2 * sqrt(2) = 2 * sqrt(2)
```

## 8. `amc12a_2009_p5`

```yaml
id: "amc12a_2009_p5"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall x R:
            x ^ 3 - (x + 1) * (x - 1) * x = 5
            =>:
                (x + 1) * (x - 1) = x ^ 2 - 1
                (x + 1) * (x - 1) * x = (x ^ 2 - 1) * x
                x ^ 3 - (x + 1) * (x - 1) * x = x
                x = x ^ 3 - (x + 1) * (x - 1) * x = 5
                x ^ 3 = 5 ^ 3 = 125
```

## 9. `amc12a_2009_p9`

```yaml
id: "amc12a_2009_p9"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall a, b, c R, f fn(x R) R:
            forall x R:
                f(x + 3) = 3 * x ^ 2 + 7 * x + 4
            forall x R:
                f(x) = a * x ^ 2 + b * x + c
            =>:
                a + b + c = a * 1^2 + b * 1 + c = f(1) = f(-2 + 3) = 3 * (-2)^2 + 7 * (-2) + 4 = 2
```

## 10. `amc12a_2011_p18`

```yaml
id: "amc12a_2011_p18"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall t R:
            -1 <= t
            t <= 1
            =>:
                t^2 <= 1
    0 = 1 + (-1) <= 1 + t = t + 1
    0 = 1 - 1 <= 1 - t
    0 <= (1 - t) * (t + 1)
    (1 - t) * (t + 1) = 1 - t^2
    0 <= 1 - t^2
    t^2 <= 1

claim:
    prove:
        forall x, y R:
            -1 <= x
            x <= 1
            -1 <= y
            y <= 1
            =>:
                x^2 - 6 * x + y^2 <= 8
    x^2 <= 1
    y^2 <= 1
    0 = 6 * (-1 + 1) <= 6 * (x + 1)
    -6 * x = 6 - 6 * (x + 1) <= 6 - 0 = 6
    x^2 + (-6 * x) <= 1 + 6
    x^2 - 6 * x = x^2 + (-6 * x) <= 1 + 6
    x^2 - 6 * x + y^2 <= (1 + 6) + 1 = 8

claim:
    prove:
        forall x, y R:
            abs(x + y) + abs(x - y) = 2
            =>:
                x^2 - 6 * x + y^2 <= 8

    by cases:
        prove:
            x^2 - 6 * x + y^2 <= 8
        case x + y >= 0:
            by cases:
                prove:
                    x^2 - 6 * x + y^2 <= 8
                case x - y >= 0:
                    abs(x + y) = x + y
                    abs(x - y) = x - y
                    (x + y) + (x - y) = abs(x + y) + abs(x - y) = 2
                    2 * x = (x + y) + (x - y) = 2
                    x = (2 * x) / 2 = 2 / 2 = 1
                    -1 <= x
                    x <= 1
                    0 <= x + y = 1 + y
                    -1 = -1 + 0 <= -1 + (1 + y) = y
                    0 <= x - y = 1 - y
                    y = 1 - (1 - y) <= 1 - 0 = 1
                    x^2 - 6 * x + y^2 <= 8
                case x - y < 0:
                    abs(x + y) = x + y
                    abs(x - y) = -(x - y)
                    (x + y) + (-(x - y)) = abs(x + y) + abs(x - y) = 2
                    2 * y = (x + y) + (-(x - y)) = 2
                    y = (2 * y) / 2 = 2 / 2 = 1
                    -1 <= y
                    y <= 1
                    0 <= x + y = x + 1
                    -1 = -1 + 0 <= -1 + (x + 1) = x
                    x - 1 = x - y < 0
                    x = (x - 1) + 1 < 0 + 1 = 1
                    x <= 1
                    x^2 - 6 * x + y^2 <= 8
        case x + y < 0:
            by cases:
                prove:
                    x^2 - 6 * x + y^2 <= 8
                case x - y >= 0:
                    abs(x + y) = -(x + y)
                    abs(x - y) = x - y
                    (-(x + y)) + (x - y) = abs(x + y) + abs(x - y) = 2
                    -2 * y = (-(x + y)) + (x - y) = 2
                    y = (-2 * y) / (-2) = 2 / (-2) = -1
                    -1 <= y
                    y <= 1
                    x - 1 = x + y < 0
                    x = (x - 1) + 1 < 0 + 1 = 1
                    x <= 1
                    0 <= x - y = x + 1
                    -1 = -1 + 0 <= -1 + (x + 1) = x
                    x^2 - 6 * x + y^2 <= 8
                case x - y < 0:
                    abs(x + y) = -(x + y)
                    abs(x - y) = -(x - y)
                    (-(x + y)) + (-(x - y)) = abs(x + y) + abs(x - y) = 2
                    -2 * x = (-(x + y)) + (-(x - y)) = 2
                    x = (-2 * x) / (-2) = 2 / (-2) = -1
                    -1 <= x
                    x <= 1
                    y - 1 = x + y < 0
                    y = (y - 1) + 1 < 0 + 1 = 1
                    y <= 1
                    -1 - y = x - y < 0
                    -1 = (-1 - y) + y < 0 + y = y
                    -1 <= y
                    x^2 - 6 * x + y^2 <= 8

# Natural-language idea:
# Triangle inequalities give abs(x) <= 1 and abs(y) <= 1 from
# abs(x+y)+abs(x-y)=2. Then x^2 <= 1, y^2 <= 1, and x >= -1 imply
# x^2 - 6x + y^2 <= 1 + 6 + 1 = 8.
```

## 11. `amc12a_2015_p10`

```yaml
id: "amc12a_2015_p10"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
# Natural-language idea:
# From x + y + xy = 80, get (x + 1)(y + 1) = 81.
# Since x > y > 0, the factors satisfy x + 1 > y + 1 > 1.
# The smaller factor is a positive integer b with b^2 < 81, hence 2 <= b <= 8.
# Enumerating b = 2,...,8 leaves only b = 3, so x + 1 = 27 and x = 26.

thm factor_pair_81_large_first:
    prove:
        forall a, b Z:
            1 < b
            b < a
            a * b = 81
            =>:
                a = 27
    2 <= b
    0 < b
    b * b < a * b
    b ^ 2 = b * b
    b ^ 2 < a * b = 81
    b $in N_pos
    b $in R_pos
    by thm pos_pow_strict_order_reflects(b, 9, 2)
    b < 9
    b $in closed_range(2, 8)
    by closed_range as cases: b $in 2...8
    by cases:
        prove:
            a = 27
        case b = 2:
            2 * a = b * a = a * b = 81
            a = 81 / 2
            not 81 / 2 $in Z
            impossible a $in Z
        case b = 3:
            3 * a = b * a = a * b = 81
            a = 81 / 3 = 27
        case b = 4:
            4 * a = b * a = a * b = 81
            a = 81 / 4
            not 81 / 4 $in Z
            impossible a $in Z
        case b = 5:
            5 * a = b * a = a * b = 81
            a = 81 / 5
            not 81 / 5 $in Z
            impossible a $in Z
        case b = 6:
            6 * a = b * a = a * b = 81
            a = 81 / 6
            not 81 / 6 $in Z
            impossible a $in Z
        case b = 7:
            7 * a = b * a = a * b = 81
            a = 81 / 7
            not 81 / 7 $in Z
            impossible a $in Z
        case b = 8:
            8 * a = b * a = a * b = 81
            a = 81 / 8
            not 81 / 8 $in Z
            impossible a $in Z

claim:
    prove:
        forall x, y Z:
            y > 0
            x > y
            x + y + x * y = 80
            =>:
                x = 26
    x * y + x + y = x + y + x * y = 80
    x * y + x + y + 1 = 80 + 1 = 81
    (x + 1) * (y + 1) = x * y + x + y + 1 = 81
    x + 1 $in Z
    y + 1 $in Z
    1 < y + 1
    y + 1 < x + 1
    (x + 1) * (y + 1) = 81
    by thm factor_pair_81_large_first(x + 1, y + 1)
    x + 1 = 27
    x = (x + 1) - 1 = 27 - 1 = 26
```

## 12. `amc12a_2021_p7`

```yaml
id: "amc12a_2021_p7"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall x, y R:
            (x * y - 1) ^ 2 + (x + y) ^ 2 = x ^ 2 * y ^ 2 - 2 * x * y + 1 + (x ^ 2 + 2 * x * y + y ^ 2)
            (x * y - 1) ^ 2 + (x + y) ^ 2 = x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1
            0 <= x ^ 2 * y ^ 2
            0 <= x ^ 2
            0 <= y ^ 2
            1 <= x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1 = (x * y - 1) ^ 2 + (x + y) ^ 2
```

## 13. `amc12a_2021_p8`

```yaml
id: "amc12a_2021_p8"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
import Nat

claim:
    prove:
        forall d fn(n N) N, k N:
            d(0) = 0
            d(1) = 0
            d(2) = 1
            forall m N:
                d(m + 3) = d(m + 2) + d(m)
            =>:
                d(7 * k) % 2 = 0
                d(7 * k + 1) % 2 = 0
                d(7 * k + 2) % 2 = 1
                d(7 * k + 3) % 2 = 1
                d(7 * k + 4) % 2 = 1
                d(7 * k + 5) % 2 = 0
                d(7 * k + 6) % 2 = 1

    by induc k from 0:
        prove:
            d(7 * k) % 2 = 0
            d(7 * k + 1) % 2 = 0
            d(7 * k + 2) % 2 = 1
            d(7 * k + 3) % 2 = 1
            d(7 * k + 4) % 2 = 1
            d(7 * k + 5) % 2 = 0
            d(7 * k + 6) % 2 = 1

        prove from k = 0:
            d(7 * 0) % 2 = d(0) % 2 = 0 % 2 = 0
            d(7 * 0 + 1) % 2 = d(1) % 2 = 0 % 2 = 0
            d(7 * 0 + 2) % 2 = d(2) % 2 = 1 % 2 = 1
            d(3) = d(0 + 3) = d(0 + 2) + d(0) = d(2) + d(0)
            d(7 * 0 + 3) % 2 = d(3) % 2 = (d(2) + d(0)) % 2 = ((d(2) % 2) + (d(0) % 2)) % 2 = (1 + 0) % 2 = 1
            d(4) = d(1 + 3) = d(1 + 2) + d(1) = d(3) + d(1)
            d(7 * 0 + 4) % 2 = d(4) % 2 = (d(3) + d(1)) % 2 = ((d(3) % 2) + (d(1) % 2)) % 2 = (1 + 0) % 2 = 1
            d(5) = d(2 + 3) = d(2 + 2) + d(2) = d(4) + d(2)
            d(7 * 0 + 5) % 2 = d(5) % 2 = (d(4) + d(2)) % 2 = ((d(4) % 2) + (d(2) % 2)) % 2 = (1 + 1) % 2 = 0
            d(6) = d(3 + 3) = d(3 + 2) + d(3) = d(5) + d(3)
            d(7 * 0 + 6) % 2 = d(6) % 2 = (d(5) + d(3)) % 2 = ((d(5) % 2) + (d(3) % 2)) % 2 = (0 + 1) % 2 = 1

        prove induc:
            d(7 * k + 7) = d((7 * k + 4) + 3) = d((7 * k + 4) + 2) + d(7 * k + 4) = d(7 * k + 6) + d(7 * k + 4)
            d(7 * (k + 1)) % 2 = d(7 * k + 7) % 2 = (d(7 * k + 6) + d(7 * k + 4)) % 2 = ((d(7 * k + 6) % 2) + (d(7 * k + 4) % 2)) % 2 = (1 + 1) % 2 = 0
            d(7 * k + 8) = d((7 * k + 5) + 3) = d((7 * k + 5) + 2) + d(7 * k + 5) = d(7 * k + 7) + d(7 * k + 5)
            d(7 * (k + 1) + 1) % 2 = d(7 * k + 8) % 2 = (d(7 * k + 7) + d(7 * k + 5)) % 2 = ((d(7 * k + 7) % 2) + (d(7 * k + 5) % 2)) % 2 = (0 + 0) % 2 = 0
            d(7 * k + 9) = d((7 * k + 6) + 3) = d((7 * k + 6) + 2) + d(7 * k + 6) = d(7 * k + 8) + d(7 * k + 6)
            d(7 * (k + 1) + 2) % 2 = d(7 * k + 9) % 2 = (d(7 * k + 8) + d(7 * k + 6)) % 2 = ((d(7 * k + 8) % 2) + (d(7 * k + 6) % 2)) % 2 = (0 + 1) % 2 = 1
            d(7 * k + 10) = d((7 * k + 7) + 3) = d((7 * k + 7) + 2) + d(7 * k + 7) = d(7 * k + 9) + d(7 * k + 7)
            d(7 * (k + 1) + 3) % 2 = d(7 * k + 10) % 2 = (d(7 * k + 9) + d(7 * k + 7)) % 2 = ((d(7 * k + 9) % 2) + (d(7 * k + 7) % 2)) % 2 = (1 + 0) % 2 = 1
            d(7 * k + 11) = d((7 * k + 8) + 3) = d((7 * k + 8) + 2) + d(7 * k + 8) = d(7 * k + 10) + d(7 * k + 8)
            d(7 * (k + 1) + 4) % 2 = d(7 * k + 11) % 2 = (d(7 * k + 10) + d(7 * k + 8)) % 2 = ((d(7 * k + 10) % 2) + (d(7 * k + 8) % 2)) % 2 = (1 + 0) % 2 = 1
            d(7 * k + 12) = d((7 * k + 9) + 3) = d((7 * k + 9) + 2) + d(7 * k + 9) = d(7 * k + 11) + d(7 * k + 9)
            d(7 * (k + 1) + 5) % 2 = d(7 * k + 12) % 2 = (d(7 * k + 11) + d(7 * k + 9)) % 2 = ((d(7 * k + 11) % 2) + (d(7 * k + 9) % 2)) % 2 = (1 + 1) % 2 = 0
            d(7 * k + 13) = d((7 * k + 10) + 3) = d((7 * k + 10) + 2) + d(7 * k + 10) = d(7 * k + 12) + d(7 * k + 10)
            d(7 * (k + 1) + 6) % 2 = d(7 * k + 13) % 2 = (d(7 * k + 12) + d(7 * k + 10)) % 2 = ((d(7 * k + 12) % 2) + (d(7 * k + 10) % 2)) % 2 = (0 + 1) % 2 = 1

claim:
    prove:
        forall d fn(n N) N:
            d(0) = 0
            d(1) = 0
            d(2) = 1
            forall m N:
                d(m + 3) = d(m + 2) + d(m)
            =>:
                d(2021) % 2 = 0
                d(2022) % 2 = 1
                d(2023) % 2 = 0
    2021 = 7 * 288 + 5
    2022 = 7 * 288 + 6
    2023 = 7 * 289
    d(2021) % 2 = d(7 * 288 + 5) % 2 = 0
    d(2022) % 2 = d(7 * 288 + 6) % 2 = 1
    d(2023) % 2 = d(7 * 289) % 2 = 0
```

## 14. `amc12b_2002_p6`

```yaml
id: "amc12b_2002_p6"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for an explicit, fast-running contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall a, b R:
            forall x R:
                x ^ 2 + a * x + b = (x - a) * (x - b)
            =>:
                b = a * b
    b = 0 ^ 2 + a * 0 + b = (0 - a) * (0 - b) = a * b

claim:
    prove:
        forall a, b R:
            a != 0
            b != 0
            forall x R:
                x ^ 2 + a * x + b = (x - a) * (x - b)
            =>:
                b = a * b
                a = 1
                b = -2
    b = a * b
    b / b = (a * b) / b
    1 = b / b = (a * b) / b = a
    a = 1
    1 ^ 2 + a * 1 + b = (1 - a) * (1 - b)
    1 ^ 2 + 1 * 1 + b = 1 ^ 2 + a * 1 + b
    (1 - a) * (1 - b) = (1 - 1) * (1 - b) = 0
    2 + b = 1 ^ 2 + 1 * 1 + b = 1 ^ 2 + a * 1 + b = (1 - a) * (1 - b) = 0
    b = 0 - 2 = -2
```

## 15. `amc12b_2020_p13`

```yaml
id: "amc12b_2020_p13"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
import Real

claim:
    prove:
        log(2, 3) >= 0
    1 < 2
    1 < 3
    log(2, 3) > 0
    log(2, 3) >= 0

claim:
    prove:
        log(3, 2) >= 0
    1 < 3
    1 < 2
    log(3, 2) > 0
    log(3, 2) >= 0

claim:
    prove:
        log(2, 6) + log(3, 6) >= 0
    1 < 2
    1 < 3
    1 < 6
    log(2, 6) > 0
    log(3, 6) > 0
    log(2, 6) + log(3, 6) > 0
    log(2, 6) + log(3, 6) >= 0

claim:
    prove:
        sqrt(log(2, 6) + log(3, 6)) = sqrt(log(2, 3)) + sqrt(log(3, 2))
    have A R = log(2, 3)
    have B R = log(3, 2)
    log(2, 3) > 0
    log(3, 2) > 0
    A > 0
    B > 0
    A >= 0
    B >= 0
    A != 0
    log(3, 2) = log(2, 2) / log(2, 3) = 1 / A
    B = 1 / A
    A * B = A * (1 / A) = 1
    log(2, 3) = A
    log(3, 2) = B
    sqrt(A) = sqrt(A)
    sqrt(B) = sqrt(B)
    0 <= sqrt(A)
    0 <= sqrt(B)
    0 <= sqrt(A)
    0 <= sqrt(B)
    log(2, 6) = log(2, 2 * 3) = log(2, 2) + log(2, 3) = 1 + A
    log(3, 6) = log(3, 3 * 2) = log(3, 3) + log(3, 2) = 1 + B
    log(2, 6) + log(3, 6) = (1 + A) + (1 + B) = A + B + 2
    sqrt(log(2, 3)) = sqrt(A)
    sqrt(log(3, 2)) = sqrt(B)
    sqrt(log(2, 3)) + sqrt(log(3, 2)) = sqrt(A) + sqrt(B)
    sqrt(A)^2 = A
    sqrt(B)^2 = B
    (sqrt(A) * sqrt(B))^2 = sqrt(A)^2 * sqrt(B)^2 = A * B = 1
    sqrt(A) * sqrt(B) >= 0
    sqrt(A) * sqrt(B) = sqrt((sqrt(A) * sqrt(B))^2) = sqrt(1) = 1
    (sqrt(A) + sqrt(B))^2 = sqrt(A)^2 + 2 * sqrt(A) * sqrt(B) + sqrt(B)^2
    2 * sqrt(A) * sqrt(B) = 2 * (sqrt(A) * sqrt(B))
    2 * (sqrt(A) * sqrt(B)) = 2 * 1
    sqrt(A)^2 + 2 * sqrt(A) * sqrt(B) + sqrt(B)^2 = A + 2 * 1 + B
    A + 2 * 1 + B = A + B + 2
    (sqrt(A) + sqrt(B))^2 = A + B + 2
    sqrt(A) + sqrt(B) >= 0
    sqrt((sqrt(A) + sqrt(B))^2) = sqrt(A) + sqrt(B)
    sqrt(A + B + 2) = sqrt((sqrt(A) + sqrt(B))^2) = sqrt(A) + sqrt(B)
    sqrt(log(2, 6) + log(3, 6)) = sqrt(A + B + 2) = sqrt(A) + sqrt(B) = sqrt(log(2, 3)) + sqrt(log(3, 2))
```

## 16. `amc12b_2020_p6`

```yaml
id: "amc12b_2020_p6"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall n N:
            1 <= n
            =>:
                product(1, n, 'N_pos(k){k}) >= 1

claim:
    prove:
        forall n N:
            1 <= n
            =>:
                product(1, n, 'N_pos(k){k}) != 0
    product(1, n, 'N_pos(k){k}) >= 1
    product(1, n, 'N_pos(k){k}) != 0

claim:
    prove:
        forall n N:
            9 <= n
            =>:
                exist x N st {x = n + 1, x^2 = (product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k})) / product(1, n, 'N_pos(k){k})}
    product(1, n, 'N_pos(k){k}) >= 1
    product(1, n, 'N_pos(k){k}) != 0
    product(1, n + 1, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * 'N_pos(k){k}(n + 1)
    'N_pos(k){k}(n + 1) = n + 1
    product(1, n + 1, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * (n + 1)
    product(1, n + 2, 'N_pos(k){k}) = product(1, n + 1, 'N_pos(k){k}) * 'N_pos(k){k}(n + 2)
    'N_pos(k){k}(n + 2) = n + 2
    product(1, n + 2, 'N_pos(k){k}) = product(1, n + 1, 'N_pos(k){k}) * (n + 2)
    product(1, n + 2, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * (n + 1) * (n + 2)
    product(1, n + 1, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * (n + 1)
    product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * (n + 1) * (n + 2) - product(1, n, 'N_pos(k){k}) * (n + 1)
    product(1, n, 'N_pos(k){k}) * (n + 1) * (n + 2) - product(1, n, 'N_pos(k){k}) * (n + 1) = product(1, n, 'N_pos(k){k}) * (n + 1) * ((n + 2) - 1)
    product(1, n, 'N_pos(k){k}) * (n + 1) * ((n + 2) - 1) = product(1, n, 'N_pos(k){k}) * (n + 1) * (n + 1)
    product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k}) = product(1, n, 'N_pos(k){k}) * (n + 1) * (n + 1)
    (product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k})) / product(1, n, 'N_pos(k){k}) = (n + 1) * (n + 1)
    (n + 1)^2 = (n + 1) * (n + 1)
    witness exist x N st {x = n + 1, x^2 = (product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k})) / product(1, n, 'N_pos(k){k})} from n + 1:
        n + 1 = n + 1
        (n + 1)^2 = (product(1, n + 2, 'N_pos(k){k}) - product(1, n + 1, 'N_pos(k){k})) / product(1, n, 'N_pos(k){k})
```

## 17. `imo_1964_p2`

```yaml
id: "imo_1964_p2"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall a, b, c R:
            0 < a
            0 < b
            0 < c
            c < a + b
            b < a + c
            a < b + c
            =>:
                a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) <= 3 * a * b * c
    have u R = b + c - a
    have v R = a + c - b
    have w R = a + b - c
    b + c - a > 0
    a + c - b > 0
    a + b - c > 0
    0 < u
    0 < v
    0 < w
    v + w = (a + c - b) + (a + b - c) = 2 * a
    u + w = (b + c - a) + (a + b - c) = 2 * b
    u + v = (b + c - a) + (a + c - b) = 2 * c
    a = (v + w) / 2
    b = (u + w) / 2
    c = (u + v) / 2
    a^2 = ((v + w) / 2)^2
    b^2 = ((u + w) / 2)^2
    c^2 = ((u + v) / 2)^2
    a * b * c = ((v + w) / 2) * ((u + w) / 2) * ((u + v) / 2)
    3 * a * b * c = 3 * ((v + w) / 2) * ((u + w) / 2) * ((u + v) / 2)
    a^2 * u + b^2 * v + c^2 * w = ((v + w) / 2)^2 * u + ((u + w) / 2)^2 * v + ((u + v) / 2)^2 * w
    3 * a * b * c - (a^2 * u + b^2 * v + c^2 * w) = 3 * ((v + w) / 2) * ((u + w) / 2) * ((u + v) / 2) - (((v + w) / 2)^2 * u + ((u + w) / 2)^2 * v + ((u + v) / 2)^2 * w)
    3 * ((v + w) / 2) * ((u + w) / 2) * ((u + v) / 2) - (((v + w) / 2)^2 * u + ((u + w) / 2)^2 * v + ((u + v) / 2)^2 * w) = (u * (v - w)^2 + v * (w - u)^2 + w * (u - v)^2) / 8
    3 * a * b * c - (a^2 * u + b^2 * v + c^2 * w) = (u * (v - w)^2 + v * (w - u)^2 + w * (u - v)^2) / 8
    0 <= (v - w)^2
    0 <= (w - u)^2
    0 <= (u - v)^2
    0 <= u * (v - w)^2
    0 <= v * (w - u)^2
    0 <= w * (u - v)^2
    0 <= u * (v - w)^2 + v * (w - u)^2
    0 <= u * (v - w)^2 + v * (w - u)^2 + w * (u - v)^2
    0 <= (u * (v - w)^2 + v * (w - u)^2 + w * (u - v)^2) / 8
    0 <= 3 * a * b * c - (a^2 * u + b^2 * v + c^2 * w)
    a^2 * u + b^2 * v + c^2 * w <= 3 * a * b * c
    c + a - b = a + c - b
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) = a^2 * u + b^2 * v + c^2 * w
    a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) <= 3 * a * b * c
```

## 18. `induction_prod1p1onk3le3m1onn`

```yaml
id: "induction_prod1p1onk3le3m1onn"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall n N_pos:
            product(1, n, '(k N_pos) R {1 + 1 / k^3}) <= 3 - 1 / n

    by induc n from 1:
        prove:
            product(1, n, '(k N_pos) R {1 + 1 / k^3}) <= 3 - 1 / n

        prove from n = 1:
            product(1, 1, '(k N_pos) R {1 + 1 / k^3}) = 1 + 1 / 1^3 = 2
            3 - 1 / 1 = 2
            product(1, 1, '(k N_pos) R {1 + 1 / k^3}) <= 3 - 1 / 1

        prove induc:
            product(1, n + 1, '(k N_pos) R {1 + 1 / k^3}) = product(1, n, '(k N_pos) R {1 + 1 / k^3}) * '(k N_pos) R {1 + 1 / k^3}(n + 1)
            '(k N_pos) R {1 + 1 / k^3}(n + 1) = 1 + 1 / (n + 1)^3
            product(1, n + 1, '(k N_pos) R {1 + 1 / k^3}) = product(1, n, '(k N_pos) R {1 + 1 / k^3}) * (1 + 1 / (n + 1)^3)
            0 < 1 + 1 / (n + 1)^3
            product(1, n, '(k N_pos) R {1 + 1 / k^3}) * (1 + 1 / (n + 1)^3) <= (3 - 1 / n) * (1 + 1 / (n + 1)^3)
            0 <= (n - 1)^2
            0 <= n + 1
            0 <= (n - 1)^2 + (n + 1)
            n^2 - n + 2 = (n - 1)^2 + (n + 1)
            0 <= n^2 - n + 2
            0 < n * (n + 1)^3
            0 <= (n^2 - n + 2) / (n * (n + 1)^3)
            3 - 1 / (n + 1) - (3 - 1 / n) * (1 + 1 / (n + 1)^3) = (n^2 - n + 2) / (n * (n + 1)^3)
            0 <= 3 - 1 / (n + 1) - (3 - 1 / n) * (1 + 1 / (n + 1)^3)
            (3 - 1 / n) * (1 + 1 / (n + 1)^3) <= 3 - 1 / (n + 1)
            product(1, n + 1, '(k N_pos) R {1 + 1 / k^3}) <= (3 - 1 / n) * (1 + 1 / (n + 1)^3) <= 3 - 1 / (n + 1)
```

## 19. `induction_sumkexp3eqsumksq`

```yaml
id: "induction_sumkexp3eqsumksq"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall n N_pos:
            sum(0, n - 1, 'R(k){k}) = n * (n - 1) / 2

    by induc n from 1:
        prove:
            sum(0, n - 1, 'R(k){k}) = n * (n - 1) / 2

        prove from n = 1:
            sum(0, 0, 'R(k){k}) = 0
            sum(0, 1 - 1, 'R(k){k}) = sum(0, 0, 'R(k){k}) = 0 = 1 * (1 - 1) / 2

        prove induc:
            sum(0, n, 'R(k){k}) = sum(0, n - 1, 'R(k){k}) + 'R(k){k}(n)
            'R(k){k}(n) = n
            sum(0, n + 1 - 1, 'R(k){k}) = sum(0, n, 'R(k){k}) = sum(0, n - 1, 'R(k){k}) + n = n * (n - 1) / 2 + n = (n + 1) * ((n + 1) - 1) / 2

claim:
    prove:
        forall n N_pos:
            sum(0, n - 1, 'R(k){k^3}) = sum(0, n - 1, 'R(k){k})^2

    by induc n from 1:
        prove:
            sum(0, n - 1, 'R(k){k^3}) = sum(0, n - 1, 'R(k){k})^2

        prove from n = 1:
            sum(0, 0, 'R(k){k^3}) = 0
            sum(0, 0, 'R(k){k}) = 0
            sum(0, 1 - 1, 'R(k){k^3}) = sum(0, 0, 'R(k){k^3}) = 0 = 0^2 = sum(0, 0, 'R(k){k})^2 = sum(0, 1 - 1, 'R(k){k})^2

        prove induc:
            sum(0, n, 'R(k){k^3}) = sum(0, n - 1, 'R(k){k^3}) + 'R(k){k^3}(n)
            'R(k){k^3}(n) = n^3
            sum(0, n, 'R(k){k}) = sum(0, n - 1, 'R(k){k}) + 'R(k){k}(n)
            'R(k){k}(n) = n
            sum(0, n - 1, 'R(k){k}) = n * (n - 1) / 2
            sum(0, n, 'R(k){k}) = sum(0, n - 1, 'R(k){k}) + n = n * (n - 1) / 2 + n = (n + 1) * n / 2
            sum(0, n + 1 - 1, 'R(k){k^3}) = sum(0, n, 'R(k){k^3}) = sum(0, n - 1, 'R(k){k^3}) + n^3 = sum(0, n - 1, 'R(k){k})^2 + n^3 = (n * (n - 1) / 2)^2 + n^3 = ((n + 1) * n / 2)^2 = sum(0, n, 'R(k){k})^2 = sum(0, n + 1 - 1, 'R(k){k})^2
```

## 20. `numbertheory_x5neqy2p4`

```yaml
id: "numbertheory_x5neqy2p4"
source: "miniF2F"
topic: "contest theorem proving"
difficulty: "mixed"
natural_language_idea: "Finished miniF2F derivation selected for its explicit algebra, number-theory, induction, or contest-problem proof shape."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Representative checked example for this gallery."
```

```litex
claim:
    prove:
        forall x Z:
            x^5 % 11 = 0 or x^5 % 11 = 1 or x^5 % 11 = 10
    by cases:
        prove:
            x^5 % 11 = 0 or x^5 % 11 = 1 or x^5 % 11 = 10
        case x % 11 = 0:
            x^5 % 11 = ((x % 11)^5) % 11 = 0^5 % 11 = 0
        case x % 11 = 1:
            x^5 % 11 = ((x % 11)^5) % 11 = 1^5 % 11 = 1
        case x % 11 = 2:
            x^5 % 11 = ((x % 11)^5) % 11 = 2^5 % 11 = 10
        case x % 11 = 3:
            x^5 % 11 = ((x % 11)^5) % 11 = 3^5 % 11 = 1
        case x % 11 = 4:
            x^5 % 11 = ((x % 11)^5) % 11 = 4^5 % 11 = 1
        case x % 11 = 5:
            x^5 % 11 = ((x % 11)^5) % 11 = 5^5 % 11 = 1
        case x % 11 = 6:
            x^5 % 11 = ((x % 11)^5) % 11 = 6^5 % 11 = 10
        case x % 11 = 7:
            x^5 % 11 = ((x % 11)^5) % 11 = 7^5 % 11 = 10
        case x % 11 = 8:
            x^5 % 11 = ((x % 11)^5) % 11 = 8^5 % 11 = 10
        case x % 11 = 9:
            x^5 % 11 = ((x % 11)^5) % 11 = 9^5 % 11 = 1
        case x % 11 = 10:
            x^5 % 11 = ((x % 11)^5) % 11 = 10^5 % 11 = 10

claim:
    prove:
        forall y Z:
            (y^2 + 4) % 11 = 2 or (y^2 + 4) % 11 = 4 or (y^2 + 4) % 11 = 5 or (y^2 + 4) % 11 = 7 or (y^2 + 4) % 11 = 8 or (y^2 + 4) % 11 = 9
    by cases:
        prove:
            (y^2 + 4) % 11 = 2 or (y^2 + 4) % 11 = 4 or (y^2 + 4) % 11 = 5 or (y^2 + 4) % 11 = 7 or (y^2 + 4) % 11 = 8 or (y^2 + 4) % 11 = 9
        case y % 11 = 0:
            y^2 % 11 = ((y % 11)^2) % 11 = 0^2 % 11 = 0
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (0 + 4) % 11 = 4
        case y % 11 = 1:
            y^2 % 11 = ((y % 11)^2) % 11 = 1^2 % 11 = 1
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (1 + 4) % 11 = 5
        case y % 11 = 2:
            y^2 % 11 = ((y % 11)^2) % 11 = 2^2 % 11 = 4
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (4 + 4) % 11 = 8
        case y % 11 = 3:
            y^2 % 11 = ((y % 11)^2) % 11 = 3^2 % 11 = 9
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (9 + 4) % 11 = 2
        case y % 11 = 4:
            y^2 % 11 = ((y % 11)^2) % 11 = 4^2 % 11 = 5
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (5 + 4) % 11 = 9
        case y % 11 = 5:
            y^2 % 11 = ((y % 11)^2) % 11 = 5^2 % 11 = 3
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (3 + 4) % 11 = 7
        case y % 11 = 6:
            y^2 % 11 = ((y % 11)^2) % 11 = 6^2 % 11 = 3
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (3 + 4) % 11 = 7
        case y % 11 = 7:
            y^2 % 11 = ((y % 11)^2) % 11 = 7^2 % 11 = 5
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (5 + 4) % 11 = 9
        case y % 11 = 8:
            y^2 % 11 = ((y % 11)^2) % 11 = 8^2 % 11 = 9
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (9 + 4) % 11 = 2
        case y % 11 = 9:
            y^2 % 11 = ((y % 11)^2) % 11 = 9^2 % 11 = 4
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (4 + 4) % 11 = 8
        case y % 11 = 10:
            y^2 % 11 = ((y % 11)^2) % 11 = 10^2 % 11 = 1
            (y^2 + 4) % 11 = ((y^2 % 11) + (4 % 11)) % 11 = (1 + 4) % 11 = 5

claim:
    prove:
        forall x, y Z:
            x^5 != y^2 + 4
    by contra:
        prove:
            x^5 != y^2 + 4
        x^5 = y^2 + 4
        x^5 % 11 = (y^2 + 4) % 11
        by cases:
            prove:
                x^5 % 11 != (y^2 + 4) % 11
            case x^5 % 11 = 0:
                by cases:
                    prove:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 2:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 4:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 5:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 7:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 8:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 9:
                        x^5 % 11 != (y^2 + 4) % 11
            case x^5 % 11 = 1:
                by cases:
                    prove:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 2:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 4:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 5:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 7:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 8:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 9:
                        x^5 % 11 != (y^2 + 4) % 11
            case x^5 % 11 = 10:
                by cases:
                    prove:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 2:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 4:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 5:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 7:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 8:
                        x^5 % 11 != (y^2 + 4) % 11
                    case (y^2 + 4) % 11 = 9:
                        x^5 % 11 != (y^2 + 4) % 11
        impossible x^5 % 11 = (y^2 + 4) % 11
```
