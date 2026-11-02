# Gaps in the rational numbers

This module proves the two square-root-of-two gap results of Tao,
*Analysis I*, 4.4.4-4.4.5. It uses native `Q` and introduces no alternate
quotient model, rational arithmetic operation or square-root selector.

```ini
[import std]
Rational = rational_numbers
[alias]
rat = Rational::main
[export]
main = "./main.lit"
```

| Theorem | Contract |
| --- | --- |
| `rat::rational_square_not_two(x)` | Every rational `x` satisfies `x^2!=2`, with no sign assumption. |
| `rat::rational_square_two_straddle(epsilon)` | For every positive real radius, there is rational `q>=0` with `q^2<2<(q+epsilon)^2`. Positive rational radii specialize the source theorem. |

## Example

With the configuration above, the following complete caller requests the
general witness and checks the source's concrete approximation:

```litex
release thm rat::rational_square_two_straddle(1/1000)
exist x Q st {0 <= x,x^2 < 2,2 < (x+1/1000)^2}
0 <= 1414/1000
(1414/1000)^2 = 1999396/1000000 < 2
((1414/1000)+(1/1000))^2 = (1415/1000)^2 = 2002225/1000000 > 2
```

The irrationality proof uses the existing unique reduced fraction, primality
of two and prime-divisor laws. The approximation proof uses native real
`sqrt(2)` and rational density, splitting at the radius `sqrt(2)`. This is an
explicit reuse of native real foundations under the selected number-system
scope; it is not a construction of the real numbers from rationals in the
source's foundational order. Neither theorem assumes the desired gap or an
unproved approximation principle. Drafts and acceptance evidence stay under
`experiments/`.
