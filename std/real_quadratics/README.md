# Real quadratic equations

This source module constructs and classifies the entire real solution set of
a*x^2+b*x+c=0. It contains five functions and 23 checked source theorems,
including all linear and constant cases, repeated/distinct roots, Vieta and
its converse, factorization, root order and attained vertex extrema. There
are no user axioms, trusts, native changes or general polynomial datatype.

## Import and use

```ini
[import std]
quad = real_quadratics
```

The following imported excerpt was checked before the requested test cleanup:

```litex
release obj def quad::main::quadratic_solutions

release thm quad::main::quadratic_solution_set_from_vieta(1,-3,2,1,2)

quad::main::quadratic_solutions(1,-3,2)=union({1},{2})

release thm quad::main::linear_solution_set(2,1)

quad::main::quadratic_solutions(0,2,1)={-1/2}

release obj def quad::main::quadratic_discriminant

quad::main::quadratic_discriminant(1,2,1)=0

release thm quad::main::quadratic_repeated_solution_set(1,2,1)

quad::main::quadratic_solutions(1,2,1)={-1}

```

These conclusions specify every real root, rather than checking a supplied
candidate alone. The union of singleton roots stays legal for repeated roots;
the two-element literal set requires distinct displayed elements in Litex.

## Functions and domains

| Function | Fixed mathematical contract |
| --- | --- |
| `quadratic_value(a,b,c,x)` | All four inputs real; returns a*x^2+b*x+c. The leading coefficient may be zero. |
| `quadratic_discriminant(a,b,c)` | All coefficients real; returns b^2-4*a*c with no sign restriction. |
| `quadratic_solutions(a,b,c)` | All coefficients real; returns the actual subset of R where the value is zero. For a=b=c=0 it is R. |
| `quadratic_root_minus(a,b,c)` | Requires a!=0 and discriminant>=0; returns ((-b-sqrt(discriminant))/a)/2. |
| `quadratic_root_plus(a,b,c)` | The same domain; returns ((-b+sqrt(discriminant))/a)/2. |

Release each imported function's object definition before applying it. The
formula-minus value is smaller for positive a and larger for negative a;
ordering theorems retain these sign hypotheses. The formula values coincide
when the discriminant is zero. They are not complex-root or ordered-root
selectors, and their denominator association preserves the usual 2*a formula.

## Theorem families

| Family | Implemented source results |
| --- | --- |
| Completing the square | Square identity, both root/square implications and the completed-square value formula. The converse requires a!=0. |
| Real roots | Both formula values solve the equation; every root is one of them; the actual solution set is their singleton union. Negative discriminant gives the empty set, zero gives one singleton, positive gives distinct exhaustive witnesses. |
| Degenerate coefficients | Linear equation with nonzero slope, nonzero constant with no solution, and the zero polynomial with all of R as solutions. |
| Vieta and factorization | Sum, product and difference of the formula values; factorization; converse sum/product data give factorization and the entire solution set. The converse allows coincident supplied roots. |
| Order and extrema | Sign-dependent order of distinct formula values; attained minimum for positive leading coefficient and maximum for negative leading coefficient. |

The imported contracts and applications exercised every
named theorem at its full domain. They classified (m-1)*x^2+2*x+1=0 for all real
m, including m=1 and m=2, and derive an attained fixed-sum product bound.
OpenStax examples 9.21 and 9.27 supply exact solution-set callers; example 9.24
is checked for its empty real solution set, with complex roots outside scope.

## Verification and scope

Before cleanup, the final gate passed 28 strict source statements, 65 strict imported
statements, the independent nine-statement excerpt and 16 final-only refusals
after a fresh Session replays all 65 positive statements.
The refusals cover zero leading coefficient, negative discriminant, complex
coefficients, repeated/distinct confusion, false order, missing sign/Vieta
premises and the infinite zero-polynomial solution set. No Cargo, Lean,
installer or local textbook gate is implied. At the user's pause request,
the round's validation directory, scripts, journals and pinned executable
were removed. These counts describe the completed historical checkpoint;
the removed imported and negative suites are no longer shipped here.
The retained source can be checked with:

```bash
LITEX_STD_PATH="$PWD/std" target/release/litex -strict -lang en -f std/real_quadratics/main.lit
```

[math_collections.md](math_collections.md) records sources, mathematical
objects, dependencies and boundaries. This module addresses the real
quadratic-equation specification S02.2. It does not establish a whole school
algebra course, polynomial-ring theory, complex roots or numerical stability.
