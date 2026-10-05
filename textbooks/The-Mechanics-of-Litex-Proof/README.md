# The Mechanics of Litex Proof

This book is a Litex version of Heather Macbeth's
[The Mechanics of Proof](https://hrmacbeth.github.io/math2001/), a textbook on
mathematical proof using Lean. Its chapters are designed around the original
book's mathematical topics and proof patterns, with corresponding arguments
written in Litex.

The aim is to help readers compare how the same mathematical reasoning is
expressed in Lean and Litex. The Litex examples develop proofs through
mathematical facts, definitions, calculations, witnesses and previously proved
results. Reading them alongside the original Lean examples makes differences
in notation, proof structure and interaction with the checker visible through
concrete mathematics.

The book begins with calculation and structured proofs, then develops logic,
induction, number theory, functions, sets and relations.

Maintained by Jiachen Shen.

## What this book demonstrates

The examples progress from calculations to definitions and constructions, then
to proofs about functions, sets and relations. These three excerpts show how
that progression is expressed in Litex.

### State mathematical facts

In [Chapter 1](chapter01-proofs-by-calculation.lit), an assumption and its
consequence can be written directly:

```litex
forall x R:
    x = 2
    =>:
        x + 1 = 3
```

This states that every real number `x` satisfying `x = 2` also satisfies
`x + 1 = 3`. Litex checks the consequence using the assumption and arithmetic.
Longer examples build arguments through intermediate facts and calculations.

### Define concepts and give witnesses

[Chapter 3](chapter03-parity-and-divisibility.lit) defines odd integers through
an existential statement, then proves that 7 is odd by supplying a witness:

```litex
prop odd(a Z):
    exist t Z st {a = 2 * t + 1}

witness $odd(7) from 3
```

The definition requires an integer `t` with `a = 2 * t + 1`. The witness `3`
lets Litex check `7 = 2 * 3 + 1`. Later proofs use `obtain` to extract witnesses
from established existential facts and reason with their defining properties.

### Construct mathematical objects

[Chapter 8](chapter08-functions.lit) introduces functions with their parameter
domains and conditions included in the declaration:

```litex
have fn f_intro(x R: x > 1) R = x + 1
f_intro(2) = 3
```

Here the input is a real number greater than 1, and the output is real. The
application uses `2`, which satisfies the input condition. The chapter also
develops functions passed as arguments, definitions by cases, constructions
from unique existence, composition and inverse functions.

### Objects and proof tools across the chapters

Numbers, sets, functions and tuples are mathematical objects. Equalities,
membership statements and quantified properties are facts about those objects.
Definitions and proof commands let readers construct objects, establish facts
and reuse proved results.

| Area | Examples in the book | Chapters |
| --- | --- | --- |
| Numbers and expressions | `N`, `Z`, `Q`, `R`; arithmetic, powers, absolute values, `quot`, remainders, `gcd` and factorials | 1, 3, 6, 7 |
| Sets | Finite sets, set builders, intervals, power sets, unions, intersections and set differences | 9 |
| Functions | Functions as values and arguments, domain conditions, composition and inverse functions | 8 |
| Tuples and Cartesian products | Pairs, component access and functions taking or returning pairs | 8 |
| Definitions and logic | `prop`, `forall`, `exist`, `exist!`, equality, membership and logical connectives | 2–5 |
| Proof structure and reuse | `claim`, `thm`, `release thm`, `witness`, `obtain`, case analysis and contradiction | 2–6 |
| Induction and construction | Ordinary and strong induction, recursive definitions and function construction from unique existence | 6, 8 |
| Set and relation proofs | Finite enumeration, extensionality, and proving and registering reflexive, symmetric and transitive laws | 9, 10 |

## Contents

| Chapter | Topic |
| --- | --- |
| 0 | Introduction |
| 1 | Proofs by calculation |
| 2 | Structured proofs |
| 3 | Parity and divisibility |
| 4 | Further structured proofs |
| 5 | Logic |
| 6 | Induction |
| 7 | Number theory |
| 8 | Functions |
| 9 | Sets |
| 10 | Relations |
