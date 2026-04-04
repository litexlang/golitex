# Manual

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex gives you a **lean, set-theoretic** idiom for mathematics—**just enough** structure to handle most day-to-day mathematical situations **without a long apprenticeship**. Each language feature is meant to **track a real mathematical concept**, not an ad hoc gadget. 

The emphasis is on **how ideas relate**: constructs are **woven together** so you can say what depends on what, in the same spirit as the mathematics itself, rather than as isolated syntax rules. 

**This manual** is a compact reference to **syntax and semantics** across Litex.

# Abstract Proposition

Syntax:

```text
abstract_prop <proposition_name> ( [ <parameter> [, <parameter> ]… ] )
```

- `<proposition_name>`: one **string** token (the name of the proposition).
- Inside the parentheses: **zero or more** `<parameter>` tokens, each a **string**, separated **only by commas** `,` (whitespace around commas is optional).  

## Examples:

```litex
abstract_prop r()
abstract_prop p(x)
abstract_prop q(x, y, z)
```

# by cases

Syntax:

```text
by_cases:
    prove:
        fact
    case fact1:
        proof_of_case_1
    case fact2:
        proof_of_case_2
    ...
    case factn:
        proof_of_case_n
```

1. fact1 or fact2 or ... or factn must be true.
2. under each case, proof_of_case_i must be a valid proof of facti.

e.g.

```litex
have fn g(x R) R =:
    case x = 2: 3
    case x != 2: 4

have x R

x = 2 or x != 2

by cases:
    prove:
        g(x) > 2
    case x = 2:
        g(x) = 3
        g(x) > 2
    case x != 2:
        g(x) = 4
        g(x) > 2
```

# by contra

Syntax:

```text
by contra:
    prove:
        fact
    proof
    ...
    impossible impossible_fact
```

1. The goal is to prove `fact`. In the body, `fact` is handled as if its negation were true; you then derive a contradiction: the fact after `impossible` must be both true and false at once.
2. `impossible_fact` must be false and true at the same time.

e.g.

```litex
abstract_prop p(x, y)
abstract_prop q(x, y)

know forall a, b R:
    $p(a, b)
    =>:
        $q(a, b)

know not $q(1, 2)

by contra:
    prove:
        not $p(1, 2)
    $p(1, 2)
    impossible $q(1,2 )
```