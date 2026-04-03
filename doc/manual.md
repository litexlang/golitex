# Manual

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex gives you a **lean, set-theoretic** idiom for mathematics—**just enough** structure to handle most day-to-day mathematical situations **without a long apprenticeship**. Each language feature is meant to **track a real mathematical concept**, not an ad hoc gadget. 

The emphasis is on **how ideas relate**: constructs are **woven together** so you can say what depends on what, in the same spirit as the mathematics itself, rather than as isolated syntax rules. 

**This manual** is a compact reference to **syntax and semantics** across Litex.

# Syntax Rules

# Proposition

Syntax:

prop 

Functionalities:

Explanation:

Examples:

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