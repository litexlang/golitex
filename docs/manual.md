# Manual

_Simplicity is the ultimate sophistication._

_– Leonardo da Vinci_

Litex gives you a **lean, set-theoretic** idiom for mathematics—**just enough** structure to handle most day-to-day mathematical situations **without a long apprenticeship**. Each language feature is meant to **track a real mathematical concept**, not an ad hoc gadget. 

The emphasis is on **how ideas relate**: constructs are **woven together** so you can say what depends on what, in the same spirit as the mathematics itself, rather than as isolated syntax rules. 

**This manual** is a compact reference to **syntax and semantics** across Litex.

# Abstract Proposition

Purpose:

Define a proposition symbol without giving it a body. Such a proposition has no built-in defining equivalence to unfold. Use it when you want to talk about a proposition abstractly without committing to its internal meaning.

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

Purpose:

Prove a target fact by splitting the proof into exhaustive cases and proving the target separately in each case.

Syntax:

```text
by cases:
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

**Shorthand:** `by cases => fact` `:` on one line (goal on the header); the body then starts with `case` arms and omits the inner `prove:` block.

1. fact1 or fact2 or ... or factn must be true.
2. under each case, proof_of_case_i must be a valid proof of fact i.

e.g.

```litex
have fn g(x R) R:
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

Purpose:

Prove a target fact indirectly by assuming its negation and deriving a contradiction.

Syntax:

```text
by contra:
    prove:
        fact
    proof
    ...
    impossible impossible_fact
```

**Shorthand:** `by contra => atomic_goal` `:` on one line; the body is the same but without the inner `prove:`.

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

# Header shorthand: `by … => <goal>:` and the same goal three ways

For **`by cases`**, **`by contra`**, and **`claim`**, you may put the goal on the **header line** after `=>` instead of opening with an inner `prove:` block. The proof body is otherwise the same: in the `by cases` form, the block starts directly with `case` arms after the header.

**Illustration:** the fact `1 = 1` is deliberately trivial; the point is that **one** outcome can be reached by **case split**, by **contradiction**, or by a **direct claim**—choose the shape that matches the mathematical story you are telling.

```litex
by cases => 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1

by contra => 1 = 1:
    impossible 1 != 1

claim => 1 = 1:
    do_nothing
```

The same minimal sketches appear at the end of `examples/by_cases.lit`, `examples/by_contra.lit`, and `examples/claim.lit`.

# witness exist … from …

Purpose:

Prove an existential statement by explicitly giving witnesses and then verifying that they satisfy the required conditions.

Syntax:

```text
witness exist <params_and_types> st { … } from <obj> [, <obj> ]…:
    <proof statements>
```

1. `exist … st { … }` has the same shape as an `exist` fact (parameters, optional type constraints, facts in braces).
2. After `from`, give one object per bound parameter, in order; they must make the `st { … }` facts true.
3. The indented block is the proof obligation (e.g. inequalities, membership).

e.g.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist x, y R st {x > y}
```

# witness nonempty set

Purpose:

Prove that a set is nonempty by exhibiting a concrete element of that set.

Syntax:

```text
witness $is_nonempty_set( <set> ) from <obj>:
    <proof statements>
```

1. `<obj>` should lie in `<set>` (typically proved in the block, e.g. `know obj $in set`).
2. After verification, `$is_nonempty_set(<set>)` may be used.

e.g.

```litex
have s set

witness $is_nonempty_set(s) from 1:
    know 1 $in s

$is_nonempty_set(s)
```

# by enumerate

Purpose:

Prove facts by checking all cases for parameters ranging over **finite list sets** (`{ … }`).

Syntax:

```text
by enumerate <param> <list_set> [, <param> <list_set> ]…:
    prove:
        <facts to prove (exist / or / chain atomic facts)>
    <optional further proof statements>
```

1. Each parameter is constrained to the given list set.
2. The `prove:` block lists what must hold for all those combinations (corresponds to a `forall` over those list sets).
3. Extra statements after `prove:` complete the proof.

e.g.

```litex
by enumerate finite_set:
    prove:
        forall a {1, 2, 3}:
            a < 4
```

# by induc

Purpose:

Prove facts by induction on an integer parameter starting from a given lower bound.

Syntax:

```text
by induc <param> from <obj>:
    <facts to prove (exist / or / chain atomic facts), one block each>
```

1. `<param>` is the induction variable; `<obj>` is the start (e.g. `0`).
2. Each body block under the header is part of what the induction establishes (base + step are verified according to the kernel rules).
3. Requires a supporting `forall`‑style hypothesis in context when used in full proofs.

e.g.

```litex
abstract_prop p(a)

know:
    $p(0)
    forall n Z:
        n >= 0
        $p(n)
        =>:
            $p(n + 1)

by induc n from 0:
    prove:
        $p(n)

forall n Z:
    n >= 0
    =>:
        $p(n)
```

# by for

Purpose:

Prove facts uniformly for parameters ranging over **`range(…)`** or **`closed_range(…)`**, using a single **`forall`** fact that carries the bounds and (optionally) domain / `=>:` conclusions.

Syntax:

```text
by for:
    prove:
        forall <param_groups with range or closed_range>:
            [ domain facts … ]
            =>:
                <then facts …>
    <proof statements>
```

1. After `for` comes only `:` (no parameter list in the header).
2. The first body block must be `prove:` containing **exactly one** `forall` fact. Every parameter type in that `forall` must be `range(…)` or `closed_range(…)` (possibly comma-grouped, e.g. `i, j closed_range(0, 3)`).
3. The executor enumerates integer values in those ranges, assumes domain facts when they verify, runs `<proof statements>`, then checks each `then` fact. `forall` with `<=>:` is not allowed here.
4. See `examples/for.lit` and `examples/tmp.lit`.

e.g.

```litex
by for:
    prove:
        forall n range(0, 10):
            n < 10
    do_nothing

by for:
    prove:
        forall n closed_range(0, 10):
            n <= 10
    do_nothing
```

# Parameter type `restrictive (fn …)`

In a parameter list (e.g. `forall`, `have`, `let`), **`restrictive (`** … **`)`** takes one **`fn …`** value (same shape as the second argument of **`$restrict_fn_in`**). Binding a name with this type **stores** **`$restrict_fn_in(name, fn …)`** (and inference records the narrowed signature for well-defined checks). It does **not** assert **`name $in fn …`** membership; use a normal **`fn …`** parameter type when you want membership.

Example:

```litex
forall f restrictive (fn (x R, y Q) R):
    f(1, 2) = f(1, 2)
```

# by extension

Purpose:

Prove **set equality** by **extensionality**: show that each side is a subset of the other.

Syntax:

```text
by extension:
    prove:
        <left> = <right>
    <proof statements>
```

1. The `prove:` block must contain a single **equality** atomic fact between two sets (or set‑denoting objects).
2. The following statements prove subset both ways (whatever the verifier expects for the proof body).

e.g.

```litex
by extension:
    prove:
        {1, 2} = {2, 1}
    by enumerate finite_set:
        prove:
            forall x {1, 2}:
                x $in {2, 1}
    by enumerate finite_set:
        prove:
            forall y {2, 1}:
                y $in {1, 2}

{1, 2} = {2, 1}
```