# Builtin predicates

**Builtin predicates** are the fixed relation and `$…` predicate names that Litex treats as special atomic facts—equality and comparisons need **no** leading `$`; most others use **`$`** and either **infix** (two arguments) or **prefix** `$name(…)`.

User-defined facts like `$my_prop(…)` from `prop` / `abstract_prop` are **not** builtins: the checker resolves them from **your** definitions, not from the fixed list below.

Negation, when allowed, is written with **`not`** in front of the same atomic spelling (for example `not 0 $in {1}`). The two function-equality builtins **`$fn_eq`** and **`$fn_eq_in`** do **not** support `not` in the checker.

---

## Equality and numeric order (no `$`)

| Meaning | Example |
|--------|---------|
| Equality | `1 = 1` |
| Inequality | `1 != 0` |
| Less than | `0 < 1` |
| Greater than | `2 > 1` |
| Less or equal | `1 <= 2` |
| Greater or equal | `3 >= 2` |
| Negated equality | `not 1 = 2` |
| Negated strict inequality | `not 0 < -1` |
| Negated `<=` / `>=` | `not 2 <= 1`, `not 1 >= 3` |

---

## Membership **`$in`** (two arguments; usually infix)

| Meaning | Example |
|--------|---------|
| Element of a set | `1 $in {1, 2}` |
| Membership in a typed domain (when valid in context) | `0.5 $in Q` |
| Not in | `not 0 $in {1, 2}` |

---

## Set “sort” predicates (one argument, prefix **`$is_…(…)`**)

| Predicate | Meaning | Example |
|-----------|---------|---------|
| **`$is_set`** | The value is a set | `$is_set({1, 2})` |
| **`$is_nonempty_set`** | The set has at least one element | `$is_nonempty_set({1})` |
| **`$is_finite_set`** | The set is finite | `$is_finite_set({1, 2})` |
| **`not $is_set`** | … is not a set | *(when context supplies a non-set-like object)* |
| **`not $is_nonempty_set`** | Empty or not nonempty | `not $is_nonempty_set({})` |
| **`not $is_finite_set`** | Not finite | *(in proofs where the checker can refute finiteness)* |

---

## Cartesian product and tuple shape (one argument)

| Predicate | Meaning | Example |
|-----------|---------|---------|
| **`$is_cart`** | Object is a Cartesian-product set (built with `cart`) | `have c set = cart(R, Q)`<br>`$is_cart(c)` |
| **`$is_tuple`** | Object is an n-tuple value | `have u set = (1, 2)`<br>`$is_tuple(u)` |
| **`not $is_cart`**, **`not $is_tuple`** | Deny those shapes | *(same pattern as other `not $…` facts)* |

---

## Subset and superset (infix **`$subset`**, **`$superset`**)

| Meaning | Example |
|--------|---------|
| Subset | `let a, b set:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`a $subset b` |
| Superset | `b $superset a` means `a $subset b` |
| Not a subset | `let a, b set:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`not a $subset b` |
| Not a superset | `not b $superset a` |

---

## Function restriction **`$restrict_fn_in`** (two arguments)

Means: the first callable **can be restricted** to the arity / domain pattern of the second (a `fn(…) …` “target signature” object).

```litex
have f fn(x R, y Q) R

$restrict_fn_in(f, fn(a Q, b Q) R)
```

Negation: `not f $restrict_fn_in(target)` when you refute restrictability.

---

## Function equality **`$fn_eq`** and **`$fn_eq_in`**

| Predicate | Meaning | Example |
|-----------|---------|---------|
| **`$fn_eq(f, g)`** | `f` and `g` are the same function (typing + pointwise equality on the shared domain) | `have fn f(x R) R = x`<br>`have fn g(x R) R = x`<br>`forall x R:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`f(x) = x = g(x)`<br>`$fn_eq(f, g)` |
| | | `$fn_eq('R(x){x}, 'R(y){y})` |
| **`$fn_eq_in(f, g, S)`** | `f` and `g` agree **on every point of set `S`** | `have fn f(x R) R = x`<br>`have fn g(x R) R = x`<br>`forall x R:`<br>&nbsp;&nbsp;&nbsp;&nbsp;`f(x) = x = g(x)`<br>`$fn_eq_in(f, g, R)` |
| | | `$fn_eq_in('R(x){x}, 'R(y){y}, R)` |

Neither accepts `not` in the builtin builder; to state inequality, use other facts (for example disprove pointwise equality on some input).

---

## Other `$…` atoms: **not** builtins

Any other **`$name(…)`** (including `not $name(…)`) that you declare with `prop` or `abstract_prop` is **not** a builtin; the checker uses **your** definition to validate it.

```litex
prove:
    abstract_prop ok(x)
    know $ok(0)
    $ok(0)
```

```litex
prove:
    abstract_prop bad(x)
    know not $bad(1)
    not $bad(1)
```
