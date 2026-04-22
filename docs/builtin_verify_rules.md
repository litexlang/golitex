# Builtin verification (what each rule actually does)

The kernel still loads Lit from `src/builtin_code/`. This file explains **behavior**: after the verifier matches a **pattern**, what **sub-goals** it tries and whether it recurses into the same pipeline.

If anything here disagrees with Rust, the code wins.

---

## Shared: normalizing order (`order_normalize.rs`)

Many order builtins only care about **`<`** and **`<=`**. First, `normalize_positive_order_atomic_fact` rewrites:

- `a > b` → `b < a`; `a >= b` → `b <= a`
- `not a < b` → `b <= a`; `not a <= b` → `b < a`
- `not a > b` → `a <= b`; `not a >= b` → `a < b`

So your surface goal might be `a <= b`, but internally an earlier step may have flipped sides.

---

## Shared: order sub-goals (`order_algebra_builtin.rs`, `verify_order_subgoal`)

When algebra rules need a smaller order fact, they call `verify_order_subgoal`:

1. `verify_non_equational_atomic_fact_with_known_atomic_facts` (only what is already **known** as atomic facts).
2. If that is not `true`, `verify_order_atomic_fact_numeric_builtin_only` (**full order builtin pipeline** again on the sub-goal).

So sub-goals can chain: known facts → numeric/builtin cone → algebra again, etc.

---

## Order pipeline: `verify_order_atomic_fact_numeric_builtin_only` (`number_compare.rs`)

**Every** order-related `AtomicFact` dispatched from `non_equational_dispatch.rs` enters here. Steps run **in order**; the **first** step that returns a definite success stops the chain. If none apply, the code may still fall through to reflexivity / numeric comparison at the end of the function.

### Step A — `verify_order_from_known_negated_complement`

**Idea:** total-order duality from a **known negated** fact.

- Goal `a > b` → look for known `not (a <= b)` (stored as `NotLessEqualFact`).
- Goal `a < b` → look for known `not (a >= b)`.
- Goal `a >= b` → look for known `not (a < b)`.
- Goal `a <= b` → look for known `not (a > b)`.

**Mechanism:** only consults **known atomic facts** for that negated form (no full builtin recursion for the negated fact in this step). If found, the original order goal succeeds with reason `order_from_known_negated_complement`.

### Step B — `verify_negated_order_from_known_equivalent_order`

**For goals** `not a < b`, `not a > b`, `not a <= b`, `not a >= b`:

Builds **two** candidate strict/weak facts equivalent on a total line (e.g. `not a < b` tries `b <= a` and `a >= b`). Tries each against **known atomic facts** only. First match wins; reason `negated_order_from_known_equivalent_order`.

### Step C — `verify_order_algebra_structural_builtin_rule` (`order_algebra_builtin.rs`)

Normalizes the goal to `LessEqual` or `Less`, then runs **`try_less_equal_algebra`** or **`try_less_algebra`**. Each clause below **only** fires if the **AST shape** matches; then it proves **sub-goals** via `verify_order_subgoal`.

#### Weak order `a <= b` (`try_less_equal_algebra`)

| Pattern on `left <= right` | What you need to prove (sub-goals) | Builtin reason string (abbrev.) |
|----------------------------|-------------------------------------|----------------------------------|
| `right` is `a + b` and one addend is **syntactically** `left` | `0 <=` the **other** addend | `a <= a + b from 0 <= b` |
| `right` is `u + v` | `left <= u` **and** `0 <= v`, or the symmetric swap of addends (`left <= v` **and** `0 <= u`) | `a <= b + c from a <= b and 0 <= c` |
| `right` is `b * a` and **right factor** equals `left` | `0 <= left` **and** `1 <= b` (here `b` is the left factor of `*`) | `a <= b * a from 0 <= a and 1 <= b` |
| `left` and `right` are `k*u` and `k*v` with **same** left factor `k` | Either (`0 <= k` and `u <= v`) **or** (`k <= 0` and `v <= u`) | `k * a <= k * b from …` / `… from k <= 0 and b <= a` |
| Same with `*` and **same right factor** `k` | Same coefficient sign split on the **other** side | `a * k <= b * k from …` |
| Both sides are `+` | `left.left <= right.left` **and** `left.right <= right.right` | `a + c <= b + d from a <= b and c <= d` |
| Both sides are `-` | `left.left <= right.left` **and** `right.right <= left.right` (second compares **subtrahends** reversed) | `a - d <= b - c from a <= b and c <= d` |
| Both sides are `/` with **same denominator** | If `0 < denom`: `num_left <= num_right`; if `denom < 0`: **flip** numerators | `a / c <= b / c from 0 < c …` or `b / c <= a / c from c < 0 …` |

#### Strict order `a < b` (`try_less_algebra`)

Same **shapes** as weak, but sub-goals use `<` / `<=` where the implementation mixes strict and weak:

- `a < a + b` from `0 < b`.
- `a < b * a` from `0 < a` **and** `1 < b`.
- `k*a < k*b`: either (`0 < k` and `a < b`) or (`k < 0` and `b < a`); same idea for `a*k < b*k`.
- `a+c < b+d`: try **both** summands strict `<`; if that fails, try (`a < b` and `c <= d`) or (`a <= b` and `c < d`).
- Division: `a/c < b/c` from `0 < c` and `a < b`, or `b/c < a/c` from `c < 0` and `a < b`.

### Step D — `verify_zero_le_abs_builtin_rule`

After normalize: must be **`0 <= abs(x)`**. **No sub-goals**; always succeeds with reason `0 <= abs(x) for x in R`.

### Step E — `verify_zero_order_on_sub_from_two_sided_order_builtin_rule`

After normalize, goal is **`0 <= u - v`** or **`0 < u - v`**:

- Derives **`v <= u`** or **`v < u`** (swap minuend/subtrahend).
- Proves derived fact: **known atomic first**, then full **`verify_order_atomic_fact_numeric_builtin_only`** on the derived fact.
- Reasons: `0 <= u - v from v <= u` / `0 < u - v from v < u`.

### Step F — `0 <=` / `0 <` on **sums** (`verify_zero_le_add_*`, `verify_zero_lt_add_*`)

- **`0 <= a + b`:** requires **`0 <= a`** and **`0 <= b`** (each via `verify_zero_order_on_sub_expr`: known then builtin).
- **`0 < a + b`:** either (`0 < a` and `0 <= b`) or (`0 <= a` and `0 < b`) (implementation peels addition and combines branches).

### Step G — powers, products, quotients (same file, later helpers)

Rough behavior (see comments above `verify_order_atomic_fact_numeric_builtin_only`):

- **Even literal integer exponent:** `0 <= base^n`.
- **Integer exponent** with `0 <= base` (and `0 < base` if exponent negative): `0 <= base^n`.
- **`a * a`:** `0 <= a * a`.
- **`0 < base^exp`:** from `0 < base` and exponent **in R** (real exponent, positive base).
- **Products / quotients:** `0 <=` or `0 <` on `*` and `/` by splitting into operand sub-goals (denominator must be **strictly positive** for the non-flipped division rules).

### Step H — reflexivity

- **`a <= a`** or **`a >= a`** (syntactic same left/right string): builtin success with reasons like `less_equal_fact_equal` / `greater_equal_fact_equal`.

### Step I — numeric literals (`verify_number_comparison_builtin_rule`)

After normalize to `<` or `<=`:

1. Try to **evaluate** both sides to concrete `Number` strings; compare lexicographically as decimals (`number_compare` helpers).
2. If that fails, **`try_verify_numeric_order_via_div_elimination`** (clear denominators / division elimination path).

Success reason: `number comparison`.

---

## Dispatch overview (`non_equational_dispatch.rs`)

Short map (details live in the named modules):

| Fact kind | First builtin entry |
|-----------|---------------------|
| `NotEqualFact` | `not_equal_builtin.rs` |
| `InFact` / `NotInFact` | `in_fact_builtin.rs` (for **`$in R`**, finite **`sum(...)`** and **`product(...)`** are accepted like `+` / `*` arithmetic: no extra sub-goals; same reason as other real-closed surface forms). For **`f $in`** a **`fn …`** on the RHS, if the env already has **`f`** typed by a stored **`fn_set`** (`known_objs_in_fn_sets`), equality of signatures is first **`to_string`**, then if that fails (and flat param counts match) one draw of **`generate_random_unused_names`** supplies shared fresh names for both sides and **`to_string`** is compared again after alpha-rename. |
| `SubsetFact` / `SupersetFact` / negated | `set_relation_duality.rs` (and related) |
| All order atoms (`<`, `<=`, `>`, `>=`, `not …`) | **This order pipeline** |
| `IsSetFact` | Unconditional: `"Every object is a set."` |
| `IsNonemptySetFact` / `IsFiniteSetFact` / `IsCartFact` / `IsTupleFact` / `NotIsNonemptySetFact` | `type_predicates_builtin.rs` (shape-based: standard sets, nonempty list syntax, `cart` factors, `fn` return nonempty, etc.) |

```lit
know 0 <= abs(x)
know 1 + 1 < 3
```

---

## Equality: `verify_equality_by_builtin_rules` (`verify_equality_by_builtin_rules.rs`)

Runs **before** known equalities and before generic same-shape recursion (`verify_equality.rs`). Each line: **pattern** → **action**.

**Finite sum / product rules (5–9, 10–13):** corresponding bounds, bodies, peeled **`tail`** vs **`inst_obj`**, and **`end+1`** vs the next segment’s **`start`** are aligned with **`objs_equal_by_display_string`** (same object **`Display`** text), not **`verify_objs_are_equal`**.

1. **Family expansion** — One or both sides `family …(…)` with known `equal_to`: substitute parameters, **`verify_objs_are_equal`** on expanded sets; success strings like `equality: expand family definition…`.
2. **`0 = x - y`** — If one side is literal `0` and the other is `x - y`, requires **`x = y`** via full `verify_objs_are_equal`.
3. **`0 = a^n`** — Literal integer **`n > 0`**, requires **`a = 0`** (again full equality).
4. **Log** — `log(base, base^exp) = exp`; plus product/quotient/power algebra on `log`; **`log(a,b)=c`** from **`a^c = b`** (pow inverse).
5. **Finite sum (peel last index)** — Matches a **single** binary **`+`** on the other side: **`sum(i, a, e+1, F) = sum(i, a, e, F) + tail`** (either addend order). Same **`i`**, **`a`**, **`F`**; **`outer_end`** vs **`inner_end + 1`**; **`tail`** is **`inst_obj(F, { i ↦ outer_end }, Sum)`**. For **`tail`** that parses as several **`+`** (e.g. **`last + 1`**), parenthesize **`(last + 1)`** so the RHS is one **`+`** node. Reason: `equality: sum upper +1 = inner sum + term at new index`.
6. **Finite sum (additivity, same bounds)** — **`sum(i, a, b, F+G) = sum(i, a, b, F) + sum(i, a, b, G)`** (one **`+`** on the other side; the two inner sums may be swapped). Reason: `equality: sum(summand + summand) = sum + sum same bounds`.
7. **Finite sum (single index)** — If **`start`** and **`end`** match by **`objs_equal_by_display_string`**, then **`sum(i, a, b, F) = inst_obj(F, { i ↦ a }, Sum)`** (RHS must match the instantiated body the same way). Reason: `equality: sum with start = end is single instantiated summand`.
8. **Finite sum (split into two adjacent segments)** — **`sum(i, a, b, F) = sum(i, a, k, F) + sum(i, k+1, b, F)`** (order of the two sums around **`+`** either way). Same **`i`**, **`a`**, **`b`**, **`F`**; **`first_end + 1`** vs **`second_start`** by **`objs_equal_by_display_string`**. Reason: `equality: sum splits into adjacent segments (end+1 = next start)`.
9. **Finite sum (factor scalar)** — **`sum(i, a, b, k*F) = k * sum(i, a, b, F)`** (either **`*`** order in the sum body and on the other side). Same **`i`**, **`a`**, **`b`**, **`F`**, **`k`** by **`objs_equal_by_display_string`**; **`k`** must be well-defined and not use the outer sum index (lexical binding check). Reason: `equality: sum(k * summand) = k * sum(summand) with k well-defined and independent of sum index`.
10. **Finite product (peel last index)** — Matches a **single** binary **`*`** on the other side: **`product(i, a, e+1, F) = product(i, a, e, F) * tail`** (either factor order). Same **`i`**, **`a`**, **`F`**; **`outer_end`** vs **`inner_end + 1`**; **`tail`** is **`inst_obj(F, { i ↦ outer_end }, Product)`**. Reason: `equality: product upper +1 = inner product * factor at new index`.
11. **Finite product (multiplicativity, same bounds)** — **`product(i, a, b, F*G) = product(i, a, b, F) * product(i, a, b, G)`** (one **`*`** on the other side; the two inner products may be swapped). Reason: `equality: product(factor * factor) = product * product same bounds`.
12. **Finite product (single index)** — Same as sum single index: **`start`** / **`end`** and RHS vs **`inst_obj`** use **`objs_equal_by_display_string`**. Reason: `equality: product with start = end is single instantiated factor`.
13. **Finite product (split into two adjacent segments)** — **`product(i, a, b, F) = product(i, a, k, F) * product(i, k+1, b, F)`** (order of the two products around **`*`** either way). Same **`objs_equal_by_display_string`** checks as the sum split. Reason: `equality: product splits into adjacent segments (end+1 = next start)`.
14. **Same + calculation** — `verify_equality_by_they_are_the_same_and_calculation` (identity and partial evaluation).
15. **Rational simplification** — If still plausible, **`objs_equal_by_rational_expression_evaluation`** on evaluated pair; reason `calculation and rational expression simplification`.
16. **Two `fn` set values** — `verify_fn_set_with_params_equality_by_builtin_rules` (structural compare).

```lit
fact 1 + 1 = 2
fact 0 = t - t
fact sum(i, 1, 3, i) = sum(i, 1, 2, i) + 3
fact sum(i, start, end, body) = sum(i, start, middle, body) + sum(i, middle + 1, end, body)
fact sum(i, 1, 3, i + i) = sum(i, 1, 3, i) + sum(i, 1, 3, i)
fact sum(i, 1, 3, 2 * i) = 2 * sum(i, 1, 3, i)
fact sum(i, 1, 1, i) = 1
fact product(i, 1, 3, i) = product(i, 1, 2, i) * 3
fact product(i, start, end, body) = product(i, start, middle, body) * product(i, middle + 1, end, body)
fact product(i, 1, 3, i * i) = product(i, 1, 3, i) * product(i, 1, 3, i)
fact product(i, 1, 1, i) = 1
```

---

## Powers: well-definedness (`verify_pow_well_defined` in `verify_obj_well_defined.rs`)

When checking that **`base ^ exponent`** is well-defined, the verifier requires **one** of these **Or** branches to go through:

1. `base > 0` and `exponent in R`
2. `base = 0`, `exponent in R`, `exponent > 0` (rules out `0^0` and `0^(non-positive)`)
3. `exponent in Z` and `base != 0`

```lit
know a in R_pos
know b in R
```

---

## Maintaining this doc

When you add a new `try_*` arm or reorder the order pipeline, update **§ Order pipeline** and the algebra table so readers see **patterns → sub-goals**, not only Rust names.
