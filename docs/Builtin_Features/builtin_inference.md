# Builtin Inference

Try all snippets in browser: https://litexlang.com/doc/Builtin_Features/Builtin_Inference

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Builtin_Features/Builtin_Inference.md

After a fact is **verified** or **known** in the environment, the system **stores** it and may run **inference**. Inference can **add further facts** (still true in the same context) or remember side information used later. That is separate from **builtin verification rules**, which are the built-in steps that **close proof goals** during checking.

Below, each item gives the **mathematical meaning**, then a **`forall … =>:`** pattern: the premise is the fact that triggers inference; the conclusion lists typical consequences (what becomes available in the same way as after storing the premise).

---

## Shapes of facts: what inference does

For **atomic** facts (equations, membership, comparisons, predicates, …), the rules in the following sections apply.

For **existential** claims **`exist!`** with parameters: inference adds a **uniqueness** statement—any two witnesses (as tuples of parameters) satisfying the body must agree.

For **“not exist”** with parameters: inference adds the usual **universal** (De Morgan) equivalent.

For a **chain** of equalities (and similar chained facts): every equality forced by **transitivity** along the chain is treated like any other equation for inference purposes.

**Disjunctions, conjunctions**, and **outermost universal** facts (`forall` as a single stored fact, including those with **`iff`**) do **not**, by themselves, launch the extra inference pass described here—the work happens on the **atomic pieces** when those are assumed or proved separately.

For **“not forall”**: inference adds an **existential counterexample** (parameters that falsify the inner universal claim).

---

## Equality: difference zero

If one side is `0` and the other is a **difference** `u - v`, inference adds **`u = v`** (when that is not already trivial from syntax).

```litex
forall a, b R:
    a - b = 0
    =>:
        a = b
```

---

## Equality: tuple on one side

If one side is a **tuple** with at least two components and the other is not, inference records that the other object **is a tuple**, that its **length** matches, and keeps **tuple / product-set** bookkeeping consistent with that.

```litex
forall t R, a R, b R:
    t = (a, b)
    =>:
        $is_tuple(t)
```

---

## Equality: Cartesian product literal on one side

If one side is a **literal** Cartesian product **`cart(…)`** and the other is not, inference records **“is a Cartesian product”**, the **number of factors**, and related metadata.

```litex
forall d set:
    d = cart(R, Q)
    =>:
        $is_cart(d)
```

---

## Equality: numeric value on one side

If one side **simplifies to a concrete number**, inference treats the other side as **known to equal that number** for substitution and numeric reasoning. This may **not** appear as a separate new displayed line in a short trace.

---

## Equality: simple linear equations

If an equality has a **simple linear** form and one side is a **concrete number**, inference may treat the main unknown as **fixed to that number**, in the same sense as above (again, not always as a separate displayed line).

---

## Equality: finite sequence or matrix display on one side

If one side is a **finite sequence literal** or **matrix written as a literal grid** and the other is not, inference **remembers** that the other name has that **list or matrix shape** for later checks.

---

## Equality: name equals an anonymous function

If one side is an **anonymous function** and the other is not, inference **remembers** for the other side the **argument list** and, when present, the **defining equation** of that function.

---

## Predicate calls (`$P(…)`): parameters and definition

For a user **`prop`** whose body includes **`iff`** parts, once **`$P(args)`** is in context, inference first ensures **typing constraints** for the arguments, then **instantiates** each **`iff`** clause by plugging in those arguments. What you get next depends entirely on how **`P`** is defined.

```litex
prove:
    prop unit_x(x R):
        forall x R:
            =>:
                x = 1
            <=>:
                x + 0 = 1
```

---

## Membership in `N`

Inference adds **`x >= 0`** (equivalently **`0 <= x`**) so membership in the naturals is aligned with the usual nonnegative half-line.

```litex
forall k N:
    0 <= k
```

---

## Membership in `N_pos`, `R_pos`, `Q_pos`

Inference adds **strict positivity** **`0 < x`**.

```litex
forall x R_pos:
    0 < x
```

```litex
forall x N_pos:
    0 < x
```

---

## Membership in `R_neg`, `Q_neg`, `Z_neg`

Inference adds **`x < 0`**.

```litex
forall x R_neg:
    x < 0
```

---

## Membership in `R_nz`, `Q_nz`, `Z_nz`

Inference adds **`x != 0`**.

```litex
forall x R_nz:
    x != 0
```

---

## Membership in `Z`, `Q`, `R`

**No** further facts follow from these **membership judgements alone**.

---

## Membership in a finite enumeration `{…}`

Inference replaces membership by a **finite disjunction**: **`x = e1` or `x = e2` or …**.

```litex
forall a R:
    a $in {1, 2}
    =>:
        a = 1 or a = 2
```

---

## Membership in `cart(…)` (at least two factors)

Inference adds **tuple** information (**“is a tuple”**, **dimension** \(n\) equal to the number of factors), aligns product-set bookkeeping, and for each factor **`A_i`** infers **`u[i] $in A_i`** (one-based indexing).

```litex
forall u cart(R, R):
    $is_tuple(u)
    u[1] $in R
    u[2] $in R
```

---

## Membership in `range(a, b)` (half-open integer interval)

Inference adds integer membership and the **two-sided bounds** **`a <= x`** and **`x < b`**.

```litex
forall i Z:
    i $in range(2, 6)
    =>:
        2 <= i
        i < 6
```

---

## Membership in `closed_range(a, b)`

Inference adds integer membership and **`a <= x`** and **`x <= b`**.

```litex
forall i Z:
    i $in closed_range(1, 3)
    =>:
        1 <= i
        i <= 3
```

---

## Membership in a set comprehension `{ param $in S | … }`

Inference adds **membership in the base set** **`S`**, and each **filter** condition with the bound variable **replaced by the element**.

```litex
forall x R:
    x $in { y R: 0 <= y }
    =>:
        0 <= x
```

---

## Membership in `fn(…)` (function space)

Inference **records function-space information** for suitable function heads (names coming from the language, not arbitrary complex expressions) so later goals can use the expected **domain and codomain** shape.

---

## Membership in `finite_seq(…)`, `seq(…)`, `matrix(…)`

These are read as **function types**; inference applies the same ideas as for **`fn(…)`** and may expose an explicit **`… $in fn …`** fact.

A finite sequence literal can also be used as the finite function it denotes. For example, `[1, 2, 3](i)` is checked as the `i`-th entry of the sequence, with `i $in N_pos` and `i <= 3`.

---

## Membership in a `family` instance `\name(…)`

The family is **expanded** to the set it denotes; then the usual **membership** inference rules apply to that set.

---

## Subset

From **`A $subset B`**, inference adds universal membership: **for every `x` in `A`, `x $in B`** (with a fresh variable name).

Litex note: inside a **`forall … =>:`** block, the **`=>:`** tail cannot be another raw **`forall`**; use **`let`** for the subset statement, then a separate **`forall`** line that matches what inference added.

```litex
prove:
    let A, B set:
        A $subset B
    forall x A:
        x $in B
```

---

## Superset

From **`A $superset B`**, inference adds **for every `x` in `B`, `x $in A`**. Same syntactic remark as for subset.

```litex
prove:
    let A, B set:
        A $superset B
    forall x B:
        x $in A
```

---

## Restricting a function to a smaller function type (`$restrict_fn_in`)

Inference **narrows** the recorded “this object lives in this function space” information to the **more specific** function type you gave—without restating the whole definition.

---

## Order: constant on one side, infer sign versus zero

When **exactly one** side of an inequality is a **numeric constant** that the system has fully evaluated, inference may add a simpler inequality comparing the **other** side **to zero** (e.g. from **`k <= a`** with **`k > 0`** one gets **`0 < a`**; from **`k > b`** with **`k <= 0`** one gets **`b <= 0`**, and similar cases).

```litex
forall a R:
    2 <= a
    =>:
        0 < a
```

```litex
forall b R:
    -1 >= b
    =>:
        b <= 0
```

---

## Order: zero on the right and multiplying by **\(-1\)**

When the **right-hand** side is **`0`** and the left-hand side is **not** already **`(-1) * u`**, inference may **flip** strict/weak inequality to a statement about **`-1` times** the left-hand side (e.g. **`x < 0`** yields **`-1 * x >= 0`**). There is **no** matching automatic rule when **`0` is on the left**.

```litex
forall x R:
    x < 0
    =>:
        -1 * x >= 0
```

---

## Atomic facts that trigger no extra inference

Some built-in atoms are **left as they are** for this pass—e.g. **negated comparisons**, **`$is_set`**, **`not $restrict_fn_in`**, and similar. They can still be used in proofs; inference simply does not unfold them further here.
