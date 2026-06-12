# Objects And Data

Examples for Litex objects, data constructors, function objects, structures, macros, templates, and statement forms.


For the syntax sections, the bold line names the Litex form and the following
code shows a small, complete use of that form.

## 1. `algo`

- Category: `obj`
- Purpose: Shows algorithm-backed function definitions.

```litex
sketch:
    have fn f(x R) R = 1

    algo f(x):
        1
```




## 2. `algo_eval`

- Category: `obj`
- Purpose: Shows evaluating algorithm-style functions.

```litex
sketch:
    have fn f(x R) R = x + 1

    algo f(x):
        x + 1

    eval f(2)
    f(2) = 3
```

## 3. `anonymous_function`

- Category: `obj`
- Purpose: Shows anonymous function objects and equality.

```litex
'R(x){x + 1}(2) = 3
$fn_eq('R(x){x}, 'R(y){y})
```

## 4. `anonyumous_fn_forall_match`

- Category: `fact`
- Purpose: Shows matching universal facts over anonymous functions.

```litex
abstract_prop p(x)

claim:
    prove:
        forall a, b, c fn(x R) R:
            forall f, g fn(x R) R:
                $p(f)
                $p(g)
                =>:
                    $p('R(x){f(x) + g(x)})
            $p(a)
            $p(b)
            $p(c)
            =>:
                $p('R(x){a(x) + (b(x) + c(x))})
    $p('R(x){b(x) + c(x)})
```

## 5. `complex_number`

- Category: `obj`
- Purpose: Shows complex-number object syntax.

```litex
struct C:
    re R
    im R
```

## 6. `finite_seq`

- Category: `obj`
- Purpose: Shows finite sequence objects.

```litex
have a finite_seq(R, 3) = [1, 2, 3]

a $in fn(x N_pos: x <= 3) R

a(1) = 1
a(2) = 2
a(3) = 3

finite_seq(R, 3) = fn(x N_pos: x <= 3) R

[1, 2, 3](1) = 1
```

## 7. `fn_eq`

- Category: `fact`
- Purpose: Shows equality of functions by pointwise facts.

```litex
$fn_eq('R(x){x}, 'R(y){y})

have fn f(x R) R = x
have fn g(x R) R = x
forall x R: 
    f(x) = x = g(x)
$fn_eq(f, g)

forall x R:
    (f(x) + g(x)) * g(x) = (g(x) + f(x)) * f(x)
```

## 8. `fn_eq_in`

- Category: `fact`
- Purpose: Shows function equality under set membership constraints.

```litex
# 演示 `$fn_eq_in(f, g, S)`：在 S 上逐点相等；builtin 将目标归约为 forall x in S, f(x)=g(x)
# 本例用 `f` 与 `f` 相同，因而不依赖 forall 的 alpha 匹配，即可在证明中直接验证
have fn f(x R) R = x
have fn g(x R) R = x 

forall x R:
    f(x) = x = g(x)

$fn_eq_in(f, g, R)

$fn_eq_in('R(x){x}, 'R(y){y}, R)
```

## 9. `fn_range`

- Category: `obj`
- Purpose: Shows function range objects and restricted range facts.

```litex
sketch:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    fn_range(f) $subset R
    fn_range(f) $in power_set(R)
```

```litex
sketch:
    have f fn(x R: x > 0) R
    f(1) $in fn_range(f)
    have z R = f(1)

    z = f(1)
    z $in fn_range(f)
    z $in R

    have by preimage x from z $in fn_range(f)
    x $in R
    x > 0
    z = f(x)
```

```litex
sketch:
    have fn shift(x R) R = x + 1

    shift(2) $in fn_range(shift)
    fn_range(shift) $subset R

    have by preimage x from shift(2) $in fn_range(shift)
    x $in R
    shift(2) = shift(x)
```

```litex
sketch:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    have by preimage x from f(1) $in fn_range(f)
    x $in R
    x > 0
    f(1) = f(x)
```

```litex
sketch:
    have g fn(x R, y R: x < y) R

    g(0, 1) $in fn_range(g)
    fn_range(g) $subset R
    fn_range(g) $in power_set(R)

    have by preimage a, b from g(0, 1) $in fn_range(g)
    a $in R
    b $in R
    a < b
    g(0, 1) = g(a, b)
```

```litex
sketch:
    have a seq(R)

    a(1) $in fn_range_on(a, 1...3)
    a(2) $in fn_range_on(a, 1...3)
    fn_range_on(a, 1...3) $subset R
    fn_range_on(a, 1...3) $in power_set(R)
    $is_finite_set(fn_range_on(a, 1...3))
    count(fn_range_on(a, 1...3)) $in N

    have by preimage k from a(2) $in fn_range_on(a, 1...3)
    k $in 1...3
    a(2) = a(k)
```

## 10. `have_fn_as_algo`

- Category: `stmt`
- Purpose: Shows function definitions by algorithm, cases, and induction.

```litex
sketch:
    have fn as algo f(x R) R = x

    eval f(3)
    f(3) = 3
```

```litex
sketch:
    have fn as algo self_max(x, y R) R by cases:
        case x > y: x
        case x <= y: y

    eval self_max(5, 3)
    self_max(5, 3) = 5

    eval self_max(2, 7)
    self_max(2, 7) = 7
```

```litex
sketch:
    have fn as algo h(x Z: x >= 1) R by induc x from 1:
        case x = 1: 211
        case x = 2: 375
        case x = 3: 420
        case x = 4: 523
        case x > 4: h(x - 1) - h(x - 2) + h(x - 3) - h(x - 4)

    eval h(5)
    h(5) = 267
```

## 11. `have_fn_as_set_intro`

- Category: `stmt`
- Purpose: Shows building functions from unique-existence graph facts.

```litex
have A set = R
have B set = R

have fn f as set:
    prove:
        forall x A:
            exist! y B st {y = x}
    witness exist! y B st {y = x} from x

forall x A:
    f(x) = x
```

## 12. `have_fn_by_induc`

- Category: `stmt`
- Purpose: Shows recursive function construction by induction.

```litex
have fn f(x Z: x >= 0) R by induc x from 0:
    case x = 0: 1
    case x > 0: f(x - 1) + 1

have fn g(a Z, b Z: a >= 0, b >= 0) R by induc abs(a) + abs(b) from 0:
    case b = 0: a
    case b > 0: g(a, b - 1) + 1

# Mutual recursion pattern: define a tuple-valued recursive function,
# then project the component functions.
have fn fg(n Z: n >= 0) cart(R, R) by induc n from 0:
    case n = 0: (1, 0)
    case n > 0: (fg(n - 1)[2], fg(n - 1)[1])

have fn f_from_fg(n Z: n >= 0) R = fg(n)[1]
have fn g_from_fg(n Z: n >= 0) R = fg(n)[2]

fg(0) = (1, 0)
f_from_fg(0) = 1
g_from_fg(0) = 0

have fn h(x Z: x >= 1) R by induc x from 1:
    case x = 1: 211
    case x = 2: 375
    case x = 3: 420
    case x = 4: 523
    case x > 4: h(x - 1) - h(x - 2) + h(x - 3) - h(x - 4)

algo h(x):
    case x = 1: 211
    case x = 2: 375
    case x = 3: 420
    case x = 4: 523
    case x > 4: h(x - 1) - h(x - 2) + h(x - 3) - h(x - 4)
```

## 13. `have_fn_case_by_case`

- Category: `stmt`
- Purpose: Shows case-defined functions.

```litex
have fn self_max(x, y R) R by cases:
    case x > y: x
    case x <= y: y
```

## 14. `litex_code_style_guide`

- Category: `stmt`
- Purpose: Shows preferred Litex proof formatting patterns.

```litex
forall a, b Q:
    a - b = 4
    a * b = 1
    =>:
        (a + b)^2 = (a - b)^2 + 4 * (a * b) = 20
```

## 15. `litex_fact_examples`

- Category: `fact`
- Purpose: Shows common fact syntax and verification examples.


**These are the main shapes a fact can have.**

**Equal and not-equal facts**


```litex
sketch:
    1 = 1
    2 != 3
```

**Order facts and their negations**


```litex
sketch:
    0 < 1
    2 > 1
    1 <= 1
    2 >= 1
    not 1 < 0
```

**Chained inequalities**


```litex
sketch:
    0 < 1 < 2
```

**Conjunctions**


```litex
sketch:
    1 = 1 and 2 < 3
```

**disjunctions — disjunction**


```litex
sketch:
    1 = 2 or 1 = 1
```

**existential facts**

**exist fact is usually proved by witness exist ... from ...**


```litex
sketch:
    witness exist x R st { x = 1 } from 1:
        1 = 1

    exist y R st { y = 1 }
```

**forall facts without hypotheses**


```litex
sketch:
    forall s set:
        s = s

    forall x Z:
        x $in R
```

**forall facts with hypotheses and conclusions**

```litex
claim:
    prove:
        forall t R:
            100 < t
            =>:
                0 < t
    by thm a_lt_c(0, 100, t)
```

**forall facts with iff — required `=>:` left side, then `<=>:`**


```litex
sketch:
    forall x, y R:
        =>:
            x > y
        <=>:
            y < x
```

**atomic facts — $is_set / $is_nonempty_set / $is_finite_set / $in**


```litex
sketch:
    $is_set({1, 2})
    $is_nonempty_set({1})
    $is_finite_set({1, 2})
    1 $in {1, 2}
    0.5 $in Q
```


```litex
sketch:
    not $is_nonempty_set({})
```

**atomic facts — $is_cart**


```litex
sketch:
    have c set = cart(R, Q)
    $is_cart(c)
```

**atomic facts — $is_tuple**


```litex
sketch:
    have u set = (1, 2)
    $is_tuple(u)
```

**atomic facts — $subset / $superset**



**atomic facts — negative subset facts**



**restriction facts**

```litex
have f fn(x R, y Q) R

$restricts_to(f, fn(a Q, b Q) R)
```

**named predicate facts**





## 16. `litex_object_examples`

- Category: `obj`
- Purpose: Shows core object constructors and membership facts.


**These examples show how ordinary mathematical data is written and checked.**

**Module names use `::`, as in `Nat::gcd`.**

**numbers**


```litex
sketch:
    1 = 1
    1.5 = 1.5
```

**arithmetic objects, including unary minus**


```litex
sketch:
    1 + 2 = 3
    3 - 1 = 2
    2 * 3 = 6
    6 / 2 = 3
    5 % 2 = 1
    2 ^ 3 = 8
    -1 + 2 = 1
```

**tuples and parenthesized expressions**


```litex
sketch:
    (1, 2) = (1, 2)
```

**standard sets**


```litex
sketch:
    0 $in N
    0 $in Z
    0 $in Q
    0 $in R
    1 $in N_pos
    1 $in R_pos
    -1 $in Z_neg
    1 $in Z_nz
    1 / 6 $in Q
    6 / 3 $in Z
    not 1 / 6 $in Z
    not 2 / 6 $in Z
    not (-1) / 6 $in Z
    not 0 $in Q_nz
```

**displayed finite sets**


```litex
sketch:
    1 $in {1, 2, 3}
    $is_finite_set({1, 2})
```

**set builders as named objects**


```litex
sketch:
    have s set = { z N : z > 5 }
```

**unions, intersections, and set difference**


```litex
sketch:
    2 $in union({1, 2}, {2, 3})
    2 $in intersect({1, 2}, {2, 3})
```


```litex
sketch:
    have t set = set_minus({1, 2}, {1})
```


```litex
sketch:
    have u set = set_diff({1, 2}, {3})
```

**ranges and closed ranges**


```litex
sketch:
    have r set = range(0, 10)
    have w set = closed_range(0, 1)
```

**projections (keyword)**



**Cartesian products and dimensions**




```litex
sketch:
    have f fn(x R) R
    have g set = fn(x R) R
```

**tuple dimensions and indexing**

```litex

(1, 2)[1] = 1
(1, 2)[2] = 2

have a set = (1, 2)
a[1] = 1
a[2] = 2

```



**power sets and counting**


```litex
sketch:
    {1, 2} $in power_set({1, 2, 3})
    count({1, 2, 3}) = 3
```

**unions and intersections over families**

**Surface: `cup({{a}, {b}})`, `cap({{a, b}, {b, c}})` (requires provably distinct inner sets for `have`).**

**Axiom of choice proof step**



**function applications (e.g. `f(0)` after `have fn f(x R) R = ...`)**


```litex
sketch:
    have fn f(x R) R = x + 1

    have fn pair_value(x Z) cart(Z, Z) = (x, x + 1)
    pair_value(0)[1] $in Z
    pair_value(0)[2] $in Z
```

**Parameterized struct references use angle brackets; fields are accessed through a struct view.**


```litex
sketch:
    struct rec<a set>:
        fld a
        fld2 a

    have r &rec<R>
    &rec<R>{r}.fld $in R
```

## 17. `litex_statement_examples`

- Category: `stmt`
- Purpose: Shows common statement forms in one reference file.


**These examples show common statement forms.**

**`import` and `run_file` syntax is shown in comments only here.**

**assert a closed fact**


```litex
sketch:
    1 + 1 = 2
```

**let statements — local names with defining properties**



**property definitions — define a named predicate with its if and only if properties**


```litex
sketch:
    prop p(x R):
        x = x
```

**abstract predicate declarations — declare a predicate symbol and arity only**


```litex
sketch:
    abstract_prop q(a)
```

**typed object introductions — introduce typed parameters (membership in given sets / types)**


```litex
sketch:
    have x R, y Z
```

**object definitions — introduce parameters and fix them to given values**


```litex
sketch:
    have a R = 1
    a = 1
```

**naming existential witnesses — name witnesses for an already known existential**



**function definitions — define a function by a single defining equation on its domain**


```litex
sketch:
    have fn f(x R) R = x + 1
    do_nothing
```

**piecewise function definitions — piecewise definition by cases on the domain**


```litex
sketch:
    have fn g(z R) R by cases:
        case z = 2: 3
        case z != 2: 4
    do_nothing
```

**recursive function definitions — recursive function given by a decreasing measure**


```litex
sketch:
    have fn h(a Z, b Z: a >= 0, b >= 0) R by induc abs(a) + abs(b) from 0:
        case b = 0: a
        case b > 0: h(a, b - 1) + 1
```

**struct declarations — removed in this branch (record-like `struct`); see git history to restore.**

**algorithm presentations — computational presentation of a function (evaluation)**


```litex
sketch:
    have fn m(x N_pos) R by cases:
        case x = 1: 1
        case x != 1: 0

    algo m(x):
        case x = 1: 1
        case x != 1: 0

    eval m(1)
    m(1) = 1
```

**claim blocks — stated goal with a sub-proof and lemmas**

**(A claim may state a `forall` goal; here both goals are short tautologies so the file runs.)**


```litex
sketch:
    claim:
        prove:
            1 + 1 = 2
        1 + 1 = 2

    claim:
        prove:
            2 = 2
        2 = 2
```

**assumption blocks — assume lemmas / axioms in scope**



**sketch blocks — checked sketch work with local facts**


```litex
sketch:
    2 = 2
```

**imports and run_file — module or file inclusion (syntax only here)**

**import Nat**

**run_file "./runfile2.lit"**

**do_nothing — trivial proof step**


```litex
sketch:
    do_nothing
```

**evaluation — compute a closed expression**



**existential witnesses — exhibit witnesses for an existential claim**


```litex
sketch:
    witness exist x, y R st {x > y} from 1, 0:
        1 > 0

    exist a, b R st {a > b}
```

**nonempty-set witnesses — exhibit an element to show a set is nonempty**



**proof by cases — proof by cases on a finite disjunction**


```litex
sketch:
    have fn k(z R) R by cases:
        case z = 2: 3
        case z != 2: 4

    have x R

    x = 2 or x != 2

    by cases:
        prove:
            k(x) > 2
        case x = 2:
            k(x) = 3
            k(x) > 2
        case x != 2:
            k(x) = 4
            k(x) > 2
```

**proof by contradiction — proof of negation from a contradiction**



**ByEnumerateFiniteSetStmt — Cartesian product over list-set forall params (like by for; see docs/quick_reference.md). Use `by enumerate finite_set:` then `prove:` with one forall.**



**ByEnumerateRangeStmt — expand integer range / closed_range membership into equality cases.**



**induction — induction on a discrete parameter**



**bounded iteration — finite or bounded iteration as proof skeleton**


```litex
sketch:
    by for:
        prove:
            forall i range(0, 10):
                i < 10
        do_nothing
```

**extensional equality — set equality by mutual inclusion**


```litex
sketch:
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

**function-as-set reasoning — use the graph characterization of a function in a function space**


```litex
sketch:
    have fn f(x R) R = 1

    by fn as set: f
```

**struct declarations — define a structure shape for future struct features**


```litex
sketch:
    abstract_prop bs(b, c, d)

    struct sq<a set>:
        b1 a
        c1 fn(x a) a
        d1 fn(x, y a) a
        <=>:
            $bs(b1, c1, d1)
```

**tuple-as-set reasoning — tuple / product-space reasoning on an object**



**function-set reasoning — membership of a function in a function set (graph axioms)**



## 18. `macro`

- Category: `stmt`
- Purpose: Shows macro definitions and expansion.

```litex
macro SELF_R "R"

macro HAVE_FN "have fn"

@HAVE_FN f(x @SELF_R) @SELF_R = x
```

```litex
sketch:
    macro SELF_R "R"
    macro HAVE_FN "have fn"
    macro SELF_Q "Q"
    @HAVE_FN g(x @SELF_Q) @SELF_Q = x

    @HAVE_FN h(x @SELF_R) @SELF_R = x

macro STRANGE "f("

have fn f(x R) R = x

forall x R:
    @STRANGE x) = f( x)
```

## 19. `matrix`

- Category: `obj`
- Purpose: Shows matrix-like function objects and indexing.

```litex
sketch:
    matrix(R, 2, 2) = matrix(R, 2, 2)

    have a matrix(R, 2, 2) = [[1, 2], [3, 4]]

    a $in fn (x1 N_pos, x2 N_pos: x1 <= 2, x2 <= 2) R

    a(1, 1) = 1
    a(1, 2) = 2
    a(2, 1) = 3
    a(2, 2) = 4


# Matrix ++: same shape, cell-wise add
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]

have m matrix(R, 2, 2) = [[1, 0], [0, 1]]

# Named matrix ++
eval m ++ m

# Matrix --: same shape, cell-wise subtract
eval [[2, 0], [0, 2]] -- [[1, 0], [0, 1]]

# Matrix **: columns of left = rows of right
# [[1,2],[0,1]] * [[1,0],[1,1]] = [[3,2],[1,1]]
eval [[1, 2], [0, 1]] ** [[1, 0], [1, 1]]

# *. : scalar (left) times matrix (right)
eval 3 *. [[1, 2], [4, 5]]

# ^^ : square matrix to power n (n in N_pos)
eval [[2, 0], [0, 2]] ^^ 2

# Named identity: ** and scalar
eval m ** m
eval 2 *. m

# Matrix eval keeps exact rational entries
eval [[1 / 2, 1 / 3], [0, 1]] ** [[1, 0], [1 / 6, 1 / 2]]
eval (1 / 3) *. [[3, 6], [9, 12]]
```

## 20. `restrict`

- Category: `obj`
- Purpose: Shows restricted parameter and object types.

```litex
sketch:
    have f fn(x R, y Q) R 

    $restricts_to(f, fn(a Q, b Q) R)

    $restricts_to(f, fn(x R, y Q: x < y) R)

    have g fn(x, y R) R

    $restricts_to(g, fn(x, y R: x < y, x < 0) R)

    $restricts_to(g, fn(p Q, q Q) R)
```


```litex
sketch:
    forall f fn(x R, y Q) R:
        f(1, 2) = f(1, 2)
```


```litex
sketch:
    $restricts_to('R(x){x}, fn(x closed_range(1, 2)) R)
    $restricts_to('R(x){x + 1}, fn(x closed_range(1, 2)) R)
    $restricts_to('(x R: x > 0) R {x}, fn(x N_pos) R)
    $restricts_to('R(x){x}, fn(x closed_range(1, 2)) N)
```

## 21. `set_builder`

- Category: `obj`
- Purpose: Shows set-builder object syntax.

```litex
1 $in {x R: x > 0}
```

## 22. `signed_area`

- Category: `obj`
- Purpose: Shows a small geometric data expression.

```litex
have fn signed_area(x, y cart(R, R)) R = x[1] * y[2] - x[2] * y[1]

signed_area((1, 0), (0, 1)) = 1 * 1 - 0 * 0 = 1
```

## 23. `struct`

- Category: `obj`
- Purpose: Shows struct definitions, fields, and dependent struct views.

```litex
sketch:
    struct Point:
        x R
        y R

    (1, 2) $in &Point
    have p &Point = (1, 2)
    &Point{p}.x = p[1]
    &Point{p}.x = 1
    &Point{(1, 2)}.y = 2

    have p2 &Point

    &Point{p2}.x $in R

    have a &Point

    have fn point_add (a, b &Point) &Point = (a[1] + b[1], a[2] + b[2])

    forall a, b &Point:
        point_add(a, b) = (a[1] + b[1], a[2] + b[2]) = (b[1] + a[1], b[2] + a[2]) = point_add(b, a)
```

```litex
sketch:
    prop GroupProperty(s set, inv fn(x s) s, op fn(x, y s) s, e s):
        forall x s:
            op(x, inv(x)) = e
            op(inv(x), x) = e
        forall x, y, z s:
            op(x, op(y, z)) = op(op(x, y), z)
        forall x s:
            op(x, e) = x
            op(e, x) = x

    struct Group<s set>:
        inv fn(x s) s
        op fn(x, y s) s
        e s
        <=>:
            $GroupProperty(s, inv, op, e)

    $GroupProperty(R, 'R(x){-x}, 'R(x, y){x + y}, 0)
    ('R(x){-x}, 'R(x, y){x + y}, 0) $in &Group<R>
```

```litex
sketch:
    struct StandardTwoSimplex:
        x R
        y R
        z R
        <=>:
            0 <= x
            0 <= y
            0 <= z
            x + y + z = 1

    forall s &StandardTwoSimplex:
        s[1] $in R
        s[2] $in R
        s[3] $in R
        0 <= s[1]
        0 <= s[2]
        0 <= s[3]

    forall s &StandardTwoSimplex:
        1 = s[1] + s[2] + s[3] = s[2] + s[1] + s[3]
        (s[2], s[1], s[3]) $in &StandardTwoSimplex

    have fn swapXy(s &StandardTwoSimplex) &StandardTwoSimplex = (s[2], s[1], s[3])

    forall a, b &StandardTwoSimplex:
        (a[1] + b[1]) / 2 + (a[2] + b[2]) / 2 + (a[3] + b[3]) / 2 = ((a[1] + a[2] + a[3]) + (b[1] + b[2] + b[3])) / 2 = (1 + 1) / 2 = 1
        ((a[1] + b[1]) / 2, (a[2] + b[2]) / 2, (a[3] + b[3]) / 2) $in &StandardTwoSimplex

    have fn midpoint(a, b &StandardTwoSimplex) &StandardTwoSimplex = ((a[1] + b[1]) / 2, (a[2] + b[2]) / 2, (a[3] + b[3]) / 2)
```

```litex
sketch:
    struct StandardTwoSimplex:
        x R
        y R
        z R
        <=>:
            0 <= x
            0 <= y
            0 <= z
            x + y + z = 1

    forall s &StandardTwoSimplex:
        1 = &StandardTwoSimplex{s}.x + &StandardTwoSimplex{s}.y + &StandardTwoSimplex{s}.z = &StandardTwoSimplex{s}.y + &StandardTwoSimplex{s}.x + &StandardTwoSimplex{s}.z
        (&StandardTwoSimplex{s}.y, &StandardTwoSimplex{s}.x, &StandardTwoSimplex{s}.z) $in &StandardTwoSimplex

    have fn swapXy(s &StandardTwoSimplex) &StandardTwoSimplex = (&StandardTwoSimplex{s}.y, &StandardTwoSimplex{s}.x, &StandardTwoSimplex{s}.z)

    forall a, b &StandardTwoSimplex:
        (&StandardTwoSimplex{a}.x + &StandardTwoSimplex{b}.x) / 2 + (&StandardTwoSimplex{a}.y + &StandardTwoSimplex{b}.y) / 2 + (&StandardTwoSimplex{a}.z + &StandardTwoSimplex{b}.z) / 2 = ((&StandardTwoSimplex{a}.x + &StandardTwoSimplex{a}.y + &StandardTwoSimplex{a}.z) + (&StandardTwoSimplex{b}.x + &StandardTwoSimplex{b}.y + &StandardTwoSimplex{b}.z)) / 2 = (1 + 1) / 2 = 1
        ((&StandardTwoSimplex{a}.x + &StandardTwoSimplex{b}.x) / 2, (&StandardTwoSimplex{a}.y + &StandardTwoSimplex{b}.y) / 2, (&StandardTwoSimplex{a}.z + &StandardTwoSimplex{b}.z) / 2) $in &StandardTwoSimplex

    have fn midpoint(a, b &StandardTwoSimplex) &StandardTwoSimplex = ((&StandardTwoSimplex{a}.x + &StandardTwoSimplex{b}.x) / 2, (&StandardTwoSimplex{a}.y + &StandardTwoSimplex{b}.y) / 2, (&StandardTwoSimplex{a}.z + &StandardTwoSimplex{b}.z) / 2)
```

```litex
sketch:
    struct StandardTwoSimplex:
        x R
        y R
        z R
        <=>:
            0 <= x
            0 <= y
            0 <= z
            x + y + z = 1

    macro s "&StandardTwoSimplex{s}"
    macro a "&StandardTwoSimplex{a}"
    macro b "&StandardTwoSimplex{b}"

    forall s &StandardTwoSimplex:
        1 = @s.x + @s.y + @s.z = @s.y + @s.x + @s.z
        (@s.y, @s.x, @s.z) $in &StandardTwoSimplex

    have fn swapXy(s &StandardTwoSimplex) &StandardTwoSimplex = (@s.y, @s.x, @s.z)

    forall a, b &StandardTwoSimplex:
        (@a.x + @b.x) / 2 + (@a.y + @b.y) / 2 + (@a.z + @b.z) / 2 = ((@a.x + @a.y + @a.z) + (@b.x + @b.y + @b.z)) / 2 = (1 + 1) / 2 = 1
        ((@a.x + @b.x) / 2, (@a.y + @b.y) / 2, (@a.z + @b.z) / 2) $in &StandardTwoSimplex

    have fn midpoint(a, b &StandardTwoSimplex) &StandardTwoSimplex = ((@a.x + @b.x) / 2, (@a.y + @b.y) / 2, (@a.z + @b.z) / 2)
```

## 24. `template1`

- Category: `stmt`
- Purpose: Shows template declarations and use.

```litex
template<s set: s = s>:
    have id_on_set set = s

\id_on_set<R> = R

template<s set: s = s>:
    have fn const_zero(x s) R = 0

\const_zero<R>(0) = \const_zero<R>(0)

template<S set, n N_pos>:
    have tensor3 set = fn(i closed_range(1, n), j closed_range(1, n), k closed_range(1, n)) S

have A \tensor3<R, 3>
A(1, 2, 3) $in R
```

## 25. `template_let`

- Category: `stmt`
- Purpose: Shows local definitions inside templates.

```litex
template<s set, z s>:
    have fn const_on_s(x s) s = z

\const_on_s<R, 0> $in fn(x R) R
```

## 26. `tuple_and_cart`

- Category: `obj`
- Purpose: Shows tuple objects and Cartesian products.

```litex
(1, 2) = (1, 2)
cart_dim(cart(R, Q)) = 2
proj(cart(R, Q), 1) = R
```
