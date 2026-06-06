# Objects And Data

Examples for Litex objects, data constructors, function objects, structures, macros, templates, and statement forms.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `algo`

- Category: `obj`
- System surface: `algo function object`
- Purpose: Shows algorithm-backed function definitions.

```litex
prove:
    have fn f(x R) R = 1

    algo f(x):
        1


prove:
    have f fn(x, y R) R

    know:
        forall x, y R:
            f(x, y) = f(x - 1, y) + 1

        forall x, y R:
            x = 0
            =>:
                f(x, y) = y

    algo f(x, y):
        case x = 0: y
        f(x - 1, y) + 1

    eval f(10, 20)

    f(10, 20) = 30

prove:
    have fib fn(x R) R

    know:
        forall x R:
            x = 0
            =>:
                fib(x) = 0

        forall x R:
            x = 1
            =>:
                fib(x) = 1

        forall x R:
            x > 1
            =>:
                fib(x) = fib(x - 1) + fib(x - 2)
        
    algo fib(x):
        case x = 0: 0
        case x = 1: 1
        fib(x - 1) + fib(x - 2)
        
    eval fib(3)
    fib(3) = 2

prove:
    have factorial fn(x R) R

    know:
        forall x R:
            x = 0
            =>:
                factorial(x) = 1

        forall x R:
            x > 0
            =>:
                factorial(x) = factorial(x - 1) * x

    algo factorial(x):
        case x = 0: 1
        factorial(x - 1) * x

    eval factorial(3)
    factorial(3) = 6
```

## 2. `algo_eval`

- Category: `obj`
- System surface: `algo evaluation`
- Purpose: Shows evaluating algorithm-style functions.

```litex
let f set
know f $in fn(x R, y R) R

know:
    forall x, y R:
        x < 0
        =>:
            f(x, y) = f(x + 1, y)

    forall x, y R:
        x = 0
        =>:
            f(x, y) = y

    forall x, y R:
        x > 0
        =>:
            f(x, y) = f(x - 1, y)

algo f(x, y):
    case x < 0: f(x + 1, y)
    case x = 0: y
    case x > 0: f(x - 1, y)
```

## 3. `anonymous_function`

- Category: `obj`
- System surface: `anonymous function`
- Purpose: Shows anonymous function objects and equality.

```litex
'(x, y: x < y) R {x + y} = '(x, y: x < y) R {x + y}
'R(x){x} = 'R(x){x}
'R(x){x} = '(x R) R {x}
'R(x){x} = 'R(y){y}

'R(x){x + 2*x}(3) = 9

'R(x, y){x+y}(3, 4) = 7

forall y R:
    'R(x){x + 2*x}(y) = y + 2*y
    'R(x){x}(y) + 'R(x){2*x}(y) = y + 2*y
    'R(x){x + 2*x}(y) = 'R(x){x}(y) + 'R(x){2*x}(y)

forall f, g fn(x R) R:
    'R(x){f(x) + g(x)} = 'R(x){g(x) + f(x)}

forall f, g fn(x R) R:
    'R(x){f(x) + g(x)} = 'R(x){'R(y){f(y)}(x) + 'R(y){g(y)}(x)}

have f fn(x R) R = 'R(x){x}

f(1) = 'R(x){x}(1) = 1

abstract_prop p(fn_value)

know forall u, v fn(x R) R:
    $p(u)
    $p(v)
    =>:
        $p('R(x){u(x) + v(x)})

claim:
    prove:
        forall a, b, c fn(x R) R:
            $p(a)
            $p(b)
            $p(c)
            =>:
                $p('R(x){a(x) + (b(x) + c(x))})
    $p('R(x){b(x) + c(x)})
```

## 4. `anonyumous_fn_forall_match`

- Category: `fact`
- System surface: `anonymous function forall matching`
- Purpose: Shows matching universal facts over anonymous functions.

```litex
# This example demonstrates enhanced known-forall matching inside anonymous
# function bodies.
#
# The known forall says: if p holds for two real-valued functions f and g,
# then p holds for their pointwise sum function.

abstract_prop p(x)

know forall f, g fn(x R) R:
    $p(f)
    $p(g)
    =>:
        $p('R(x){f(x) + g(x)})

# The verifier still uses known forall facts one layer at a time.
# So the proof first establishes the inner sum function:
#     'R(x){b(x) + c(x)}
# from p(b) and p(c).
#
# Then, for the final goal, the new matcher can treat the target body
#     a(x) + (b(x) + c(x))
# as matching
#     f(x) + g(x)
# with:
#     f := a
#     g := 'R(x){b(x) + c(x)}
#
# The important new step is the match:
#     g(x)  ~  b(x) + c(x)
# inside the surrounding anonymous function 'R(x){...}.  Since g is applied
# to the full anonymous-function parameter list x, Litex may infer the whole
# function g as 'R(x){b(x) + c(x)}.  This does not apply to pointwise shapes
# such as g(0), which do not determine the whole function.

claim:
    prove:
        forall a, b, c fn(x R) R:
            $p(a)
            $p(b)
            $p(c)
            =>:
                $p('R(x){a(x) + (b(x) + c(x))})
    $p('R(x){b(x) + c(x)})
```

## 5. `complex_number`

- Category: `obj`
- System surface: `complex literals`
- Purpose: Shows complex-number object syntax.

```litex
struct C:
    re R
    im R
```

## 6. `finite_seq`

- Category: `obj`
- System surface: `finite sequence`
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
- System surface: `function equality`
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
- System surface: `function equality in context`
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
- System surface: `function range`
- Purpose: Shows function range objects and restricted range facts.

```litex
prove:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    fn_range(f) $subset R
    fn_range(f) $in power_set(R)

prove:
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

prove:
    have fn shift(x R) R = x + 1

    shift(2) $in fn_range(shift)
    fn_range(shift) $subset R

    have by preimage x from shift(2) $in fn_range(shift)
    x $in R
    shift(2) = shift(x)

prove:
    have f fn(x R: x > 0) R

    f(1) $in fn_range(f)
    have by preimage x from f(1) $in fn_range(f)
    x $in R
    x > 0
    f(1) = f(x)

prove:
    have g fn(x R, y R: x < y) R

    g(0, 1) $in fn_range(g)
    fn_range(g) $subset R
    fn_range(g) $in power_set(R)

    have by preimage a, b from g(0, 1) $in fn_range(g)
    a $in R
    b $in R
    a < b
    g(0, 1) = g(a, b)

prove:
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
- System surface: `have fn as algo`
- Purpose: Shows function definitions by algorithm, cases, and induction.

```litex
prove:
    have fn as algo f(x R) R = x

    eval f(3)
    f(3) = 3

prove:
    have fn as algo self_max(x, y R) R by cases:
        case x > y: x
        case x <= y: y

    eval self_max(5, 3)
    self_max(5, 3) = 5

    eval self_max(2, 7)
    self_max(2, 7) = 7

prove:
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
- System surface: `have fn as set`
- Purpose: Shows building functions from unique-existence graph facts.

```litex
# `have fn ... as set` turns a unique-existence theorem into a callable function.
#
# Shape:
#
#     know forall x A:
#         exist! y B st {$Graph(x, y)}
#
#     have fn f as set:
#         prove:
#             forall x A:
#                 exist! y B st {$Graph(x, y)}
#
# After that, `f(x)` is the unique `y` satisfying `$Graph(x, y)`.
#
# If the `forall` has domain facts before `=>:`, those facts become restrictions in the
# generated function set. For example, `forall x R: x != 0 => exist! y R ...` creates
# a function in `fn(x R: x != 0) R`, not a total function in `fn(x R) R`.

abstract_prop double_value(x, y)

# In a real development, this `know` can be replaced by a proof.
know:
    forall x R:
        exist! y R st {$double_value(x, y)}

    forall x, y R:
        $double_value(x, y)
        =>:
            y = 2 * x

have fn double as set:
    prove:
        forall x R:
            exist! y R st {$double_value(x, y)}

# `double` is a total function from R to R.
double $in fn(x R) R

# The function value satisfies the graph predicate.
$double_value(3, double(3))
double(3) = 2 * 3 = 6

# The same pattern can include domain assumptions before the `=>:`.
abstract_prop reciprocal_value(x, y)

know:
    forall x R:
        x != 0
        =>:
            exist! y R st {$reciprocal_value(x, y)}

    forall x, y R:
        $reciprocal_value(x, y)
        =>:
            x * y = 1

have fn reciprocal as set:
    prove:
        forall x R:
            x != 0
            =>:
                exist! y R st {$reciprocal_value(x, y)}

# Because the source `forall` has the domain fact `x != 0`, `reciprocal`
# lives in the restricted function set below.
reciprocal $in fn(x R: x != 0) R

$reciprocal_value(2, reciprocal(2))
2 * reciprocal(2) = 1

# The return object can be used anywhere an ordinary function application can be used.
reciprocal(2) * 2 = 2 * reciprocal(2) = 1
```

## 12. `have_fn_by_induc`

- Category: `stmt`
- System surface: `have fn by induc`
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
- System surface: `have fn by cases`
- Purpose: Shows case-defined functions.

```litex
have fn self_max(x, y R) R by cases:
    case x > y: x
    case x <= y: y
```

## 14. `litex_code_style_guide`

- Category: `stmt`
- System surface: `code style`
- Purpose: Shows preferred Litex proof formatting patterns.

```litex
# write <= and < instead of >= and >

# 用 thm 给一个 forall fact 取名，特别是 then-fact 本身的参数少于 forall 参数时。

"""
比如下面这个不好，因为未来想用这个事实证明后续事实的时候，then-fact 里没有 b：

know forall a, b, c R:
    a < b
    b < c
    =>:
        a < c

要写成 named theorem，然后在使用处显式传入所有 forall 参数：

thm a_less_than_c:
    prove:
        forall a, b, c R:
            a < b
            b < c
            =>:
                a < c
    a < b < c

claim:
    prove:
        forall a, b, c R:
            a < b
            b < c
            =>:
                a < c
    by thm a_less_than_c(a, b, c)
"""
```

## 15. `litex_fact_examples`

- Category: `fact`
- System surface: `fact forms`
- Purpose: Shows common fact syntax and verification examples.

```litex
# Fact layer: each surface form maps to a `Fact` variant; atomic pieces map to `AtomicFact`
# (see `src/fact/fact.rs` and `src/fact/atomic_fact.rs`). Independent blocks for copy-paste.

# --- Fact::AtomicFact — EqualFact, NotEqualFact ---
prove:
    1 = 1
    2 != 3

# --- AtomicFact — order (Less / Greater / LessEqual / GreaterEqual) and negated forms ---
prove:
    0 < 1
    2 > 1
    1 <= 1
    2 >= 1
    not 1 < 0

# --- Fact::ChainFact — chained binary relations (one `ChainFact`, not nested `AndFact`) ---
prove:
    0 < 1 < 2

# --- Fact::AndFact — conjunction of atomics ---
prove:
    1 = 1 and 2 < 3

# --- Fact::OrFact — disjunction ---
prove:
    1 = 2 or 1 = 1

# --- Fact::ExistFact ---
# exist fact is usually proved by witness exist ... from ...
prove:
    witness exist x R st { x = 1 } from 1:
        1 = 1

    exist y R st { y = 1 }

# --- Fact::ForallFact — no domain guard (empty `dom_facts`) ---
prove:
    forall s set:
        s = s

    forall x Z:
        x $in R

# --- Fact::ForallFact — with `=>:` (non-empty `dom_facts` + `then_facts`) ---
claim:
    prove:
        forall t R:
            100 < t
            =>:
                0 < t
    by thm a_lt_c(0, 100, t)

# --- Fact::ForallFactWithIff — required `=>:` left side, then `<=>:` ---
prove:
    forall x, y R:
        =>:
            x > y
        <=>:
            y < x

# --- AtomicFact — $is_set / $is_nonempty_set / $is_finite_set / $in ---
prove:
    $is_set({1, 2})
    $is_nonempty_set({1})
    $is_finite_set({1, 2})
    1 $in {1, 2}
    0.5 $in Q

prove:
    not $is_nonempty_set({})

# --- AtomicFact — $is_cart ---
prove:
    have c set = cart(R, Q)
    $is_cart(c)

# --- AtomicFact — $is_tuple ---
prove:
    have u set = (1, 2)
    $is_tuple(u)

# --- AtomicFact — $subset / $superset ---
prove:
    let a, b set:
        a $subset b
    forall x a:
        x $in b
    b $superset a

# --- AtomicFact — NotSubsetFact / NotSupersetFact ---
prove:
    let a, b set:
        not a $subset b
    not b $superset a

# --- Stmt::Fact — RestrictFact (top-level fact line, not inside `prove:`) ---
have f fn(x R, y Q) R

$restrict_fn_in(f, fn(a Q, b Q) R)

# --- AtomicFact — NormalAtomicFact / NotNormalAtomicFact (`$name(args)`) ---
prove:
    abstract_prop ok(x)
    know $ok(0)
    $ok(0)

prove:
    abstract_prop bad(x)
    know not $bad(1)
    not $bad(1)
```

## 16. `litex_object_examples`

- Category: `obj`
- System surface: `object forms`
- Purpose: Shows core object constructors and membership facts.

```litex
# Object expressions: surface syntax maps to `Obj` in `src/obj/obj.rs`. Independent blocks for copy-paste.
# IdentifierWithMod uses `::` between name parts (`MOD_SIGN`).
# Included below: Number, Tuple, Add/Sub/Mul/Div/Mod/Pow, StandardSet (sample), ListSet, SetBuilder,
# Union/Intersect/SetMinus/SetDiff, Range/ClosedRange, Proj, Cart/CartDim, FnSet (`fn`),
# TupleDim, ObjAtIndex (`[` `]`), PowerSet, Count, FnObj (via `have fn`).
# Cup/Cap: syntax in a comment (list-set distinctness checks often block short `have` demos).

# --- Obj::Number ---
prove:
    1 = 1
    1.5 = 1.5

# --- Obj::Add, Sub, Mul, Div, Mod, Pow (and unary `-` as Mul by -1) ---
prove:
    1 + 2 = 3
    3 - 1 = 2
    2 * 3 = 6
    6 / 2 = 3
    5 % 2 = 1
    2 ^ 3 = 8
    -1 + 2 = 1

# --- Obj::Tuple, parenthesized Obj ---
prove:
    (1, 2) = (1, 2)

# --- Obj::StandardSet ---
prove:
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

# --- Obj::ListSet ---
prove:
    1 $in {1, 2, 3}
    $is_finite_set({1, 2})

# --- Obj::SetBuilder (here as the rhs of `have`; membership proof needs extra `know` / forall) ---
prove:
    have s set = { z N : z > 5 }

# --- Obj::Union, Intersect, SetMinus (keyword forms); Obj::SetDiff (rhs of `have`) ---
prove:
    2 $in union({1, 2}, {2, 3})
    2 $in intersect({1, 2}, {2, 3})

prove:
    have t set = set_minus({1, 2}, {1})

prove:
    have u set = set_diff({1, 2}, {3})

# --- Obj::Range, ClosedRange (keyword forms; membership often via `know` / set equality) ---
prove:
    have r set = range(0, 10)
    have w set = closed_range(0, 1)

# --- Obj::Proj (keyword) ---
prove:
    let c set:
        c = cart(R, Q)
    proj(c, 1) = R

# --- Obj::Cart, CartDim ---
prove:
    let d set:
        d = cart(R, Q)
    $is_cart(d)
    cart_dim(d) = 2

prove:
    have f fn(x R) R
    have g set = fn(x R) R

# --- Obj::TupleDim, Obj::ObjAtIndex ---
prove:
    let e set:
        e = (2, 3)
    $is_tuple(e)
    tuple_dim(e) = 2
    e[1] = 2
    e[2] = 3

# --- Obj::PowerSet, Obj::Count ---
prove:
    {1, 2} $in power_set({1, 2, 3})
    count({1, 2, 3}) = 3

# --- Obj::Cup, Obj::Cap ---
# Surface: `cup({{a}, {b}})`, `cap({{a, b}, {b, c}})` (requires provably distinct inner sets for `have`).

# --- Axiom of choice proof step ---
prove:
    have S set

    by axiom_of_choice: set S:
        know forall A S:
            $is_nonempty_set(A)

    exist f fn(A S) cup(S) st {forall! A S: {f(A) $in A}}

# --- Obj::Identifier, Obj::FnObj (e.g. `f(0)` after `have fn f(x R) R = ...`) ---
prove:
    have fn f(x R) R = x + 1

    have fn pair_value(x Z) cart(Z, Z) = (x, x + 1)
    pair_value(0)[1] $in Z
    pair_value(0)[2] $in Z

# --- Parameterized struct references use angle brackets; fields are accessed through a struct view. ---
prove:
    struct rec<a set>:
        fld a
        fld2 a

    have r &rec<R>
    &rec<R>{r}.fld $in R
```

## 17. `litex_statement_examples`

- Category: `stmt`
- System surface: `statement forms`
- Purpose: Shows common statement forms in one reference file.

```litex
# Each block illustrates the usual mathematical reading of that statement form. Independent blocks for easy copy-paste.
# `import` / `run_file`: syntax shown in comments only (not run here).

# --- Stmt::Fact — assert a closed formula ---
prove:
    1 + 1 = 2

# --- Stmt::DefLetStmt — local names with defining properties ---
prove:
    let a R:
        a = 1
    a = 1

# --- Stmt::DefPropStmt — define a named predicate with its if and only if properties ---
prove:
    prop p(x R):
        x = x

# --- Stmt::DefAbstractPropStmt — declare a predicate symbol and arity only ---
prove:
    abstract_prop q(a)

# --- Stmt::HaveObjInNonemptySetStmt — introduce typed parameters (membership in given sets / types) ---
prove:
    have x R, y Z

# --- Stmt::HaveObjEqualStmt — introduce parameters and fix them to given values ---
prove:
    have a R = 1
    a = 1

# --- Stmt::HaveByExistStmt — name witnesses for an already known existential ---
prove:
    know exist u R st {u > 0, u < 1}
    have by exist v R st {v > 0, v < 1}: w
    w > 0

# --- Stmt::HaveFnEqualStmt — define a function by a single defining equation on its domain ---
prove:
    have fn f(x R) R = x + 1
    do_nothing

# --- Stmt::HaveFnEqualCaseByCaseStmt — piecewise definition by cases on the domain ---
prove:
    have fn g(z R) R by cases:
        case z = 2: 3
        case z != 2: 4
    do_nothing

# --- Stmt::HaveFnByInducStmt — recursive function given by a decreasing measure ---
prove:
    have fn h(a Z, b Z: a >= 0, b >= 0) R by induc abs(a) + abs(b) from 0:
        case b = 0: a
        case b > 0: h(a, b - 1) + 1

# --- Stmt::DefStructStmt — removed in this branch (record-like `struct`); see git history to restore. ---

# --- Stmt::DefAlgoStmt — computational presentation of a function (evaluation) ---
prove:
    have fn m(x N_pos) R by cases:
        case x = 1: 1
        case x != 1: 0

    algo m(x):
        case x = 1: 1
        case x != 1: 0

    eval m(1)
    m(1) = 1

# --- Stmt::ClaimStmt — stated goal with a sub-proof and lemmas ---
# (A claim may state a `forall` goal; here both goals are short tautologies so the file runs.)
prove:
    claim:
        prove:
            1 + 1 = 2
        1 + 1 = 2

    claim:
        prove:
            2 = 2
        2 = 2

# --- Stmt::KnowStmt — assume lemmas / axioms in scope ---
prove:
    know:
        1 = 1

# --- Stmt::ProveStmt — nested sub-proof (lemma) ---
prove:
    prove:
        2 = 2

# --- Stmt::ImportStmt / Stmt::RunFileStmt — module or file inclusion (syntax only here) ---
# import Nat
# run_file "./runfile2.lit"

# --- Stmt::DoNothingStmt — trivial proof step ---
prove:
    do_nothing

# --- Stmt::EvalStmt — compute a closed expression ---
prove:
    have g fn(x Z) Z

    know:
        forall x Z:
            x > 0
            =>:
                g(x) = g(x-1) + 1
        g(0) = 0
        forall x Z:
            x < 0
            =>:
                g(x) = g(x+1) - 1

    algo g(x):
        case x > 0: g(x-1) + 1
        case x = 0: 0
        case x < 0: g(x+1) - 1

    eval g(3)
    g(3) = 3

# --- Stmt::WitnessExistFact — exhibit witnesses for an existential claim ---
prove:
    witness exist x, y R st {x > y} from 1, 0:
        1 > 0

    exist a, b R st {a > b}

# --- Stmt::WitnessNonemptySet — exhibit an element to show a set is nonempty ---
prove:
    have s set

    witness $is_nonempty_set(s) from 1:
        know 1 $in s

    $is_nonempty_set(s)

# --- Stmt::ByCasesStmt — proof by cases on a finite disjunction ---
prove:
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

# --- Stmt::ByContraStmt — proof of negation from a contradiction ---
prove:
    abstract_prop p0(x, y)
    abstract_prop q0(x, y)

    know forall a, b R:
        $p0(a, b)
        =>:
            $q0(a, b)

    know not $q0(1, 2)

    by contra:
        prove:
            not $p0(1, 2)
        $p0(1, 2)
        impossible $q0(1, 2)

# --- Stmt::ByEnumerateFiniteSetStmt — Cartesian product over list-set forall params (like by for; see docs/quick_reference.md). Use `by enumerate finite_set:` then `prove:` with one forall.
prove:
    let a R:
        a $in {1, 2}

    a = 1 or a = 2

    by enumerate finite_set:
        prove:
            forall a2 {1, 2, 3}:
                a2 < 4

# --- Stmt::ByEnumerateRangeStmt — expand integer range / closed_range membership into equality cases.
prove:
    let a1 range(7, 8)

    by enumerate range: a1 $in range(7, 8)

    a1 = 7

# --- Stmt::ByInducStmt — induction on a discrete parameter ---
prove:
    abstract_prop r0(a)

    know:
        $r0(0)
        forall n Z:
            n >= 0
            $r0(n)
            =>:
                $r0(n + 1)

    by induc n from 0:
        prove:
            $r0(n)

        prove from n = 0:
            $r0(0)

        prove induc:
            $r0(n + 1)

    forall m Z:
        m >= 0
        =>:
            $r0(m)

# --- Stmt::ByForStmt — finite or bounded iteration as proof skeleton ---
prove:
    by for:
        prove:
            forall i range(0, 10):
                i < 10
        do_nothing

# --- Stmt::ByExtensionStmt — set equality by mutual inclusion ---
prove:
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

# --- Stmt::ByFnAsSetStmt — use the graph characterization of a function in a function space ---
prove:
    have fn f(x R) R = 1

    by fn as set: f

# --- Stmt::DefStructStmt — define a structure shape for future struct features ---
prove:
    abstract_prop bs(b, c, d)

    struct sq<a set>:
        b1 a
        c1 fn(x a) a
        d1 fn(x, y a) a
        <=>:
            $bs(b1, c1, d1)

# --- Stmt::ByTupleAsSetStmt — tuple / product-space reasoning on an object ---
prove:
    let u set:
        u = (2, 3)

    by tuple as set: u

# --- Stmt::ByFnSetAsSetStmt — membership of a function in a function set (graph axioms) ---
prove:
    let s set

    know:
        forall u s:
            u $in cart(R, Q, Z)
            tuple_dim(u) = 3

        forall u s:
            exist x R, y Q, z Z st {x > y, x > 2, u = (x, y, z)}

        forall x R, y Q:
            x > y
            x > 2
            =>:
                exist u s, z Z st {u = (x, y, z)}

        forall u, v s:
            u $in cart(R, Q, Z)
            v $in cart(R, Q, Z)
            u[1] = v[1]
            u[2] = v[2]
            =>:
                u = v

    by fn set as set: s $in fn(x R, y Q: x > y, x > 2) Z

    s(100, 99) = s(100, 99)
```

## 18. `macro`

- Category: `stmt`
- System surface: `macro`
- Purpose: Shows macro definitions and expansion.

```litex
macro SELF_R "R"

macro HAVE_FN "have fn"

@HAVE_FN f(x @SELF_R) @SELF_R = x

prove:
    macro SELF_Q "Q"
    @HAVE_FN g(x @SELF_Q) @SELF_Q = x

    @HAVE_FN h(x @SELF_R) @SELF_R = x

macro STRANGE "f("

forall x R:
    @STRANGE x) = f( x)
```

## 19. `matrix`

- Category: `obj`
- System surface: `matrix`
- Purpose: Shows matrix-like function objects and indexing.

```litex

prove:
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
- System surface: `restricted object`
- Purpose: Shows restricted parameter and object types.

```litex
prove:
    have f fn(x R, y Q) R 

    $restrict_fn_in(f, fn(a Q, b Q) R)

    $restrict_fn_in(f, fn(x R, y Q: x < y) R)

    have g fn(x, y R) R

    $restrict_fn_in(g, fn(x, y R: x < y, x < 0) R)

    $restrict_fn_in(g, fn(p Q, q Q) R)

prove:
    have f set
    know:
        $restrict_fn_in(f, fn(x R, y Q) R)

    f(1, 2) = f(1, 2)

prove:
    forall f fn(x R, y Q) R:
        f(1, 2) = f(1, 2)

prove:
    abstract_prop p(x)

    know:
        forall f fn(x R, y Q) R:
            $p(f)

    have f fn(x R, y Q) R
    $p(f)

prove:
    $restrict_fn_in('R(x){x}, fn(x closed_range(1, 2)) R)
    $restrict_fn_in('R(x){x + 1}, fn(x closed_range(1, 2)) R)
    $restrict_fn_in('(x R: x > 0) R {x}, fn(x N_pos) R)
    $restrict_fn_in('R(x){x}, fn(x closed_range(1, 2)) N)
```

## 21. `set_builder`

- Category: `obj`
- System surface: `set builder`
- Purpose: Shows set-builder object syntax.

```litex
let a {x R: x > 0}

a $in R
a > 0

1 $in {x R: x > 0}
```

## 22. `signed_area`

- Category: `obj`
- System surface: `tuple and determinant-style expression`
- Purpose: Shows a small geometric data expression.

```litex
have fn signed_area(x, y cart(R, R)) R = x[1] * y[2] - x[2] * y[1]

signed_area((1, 0), (0, 1)) = 1 * 1 - 0 * 0 = 1
```

## 23. `struct`

- Category: `obj`
- System surface: `struct`
- Purpose: Shows struct definitions, fields, and dependent struct views.

```litex
prove:
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

prove:
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
    
prove:
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

prove:
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

prove:
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
- System surface: `template`
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
- System surface: `template with let`
- Purpose: Shows local definitions inside templates.

```litex
template<x R>:
    let alias R:
        alias = x

\alias<2> = 2
```

## 26. `tuple_and_cart`

- Category: `obj`
- System surface: `tuple and cart`
- Purpose: Shows tuple objects and Cartesian products.

```litex
let a set:
    a = (2, 3)

$is_tuple(a)
tuple_dim(a) = 2
a[1] = 2
a[2] = 3

let b set:
    b = cart(R, Q)

$is_cart(b)
cart_dim(b) = 2
proj(b, 1) = R
proj(b, 2) = Q

forall a2 set:
    $is_cart(a2)
    =>:
        cart_dim(a2) = cart_dim(a2)

forall x cart(R, R):
    x[1] $in R
```
