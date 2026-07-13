# Typical Examples

This page collects a few small but representative Litex examples. The point is
not that these are hard theorems. The point is to show the same interface at
several scales: write a fact, let Litex match it against the context, and keep
growing a checked mathematical object.

Litex source code stays the same across languages, but CLI output supports
localized JSON keys and explanatory labels with `litex -lang <code> ...`.
See [CLI](https://litexlang.com/doc/cli) for the supported language codes.

## 1. A Divisibility Proof by Witnesses

The smallest useful pattern can already be a real proof. We define divisibility
by a concrete existential witness, then prove that every multiple of `8` is a
multiple of `2`.

```litex
prop can_be_divided_by_8(x Z):
    exist d Z st {x = 8 * d}

prop can_be_divided_by_2(x Z):
    exist d Z st {x = 2 * d}

claim:
    ? forall x Z:
        $can_be_divided_by_8(x)
        =>:
            $can_be_divided_by_2(x)
    obtain d from exist d Z st {x = 8 * d}
    witness exist e Z st {x = 2 * e} from 4 * d:
        x = 8 * d
        8 * d = 2 * (4 * d)

witness exist d Z st {8 = 1 * d} from 8
$can_be_divided_by_8(8)
$can_be_divided_by_2(8)
```

The conclusion is not a command about a proof state. It is the mathematical
fact we want. `obtain` opens the witness in the first definition, and `witness`
constructs the witness required by the second definition.

The accepted claim carries an explanation like this:

```json
{
  "result": "success",
  "type": "proved claim",
  "why_verified": {
    "type": "claim forall proof"
  }
}
```

Both predicate names have definitions. The only new mathematical construction
is the witness `4 * d`; the last equality is checked by arithmetic.

Litex also supports the named-theorem route used by many formal systems:

```litex
thm add_one_after_two:
    ? forall x R:
        x = 2
        =>:
            x + 1 = 3
    x + 1 = 2 + 1 = 3

by thm add_one_after_two(2)
2 + 1 = 3
```

This is useful for source-local cite facts, long results, or parameter-sensitive
theorems. The distinctive Litex style is that routine local reasoning can stay
as direct factual lines.

When a claim is accepted, inspect its witness choices and the facts they use.
Here the proof has no trusted premise: it explicitly transforms a witness for
divisibility by `8` into one for divisibility by `2`.

## 2. Structured Algebra

Litex can also define structured mathematical objects in a set-theoretic style.
The next example defines the group property, packages it as a `struct`, and then
defines subgroup and normal-subgroup predicates.

```litex
prop GroupProperty(s nonempty_set, inv fn(x s) s, op fn(x, y s) s, e s):
    forall x, y, z s:
        op(x, op(y, z)) = op(op(x, y), z)
    forall x s:
        op(e, x) = x
        op(x, e) = x
    forall x s:
        op(x, inv(x)) = e
        op(inv(x), x) = e

struct Group<s nonempty_set>:
    inv fn(x s) s
    op fn(x, y s) s
    e s
    <=>:
        $GroupProperty(s, inv, op, e)

macro G "&Group<s>{g}"

prop is_subgroup(s nonempty_set, g &Group<s>, h power_set(s)):
    @G.e $in h
    forall a, b s:
        a $in h
        b $in h
        =>:
            @G.op(a, b) $in h
    forall a s:
        a $in h
        =>:
            @G.inv(a) $in h

prop is_normal_subgroup(s nonempty_set, g &Group<s>, h power_set(s)):
    $is_subgroup(s, g, h)
    forall x, a s:
        a $in h
        =>:
            @G.op(@G.op(x, a), @G.inv(x)) $in h

prop is_left_coset_with_representative(s nonempty_set, g &Group<s>, h power_set(s), x s, c power_set(s)):
    forall y s:
        =>:
            y $in c
        <=>:
            exist a s st {a $in h, y = @G.op(x, a)}

prop is_in_left_coset_by_representative(s nonempty_set, g &Group<s>, h power_set(s), x, y s):
    exist a s st {a $in h, y = @G.op(x, a)}

prop is_left_coset(s nonempty_set, g &Group<s>, h power_set(s), c power_set(s)):
    exist x s st {$is_left_coset_with_representative(s, g, h, x, c)}

prop is_group_quotient_set(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s))):
    q = {c power_set(s): $is_left_coset(s, g, h, c)}

claim:
    ? forall s nonempty_set, g &Group<s>, h power_set(s):
        exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}
    witness exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)} from {c power_set(s): $is_left_coset(s, g, h, c)}:
        $is_group_quotient_set(s, g, h, {c power_set(s): $is_left_coset(s, g, h, c)})
        claim:
            ? forall q1, q2 power_set(power_set(s)):
                $is_group_quotient_set(s, g, h, q1)
                $is_group_quotient_set(s, g, h, q2)
                =>:
                    q1 = q2
            q1 = {c power_set(s): $is_left_coset(s, g, h, c)}
            {c power_set(s): $is_left_coset(s, g, h, c)} = q2
            q1 = q2

template<s nonempty_set>:
    have fn group_quotient by exist!:
        ? forall g &Group<s>, h power_set(s):
            exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}

prop is_quotient_product_coset(s nonempty_set, g &Group<s>, h power_set(s), c1 power_set(s), c2 power_set(s), c3 power_set(s)):
    forall x, y s:
        $is_left_coset_with_representative(s, g, h, x, c1)
        $is_left_coset_with_representative(s, g, h, y, c2)
        =>:
            $is_left_coset_with_representative(s, g, h, @G.op(x, y), c3)

prop quotient_product_representatives_equal(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s)), c1, c2 q, x1, x2, y1, y2 s, out1, out2 q):
    out1 = out2

prop quotient_product_well_defined(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s))):
    forall c1, c2 q, x1, x2, y1, y2 s, out1, out2 q:
        $is_left_coset_with_representative(s, g, h, x1, c1)
        $is_left_coset_with_representative(s, g, h, x2, c1)
        $is_left_coset_with_representative(s, g, h, y1, c2)
        $is_left_coset_with_representative(s, g, h, y2, c2)
        $is_left_coset_with_representative(s, g, h, @G.op(x1, y1), out1)
        $is_left_coset_with_representative(s, g, h, @G.op(x2, y2), out2)
        =>:
            $quotient_product_representatives_equal(s, g, h, q, c1, c2, x1, x2, y1, y2, out1, out2)

prop is_quotient_multiplication(s nonempty_set, g &Group<s>, h power_set(s), q power_set(power_set(s)), quotient_mul fn(c1, c2 q) q):
    forall c1, c2 q:
        $is_quotient_product_coset(s, g, h, c1, c2, quotient_mul(c1, c2))

thm group_left_cancel:
    ? forall s nonempty_set, g &Group<s>, a, b, c s:
        @G.op(a, b) = @G.op(a, c)
        =>:
            b = c
    $GroupProperty(s, @G.inv, @G.op, @G.e)
    @G.op(@G.inv(a), a) = @G.e
    @G.op(@G.e, b) = b
    @G.op(@G.e, c) = c
    @G.op(@G.op(@G.inv(a), a), b) = @G.op(@G.e, b) = b
    @G.op(@G.op(@G.inv(a), a), b) = @G.op(@G.inv(a), @G.op(a, b)) = @G.op(@G.inv(a), @G.op(a, c)) = @G.op(@G.op(@G.inv(a), a), c) = @G.op(@G.e, c) = c
    b = c

thm group_inv_inv:
    ? forall s nonempty_set, g &Group<s>, a s:
        @G.inv(@G.inv(a)) = a
    $GroupProperty(s, @G.inv, @G.op, @G.e)
    @G.op(@G.inv(a), @G.inv(@G.inv(a))) = @G.e
    @G.op(@G.inv(a), a) = @G.e
    @G.op(@G.inv(a), @G.inv(@G.inv(a))) = @G.op(@G.inv(a), a)
    by thm group_left_cancel(s, g, @G.inv(a), @G.inv(@G.inv(a)), a)
```

There is no inheritance hierarchy hidden here. The carrier set, operations, and
relations are visible. A group object gives access to `@G.inv`, `@G.op`, and
`@G.e`; subgroup and normality are stated as relations among the carrier, the
group structure, and the subset.


## 3. A Proof Shape: Local Assumptions

The next example shows a small proof block. The side conditions are written in
the premise of the `forall`, so the proof is conditional on exactly the facts
displayed above the `=>:`.

```litex
claim:
    ? forall x R:
        x + 3 = 10
        =>:
            x = 7
    x = (x + 3) - 3 = 10 - 3 = 7
```

The proof follows the classroom algebra move: subtract the same number from
both sides, simplify, and store the result as a checked fact.

## 4. Matrix And Scientific Objects

Litex also needs to handle the objects that appear in routine scientific and
engineering mathematics. Matrices are ordinary objects with indexed entries and
evaluable operations.

```litex
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]

have m matrix(R, 2, 2) = [[1, 0], [0, 1]]

m $in fn (x1 N_pos, x2 N_pos: x1 <= 2, x2 <= 2) R

eval m ++ m
eval [[2, 0], [0, 2]] -- [[1, 0], [0, 1]]
eval [[1, 2], [0, 1]] ** [[1, 0], [1, 1]]
eval 3 *. [[1, 2], [4, 5]]
eval [[2, 0], [0, 2]] ^^ 2
eval m ** m
eval 2 *. m
eval [[1 / 2, 1 / 3], [0, 1]] ** [[1, 0], [1 / 6, 1 / 2]]
eval (1 / 3) *. [[3, 6], [9, 12]]
```

This surface is intentionally close to ordinary classroom and engineering
notation: introduce a matrix, inspect entries, then evaluate addition,
subtraction, multiplication, scalar multiplication, powers, and exact rational
entries. The same direction should extend to linear algebra, probability,
optimization, numerical methods, and scientific derivations.
