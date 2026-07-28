# Typical Examples

This page collects a few small but representative Litex examples. The point is
not that these are hard theorems. The point is to show the same interface at
several scales: write a fact, let Litex match it against the context, and keep
growing a checked mathematical object.

## 1. Matching And Substitution

The smallest useful pattern is a syllogism. We introduce a set of humans, an
object `Socrates` in that set, an abstract predicate `mortal`, and a general
fact saying that every human is mortal.

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

# Assumption injection: trusted input for this example, not a checked proof.
know forall x human:
    $mortal(x)

$mortal(Socrates)
```

The final line is not a command about a proof state. It is the mathematical fact
we want. Litex sees that the known `forall` fact has the same predicate shape,
checks that `Socrates $in human`, and substitutes `Socrates` for `x`.

The accepted fact can also carry an explanation like this:

```json
{
  "result": "success",
  "type": "AtomicFact",
  "line": 7,
  "stmt": "$mortal(Socrates)",
  "verified_by": {
    "type": "cite forall fact",
    "cite_source": {
      "line": 4
    },
    "cited_stmt": "forall x human:\n    $mortal(x)"
  }
}
```

Here `abstract_prop mortal(x)` only declares the predicate vocabulary. The
`know` line is assumption injection: it stores the general rule as trusted input
for this example, without proving that rule. Once `$mortal(Socrates)` is
accepted, it becomes part of the verified context for later facts, but its proof
still depends on the injected assumption.

Litex also supports the named-theorem route used by many formal systems:

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

thm all_humans_are_mortal:
    prove:
        forall x human:
            $mortal(x)
    know $mortal(x)

by thm all_humans_are_mortal(Socrates)
$mortal(Socrates)
```

This is useful for standard-library facts, long results, or parameter-sensitive
theorems. The distinctive Litex style is that routine local reasoning can stay
as direct factual lines.

When `verified_by` says a line was accepted by citing a `forall`, check where
that `forall` came from. If it came from `know`, the output explains a
conditional proof route relative to an explicit assumption; it does not certify
that the assumed `forall` was proved by Litex.

Similarly, `result: "success"` on the `KnowStmt` line means the assumption was
stored, not proved.

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
    prove:
        forall s nonempty_set, g &Group<s>, h power_set(s):
            exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)}
    witness exist! q power_set(power_set(s)) st {$is_group_quotient_set(s, g, h, q)} from {c power_set(s): $is_left_coset(s, g, h, c)}:
        $is_group_quotient_set(s, g, h, {c power_set(s): $is_left_coset(s, g, h, c)})

template<s nonempty_set>:
    have fn group_quotient as set:
        prove:
            forall g &Group<s>, h power_set(s):
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
    prove:
        forall s nonempty_set, g &Group<s>, a, b, c s:
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
    prove:
        forall s nonempty_set, g &Group<s>, a s:
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


## 3. A Proof Shape: Infinitely Many Primes

The next example shows a proof block rather than only definitions. The `know`
block records background number-theory facts used by the final argument: a
product is divisible by every factor below the bound, every number at least `2`
has a prime divisor, and the finite product is at least the endpoint.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

# Background facts for this final proof block.
know:
    forall a, k N_pos:
        k <= a
        =>:
            product(1, a, 'N_pos(x){x}) % k = 0

    forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    forall a N_pos:
        a <= product(1, a, 'N_pos(x){x})

claim forall! a N_pos: 2 <= a => exist k N_pos st {k > a, $prime(k)}:
    2 <= a <= product(1, a, 'N_pos(x){x}) <= product(1, a, 'N_pos(x){x}) + 1
    have by exist k N_pos st {$prime(k), (product(1, a, 'N_pos(x){x}) + 1) % k = 0}: k
    by cases k > a:
        case k <= a:
            product(1, a, 'N_pos(x){x}) % k = 0
            (product(1, a, 'N_pos(x){x}) + 1) % k = (product(1, a, 'N_pos(x){x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, 'N_pos(x){x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

The proof follows the classical Euclid move. For a bound `a`, take a prime
divisor `k` of `1 * 2 * ... * a + 1`. If `k <= a`, then the product is divisible
by `k`, so the product plus `1` has remainder `1` modulo `k`, contradicting the
choice of `k`. Therefore `k > a`, and it is the witness for a larger prime.

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
