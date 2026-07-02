```litex
# Analysis I, Chapter 2: Starting at the beginning: the natural numbers.
#
# source: Analysis I, Chapter 2.
# problem: Record the Peano-style natural-number development, addition,
# multiplication, order, induction, recursion, Euclidean division, and powers.
# proof_idea: Litex already has builtin `N`, successor as `+ 1`, arithmetic,
# order, induction, and exponentiation.  The sketch therefore keeps Tao's
# source order visible, states the source-facing facts directly, and uses
# checked arithmetic/induction proof patterns where they are informative.
# litex_code: This file is the runnable sketch for Chapter 2.
# comments: Source excerpts are kept in triple-quoted blocks.  Explanatory
# examples that are not mathematical facts about builtin `N` are recorded in
# comments or `sketch:` blocks.

"""
Definition 2.1.1. (Informal) A natural number is any element of the set
N := {0,1,2,3,4,...},
which is the set of all the numbers created by starting with 0 and then
counting forward indefinitely. We call N the set of natural numbers.
"""

# `N` is the builtin Litex set of natural numbers.  The examples below record
# the starting element and closure under successor.

sketch:
    0 $in N
    1 $in N
    forall x N:
        x + 1 $in N
 
"""
Remark 2.1.2. In some texts the natural numbers start at 1 instead of 0, but
this is a notational convention.  In this text {1,2,3,...} is called the
positive integers rather than the natural numbers.
"""

# Litex uses builtin `N_pos` for the positive natural numbers.

"""
Axiom 2.1. 0 is a natural number.
"""

# This Peano axiom is a builtin membership fact for `N`.

0 $in N

"""
Axiom 2.2. If n is a natural number, then n++ is also a natural number.
"""

# Successor is represented by `n + 1`, and builtin arithmetic keeps it in `N`.

forall n N:
    n + 1 $in N

"""
Definition 2.1.3. We define 1 to be the number 0++, 2 to be the number (0++)++, 3 to be the number ((0++)++)++, etc. (In other words,1:=0++,2:=1++,3:=2++,etc. InthistextIuse“x:=y” to denote the statement that x is defined to equal y.)
"""

# Numerals and successor arithmetic are builtin, so the source definition is
# represented by direct numeral facts rather than by rebuilding numerals.

"""
Proposition 2.1.4. 3 is a natural number.
"""

# This follows directly from the builtin natural-number numerals.

3 $in N

# Example 2.1.5 is an informal nonstandard model with wrap-around successor.
# It motivates Axiom 2.3 rather than adding a theorem about builtin `N`.

"""
Axiom 2.3. 0 is not the successor of any natural number; i.e., we have n++ ̸= 0 for every natural number n.
"""

# The successor `n+1` is positive, so it cannot equal `0`.

thm zero_is_not_successor_of_any_natural_number:
    ? forall n N:
        n + 1 != 0
    n + 1 > 0
    n + 1 != 0

"""
Proposition 2.1.6. 4 is not equal to 0.
"""

# Numeral comparisons are builtin arithmetic facts.

4 != 0

"""
Example 2.1.7. Consider a number system consisting of five numbers 0,1,2,3,4, in which the increment operation hits a “ceiling” at 4. More precisely, suppose that 0++ = 1, 1++ = 2, 2++ = 3, 3++ = 4, but 4++ = 4 (or in other words that 5 = 4, and hence 6 = 4, 7 = 4, etc.). This does not contradict Axioms 2.1,2.2,2.3. Another number system with a similar problem is one in which incrementation wraps around, butnottozero,e.g. supposethat4++=1(sothat5=1,then6=2, etc.).

"""

sketch:
    0 + 1 = 1
    1 + 1 = 2
    2 + 1 = 3

"""
Axiom 2.4. Different natural numbers must have different successors; i.e., if n, m are natural numbers and n ̸= m, then n++ ̸= m++. Equiv- alently2, if n++ = m++, then we must have n = m.
"""

# Successor is injective: subtracting `1` from equal successors gives the
# original natural numbers.

thm different_natural_numbers_have_different_successors:
    ? forall n, m N:
        n != m
        =>:
            n + 1 != m + 1
    by contra n + 1 != m + 1:
        n + 1 = m + 1
        n = (n+1) - 1 = (m+1) - 1 = m
        impossible n = m

"""
Proposition 2.1.8. 6 is not equal to 2.
"""

6 != 2

"""
Axiom 2.5 (Principle of mathematical induction). Let P(n) be any property pertaining to a natural number n. Suppose that P(0) is true, and suppose that whenever P(n) is true, P(n++) is also true. Then P(n) is true for every natural number n.
"""

# Example 2.1.9 is an informal nonstandard model using half-integers before
# integers and rationals have been constructed.  It motivates why induction is
# needed.

# Remark 2.1.10 explains the meta-logical phrase "property P(n)" and the idea
# of an axiom schema.  The Litex sketch below records this by using an
# `abstract_prop`.

# Proposition 2.1.11 is the generic induction proof template.  It is not a
# separate mathematical theorem after Axiom 2.5; the following sketch shows the
# same base-case and inductive-step pattern.

# The first sketch treats `P(n)` as an abstract proposition: only the base
# case and induction step are used.  The second sketch applies the same
# induction pattern to the concrete estimate `2^n >= n+1`.

sketch:
    abstract_prop induction_demo(n)

    claim:
        ? forall n N:
            $induction_demo(0)
            forall m N:
                $induction_demo(m)
                =>:
                    $induction_demo(m + 1)
            =>:
                $induction_demo(n)
        by induc n from 0:
            ? $induction_demo(n)

            prove from n = 0:
                $induction_demo(0)

            prove induc:
                $induction_demo(n + 1)

sketch:
    claim:
        ? forall n N:
            2 ^ n >= n + 1
        by induc n from 0:
            ? 2 ^ n >= n + 1

            2^0 = 1 >= 0 + 1

            forall m Z:
                m >= 0
                2^m >= m + 1
                =>:
                    2^m * 2^1 >= (m + 1) * 2
                    2 ^ (m + 1) = 2^m * 2^1 >= (m + 1) * 2 = (m + 1) + (m + 1) >= m + 1 + 1

"""
Assumption 2.6. (Informal) There exists a number system N, whose elements we will call natural numbers, for which Axioms 2.1-2.5 are true.
"""

# Litex's builtin `N` is the natural-number system used in this sketch.

"""
Remark 2.1.12. We will refer to this number system N as the natural number system. One could of course consider the possibility that there is more than one natural number system, e.g., we could have the Hindu- Arabic number system {0,1,2,3,...} ....
"""

# The remark is explanatory: the sketch fixes the builtin model `N` and does
# not distinguish between different concrete numeral systems.

"""
Remark 2.1.13. (Informal) One interesting feature about the natural numbers is that while each individual natural number is finite, the set of natural numbers is infinite
"""

# The formal content is that `N` is not finite.  Litex uses `finite_set` for
# finite sets, so the proof argues by contradiction from a finite cardinality.

by contra:
    ? not $is_finite_set(N)
    $is_finite_set(N)
    forall x 0...count(N):
        x $in N
    0...count(N) $subset N
    count(N) + 1 = count(N) - 0 + 1 = count(0...count(N)) <= count(N)
    impossible count(N) + 1 <= count(N)

"""
Remark 2.1.14. Note that our definition of the natural numbers is ax- iomatic rather than constructive. We have not told you what the natural numbers are (so we do not address such questions as what the numbers are made of, are they physical objects, what do they measure, etc.) - we have only listed some things you can do with them (in fact, the only operation we have defined on them right now is the increment one) and some of the properties that they have. This is how mathematics works - it treats its objects abstractly, caring only about what properties the objects have, not what the objects are or what they mean. If one wants to do mathematics, it does not matter whether a natural number means a certain arrangement of beads on an abacus, or a certain organization of bits in a computer’s memory, or some more abstract concept with no physical substance; as long as you can increment them, see if two of them are equal, and later on do other arithmetic operations such as add and multiply, they qualify as numbers for mathematical purposes (provided they obey the requisite axioms, of course). It is possible to construct the natural numbers from other mathematical objects - from sets, for instance - but there are multiple ways to construct a working model of the natural numbers, and it is pointless, at least from a mathematician’s standpoint, as to argue about which model is the “true” one - as long as it obeys all the axioms and does all the right things, that’s good enough to do maths.
"""

# This remark explains the axiomatic point of view: for the present
# development, what matters is that the objects satisfy the Peano rules and
# support the required operations, not which concrete construction realizes
# them.

"""
Proposition 2.1.16 (Recursive definitions). Suppose for each natural number n, we have some function fn : N → N from the natural numbers to the natural numbers. Let c be a natural number. Then we can assign a unique natural number an to each natural number n, such that a0 = c and an++ = fn(an) for each natural number n.
"""

# Recursive definitions are represented by `have fn ... by induc`.  The local
# `step_fn(n, x)` is the source's step function `f_n` applied to the previous
# value, and the induction definition creates the sequence `a`.

sketch:
    have c N = 3
    have fn step_fn(n N, x N) N = x + n + 1

    have fn a(n Z: n >= 0) N by induc n from 0:
        case n = 0: c
        case n > 0: step_fn(n - 1, a(n - 1))

    a(0) = c = 3
    a(1) = step_fn(0, a(0)) = step_fn(0, 3) = 4
    a(2) = step_fn(1, a(1)) = step_fn(1, 4) = 6

"""
Definition 2.2.1 (Addition of natural numbers). Let m be a natural number. To add zero to m, we define 0 + m := m. Now suppose inductively that we have defined how to add n to m. Then we can add n++ to m by defining (n++) + m := (n + m)++.
"""

# Addition is builtin.  The following equations record the recursive clauses
# from the source definition.

forall m N:
    0 + m = m

forall n, m N:
    (n + 1) + m = (n + m) + 1

"""
Lemma 2.2.2. For any natural number n, n + 0 = n.
"""

forall n N:
    n + 0 = n

"""
Lemma 2.2.3. For any natural numbers n and m, n + (m++) = (n + m)++.
"""

forall n, m N:
    n + (m + 1) = (n + m) + 1

"""
Proposition 2.2.4 (Addition is commutative). For any natural numbers n and m, n+m=m+n.
"""

# Commutativity is checked directly by builtin arithmetic.

forall n, m N:
    n + m = m + n

"""
Proposition 2.2.5 (Addition is associative). For any natural numbers a,b,c, we have (a+b)+c=a+(b+c).
"""

# Associativity is also a builtin arithmetic fact.

forall a, b, c N:
    (a + b) + c = a + (b + c)

"""
Proposition 2.2.6 (Cancellation law). Let a,b,c be natural numbers
such that a+b=a+c. Then we have b=c.
"""

# Cancellation subtracts the common summand `a` from both sides.

forall a, b, c N:
    a + b = a + c
    =>:
        b = (a + b) - a = (a + c) - a = c


# The same ring-style arithmetic identities are useful over the ambient real
# numbers, where later chapters will do most sequence estimates.

forall a, b R:
    a + b = b + a

forall a, b, c R:
    (a + b) + c = a + (b + c)

forall a, b, c R:
    a + b = a + c
    =>:
        b = (a + b) - a = (a + c) - a = c

# Commutativity and associativity also give this three-term rearrangement.

forall a, b, c R:
    (a + b) + c = (a + c) + b

"""
Definition 2.2.7 (Positive natural numbers). A natural number n is said to be positive iff it is not equal to 0. (“iff” is shorthand for “if and only if” - see Section A.1).
"""

# `N_pos` is the builtin subtype of positive natural numbers.

forall n N:
    n != 0
    =>:
        n $in N_pos

"""
Proposition 2.2.8. If a is positive and b is a natural number, then a+b is positive (and hence b + a is also, by Proposition 2.2.4).
"""

forall a N_pos, b N:
    a > 0
    b >= 0
    a + b > 0

# Equivalently, adding a natural number to a positive natural stays in `N_pos`.

forall a N_pos, b N:
    a + b $in N_pos
    a + b != 0

forall a N_pos, b N:
    b + a $in N_pos
    b + a != 0

"""
Corollary 2.2.9. If a and b are natural numbers such that a+b=0, then a=0 and b=0.
"""

# Natural numbers are nonnegative.  If their sum is zero, each term is squeezed
# between `0` and the zero sum.

forall a, b N:
    a + b = 0
    =>:
        0 <= a <= a + b
        a <= 0
        a = 0
        0 <= b <= a + b
        b <= 0
        b = 0

"""
Lemma 2.2.10. Let a be a positive number. Then there exists exactly one natural number b such that b++=a.
"""

# This is the inverse operation for successor.  Since successor is `+1`, the
# witness is `a-1`, and uniqueness follows by subtracting `1` from both sides.

claim:
    ? forall a N_pos:
        exist! b N st {b + 1 = a}
    a >= 1
    a - 1 >= 0
    a - 1 $in Z
    a - 1 $in N
    witness exist b N st {b + 1 = a} from a - 1:
        (a - 1) + 1 = a
    forall b1, b2 N:
        b1 + 1 = a
        b2 + 1 = a
        =>:
            b1 + 1 = b2 + 1
            b1 = (b1 + 1) - 1 = (b2 + 1) - 1 = b2
    exist! b N st {b + 1 = a}

"""
Definition 2.2.11 (Ordering of the natural numbers). Let n and m be natural numbers. We say that n is greater than or equal to m, and write n >= m or m <= n, iff n=m+a for some natural number a. We say that n is strictly greater than m, and write n>m or m<n, iff n=m+a for some positive natural number a.
"""

# The source defines order by additive witnesses.  Litex has builtin order, so
# the sketch uses direct order facts and displays a successor witness.

sketch:
    forall n N:
        n + 1 > n

    claim:
        ? forall n N:
            exist m N st {m > n}
        witness exist m N st {m > n} from n + 1:
            n + 1 $in N
            n + 1 > n

"""
Proposition 2.2.12 (Basic properties of order for natural numbers). Let a,b,c be natural numbers. Then order is reflexive, transitive, antisymmetric, and compatible with addition.
"""

# These are the basic algebraic properties of natural-number order.

forall a N:
    a <= a

forall a, b, c N:
    a <= b
    b <= c
    =>:
        a <= b <= c
        a <= c

forall a, b N:
    a <= b
    b <= a
    =>:
        a = b

forall a, b, c N:
    a <= b
    =>:
        a + c <= b + c

forall a, b, c N:
    a + c <= b + c
    =>:
        a = (a + c) - c <= (b + c) - c = b

# Strict order on naturals can also be recovered as a positive additive
# difference.

claim:
    ? forall a, b N:
        a < b
        =>:
            exist d N_pos st {b = a + d}
    b - a > 0
    b - a $in Z # `Z` denotes the integers.
    b - a $in N_pos
    witness exist d N_pos st {b = a + d} from b - a:
        a + (b - a) = b

"""
Proposition 2.2.13 (Trichotomy of order for natural numbers). Let a and b be natural numbers. Then exactly one of a<b, a=b, or a>b is true.
"""

# Trichotomy is stated first, then the following claims rule out overlaps
# between the three cases.

forall a, b N:
    a < b or a = b or a > b

claim:
    ? forall a, b N:
        a < b
        =>:
            not a = b
            not a > b
    a != b
    not a = b
    by contra:
        ? not a > b
        a < b < a
        a < a
        a != a
        impossible a = a

claim:
    ? forall a, b N:
        a = b
        =>:
            not a < b
            not a > b
    by contra:
        ? not a < b
        b = a < b
        b < b
        b != b
        impossible b = b
    by contra:
        ? not a > b
        a = b < a
        a < a
        a != a
        impossible a = a

claim:
    ? forall a, b N:
        a > b
        =>:
            not a < b
            not a = b
    by contra:
        ? not a < b
        a < b < a
        a < a
        a != a
        impossible a = a
    a != b
    not a = b

"""
Proposition 2.2.14 (Strong principle of induction). Let m0 be a natural number, and let P(m) be a property pertaining to an arbitrary natural number m. Suppose that for each m >= m0, if P(m') is true for all natural numbers m0 <= m' < m, then P(m) is true. Then P(m) is true for all natural numbers m >= m0.
"""

# Strong induction is represented by `by strong_induc`: in the inductive step,
# all earlier cases are available, not just the immediately preceding one.

sketch:
    abstract_prop strong_induction_demo(n)

    claim:
        ? forall n N:
            $strong_induction_demo(0)
            forall m N:
                forall y N:
                    y <= m
                    =>:
                        $strong_induction_demo(y)
                =>:
                    $strong_induction_demo(m + 1)
            =>:
                $strong_induction_demo(n)
        by strong_induc n from 0:
            ? $strong_induction_demo(n)

            prove from n = 0:
                $strong_induction_demo(0)

            prove strong_induc:
                forall y N:
                    y <= n
                    =>:
                        $strong_induction_demo(y)
                $strong_induction_demo(n + 1)

# Remark 2.2.15 notes that strong induction is usually applied with
# `m0 = 0` or `m0 = 1`.  The formal strong-induction pattern is shown above.

"""
Definition 2.3.1 (Multiplication of natural numbers). Let m be a natural number. To multiply zero to m, define 0*m:=0. Suppose inductively that n*m has been defined. Then define (n++)*m := (n*m)+m.
"""

# Multiplication is builtin as `*`.  The sketch records the recursive clauses
# from the source definition.

sketch:
    forall m N:
        0 * m = 0

    forall n, m N:
        (n + 1) * m = n * m + m

"""
Lemma 2.3.2 (Multiplication is commutative). Let n,m be natural numbers. Then n*m=m*n.
"""

forall n, m N:
    n * m = m * n

"""
Lemma 2.3.3. If n and m are natural numbers, then n*m=0 iff at least one of n,m is equal to zero. In particular, if n and m are both positive, then nm is positive.
"""

# The zero-product direction uses `or`; the positive-product conclusion says
# multiplication preserves membership in `N_pos`.

forall n, m N:
    n * m = 0
    =>:
        n = 0 or m = 0

forall n, m N_pos:
    n * m $in N_pos

"""
Proposition 2.3.4 (Distributive law). For any natural numbers a,b,c, we have a(b+c)=ab+ac and (b+c)a=ba+ca.
"""

forall a, b, c N:
    a * (b + c) = a * b + a * c
    (b + c) * a = b * a + c * a

"""
Proposition 2.3.5 (Multiplication is associative). For any natural numbers a,b,c, we have (a*b)*c=a*(b*c).
"""

forall a, b, c N:
    (a * b) * c = a * (b * c)

"""
Proposition 2.3.6 (Multiplication preserves order). If a,b are natural numbers and c is positive, then a<b iff ac<bc.
"""

# Multiplying by a positive natural number preserves strict order.

forall a, b N, c N_pos:
    a < b
    =>:
        a * c < b * c

"""
Corollary 2.3.7 (Cancellation law). Let a,b,c be natural numbers such that ac=bc and c is non-zero. Then a=b.
"""

# Multiplicative cancellation divides both sides by the common positive factor.

forall a, b N, c N_pos:
    a * c = b * c
    =>:
        a = (a * c) / c = (b * c) / c = b

# Remark 2.3.8 describes cancellation as "virtual division" in preparation for
# rationals.  The checked cancellation statement is the corollary immediately
# above.

"""
Proposition 2.3.9 (Euclidean algorithm). Let n be a natural number, and let q be a positive natural number. Then there exist natural numbers m,r such that 0 <= r < q and n = mq + r.
"""

# The reusable predicate records that `m` and `r` are the quotient and
# remainder of dividing `n` by the positive modulus `q`.

prop is_euclidean_division(n N, q N_pos, m N, r N):
    0 <= r
    r < q
    n = m * q + r

# Proof idea: fix `q` and induct on `n`.  The base case uses quotient `0` and
# remainder `0`.  In the successor step, if `r+1 < q`, keep the quotient and
# increment the remainder; otherwise `r+1 = q`, reset the remainder to `0` and
# increment the quotient.

claim:
    ? forall q N_pos, n N:
        exist m, r N st {$is_euclidean_division(n, q, m, r)}
    by induc n from 0:
        ? exist m, r N st {$is_euclidean_division(n, q, m, r)}

        prove from n = 0:
            witness exist m, r N st {$is_euclidean_division(0, q, m, r)} from 0, 0:
                0 <= 0
                0 < q
                0 = 0 * q + 0
                $is_euclidean_division(0, q, 0, 0)

        prove induc:
            have by exist m, r N st {$is_euclidean_division(n, q, m, r)}: m, r
            0 <= r
            r < q
            n = m * q + r
            by cases:
                ? exist m1, r1 N st {$is_euclidean_division(n + 1, q, m1, r1)}
                case r + 1 < q:
                    witness exist m1, r1 N st {$is_euclidean_division(n + 1, q, m1, r1)} from m, r + 1:
                        0 <= r + 1
                        r + 1 < q
                        n + 1 = (m * q + r) + 1
                        (m * q + r) + 1 = m * q + (r + 1)
                        n + 1 = m * q + (r + 1)
                        $is_euclidean_division(n + 1, q, m, r + 1)
                case r + 1 >= q:
                    r + 1 <= q
                    r + 1 = q
                    witness exist m1, r1 N st {$is_euclidean_division(n + 1, q, m1, r1)} from m + 1, 0:
                        0 <= 0
                        0 < q
                        n + 1 = (m * q + r) + 1
                        (m * q + r) + 1 = m * q + (r + 1)
                        m * q + (r + 1) = m * q + q
                        m * q + q = (m + 1) * q + 0
                        n + 1 = (m + 1) * q + 0
                        $is_euclidean_division(n + 1, q, m + 1, 0)

forall n N, q N_pos:
    exist m, r N st {$is_euclidean_division(n, q, m, r)}

# Litex also has a builtin remainder operation `%`; a positive modulus keeps
# the remainder in the interval `[0, b)`.

forall a Z, b N_pos:
    0 <= a % b < b
    (a - a % b) % b = 0

# The natural-number version is the Chapter 2 special case of the same
# builtin remainder interface.

forall a N, b N_pos:
    0 <= a % b < b
    (a - a % b) % b = 0

# Remark 2.3.10 paraphrases the quotient/remainder meaning of Proposition
# 2.3.9 and notes that number theory begins here.  The formal
# quotient-remainder content is represented by Euclidean division above.

"""
Definition 2.3.11 (Exponentiation for natural numbers). Let m be a natural number. We define m^0:=1, and recursively define m^(n++) := m^n * m.
"""

# Exponentiation is builtin as `^`.  As with addition and multiplication, the
# sketch records the recursive clauses from the source definition.

sketch:
    forall m N:
        m^0 = 1

    forall m, n N:
        m^(n + 1) = m^n * m

```
