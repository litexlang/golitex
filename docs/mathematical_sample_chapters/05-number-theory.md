# Integer equations and Bezout witnesses

Does the equation $84x+30y=18$ have an integer solution? What about the
same equation with target $19$? Trying pairs one at a time obscures the
reason these questions have different answers.

The decisive information is a common divisor together with a way of
expressing it as an integer linear combination. We will prove both
directions of the resulting solvability test, construct a concrete solution,
and identify exactly which existence result is assumed in its input.

## Divisibility contains a witness

For integers $d,n$, the statement $d\mid n$ means that some integer $k$
satisfies $n=dk$. It is an existence statement. Its witness can be reused:
if $b=ak$ and $c=bm$, then $c=a(km)$, so $a\mid c$.

The following standalone example from the
[complete source](../../showcases/math_concepts_in_litex/3_number_theory/main.lit)
contains the definition and the whole transitivity proof.

```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divisibility_is_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    b = a * k
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)
```

`obtain` retrieves witnesses available from the premises. `witness` supplies
the new one and checks its equation. The definition itself proves no
particular instance of divisibility. It also permits $0\mid0$, with witness
$0$; positivity will be required separately for our gcd certificate.

## Common divisors survive linear combinations

If $d\mid a$ and $d\mid b$, write $a=dp$ and $b=dq$. For arbitrary
integers $x,y$,

$$ax+by=(dp)x+(dq)y=d(px+qy).$$

Thus $d\mid(ax+by)$, with explicit witness $px+qy$. This simple identity
is the necessity half of the solvability test. It also helps certify that a
proposed common divisor is the greatest one.

The source's gcd certificate makes all the data that later arguments need
visible. This is its complete definition.

<!-- litex-source: ../../showcases/math_concepts_in_litex/3_number_theory/main.lit -->
<!-- litex:skip-test -->
```litex
prop is_gcd_certificate(a, b, d Z):
    d > 0
    $divides_by(d, a)
    $divides_by(d, b)
    forall common Z:
        common > 0
        $divides_by(common, a)
        $divides_by(common, b)
        =>:
            $divides_by(common, d)
    exist x, y Z st {d = a * x + b * y}
```

The condition on positive common divisors says that each divides $d$.
Since $d>0$, this also makes each such divisor no larger than $d$.
The final line is Bezout data. We are not proving in this chapter that every
pair of integers admits such a certificate; we prove what follows from a
supplied certificate and build one for $(84,30)$.

## Certifying six

Euclidean division gives

$$84=2\cdot30+24,\qquad 30=24+6,\qquad24=4\cdot6.$$

Back substitution yields $6=30-(84-2\cdot30)=-84+3\cdot30$.
The number $6$ is positive and divides both $84$ and $30$, with witnesses
$14$ and $5$. If a positive integer divides both inputs, the
linear-combination result says it divides $-84+3\cdot30=6$.
Finally, $(-1,3)$ supplies the Bezout coefficients. Every clause of the
certificate is therefore established for this concrete pair.

## Solvability in both directions

**Theorem.** Given a certificate for $a,b,d$ as above, the equation
$ax+by=c$ has an integer solution if and only if $d\mid c$.

For necessity, take a solution $(x,y)$. Since $d$ divides $a$ and $b$,
it divides their combination $ax+by=c$.

For sufficiency, take Bezout coefficients $u,v$ with $d=au+bv$.
The divisibility premise supplies an integer $k$ with $c=dk$.
Then

$$c=dk=(au+bv)k=a(uk)+b(vk).$$

The pair $(uk,vk)$ is the required solution. The proof gives a construction,
not only a yes-or-no conclusion. Here are its core steps from the source
theorem, after its certificate and divisibility premises have been introduced.

<!-- litex-source: ../../showcases/math_concepts_in_litex/3_number_theory/main.lit -->
<!-- litex:skip-test -->
```litex
    obtain u, v from exist u, v Z st {d = a * u + b * v}
    obtain k from $divides_by(d, c)
    d = a * u + b * v
    c = d * k = (a * u + b * v) * k = a * (u * k) + b * (v * k)
    witness $linear_diophantine_soluble(a, b, c) from u * k, v * k:
        a * (u * k) + b * (v * k) = c
```

For target $18$, take $k=3$, giving $x=-3$ and $y=9$.
Indeed $84(-3)+30(9)=-252+270=18$. For target $19$, every left-hand
side is divisible by $6$, but $19$ is not. Thus no integer solution exists.

The same witness viewpoint extends to congruence: $a\equiv b\pmod m$
means $m>0$ and $m\mid a-b$. Two congruences can be added because the
two divisibility witnesses add. The source proves this compatibility using
the same elementary arithmetic of witnesses.

## Exercises

1. Construct a solution of $84x+30y=42$ using the same certificate.
2. Prove that $84x+30y=15$ has no integer solution.
3. Starting from one solution of $84x+30y=18$, find infinitely many
   solutions. You do not need to prove your family contains every solution.

## Answers

1. Since $42=6\cdot7$, scale $(-1,3)$ by $7$: $(x,y)=(-7,21)$.
2. The left side is divisible by $6$ whereas $15$ is not. Necessity rules
   out a solution.
3. For every integer $t$, set $x=-3+5t$ and $y=9-14t$.
   The change in the left side is $84\cdot5t-30\cdot14t=0$, so its
   value remains $18$. Different values of $t$ give different pairs.

## Continue reading

The [source guide](../../showcases/math_concepts_in_litex/3_number_theory/README.md)
describes the concrete certificate and congruence theorem. A general
Euclidean algorithm and Chinese remainder theorem are further topics.
The certificate interface here is proof-facing: it does not introduce a
new globally selected gcd function.

[Previous](04-analysis.md) · [Contents](README.md) · [Next: probability](06-probability.md)

