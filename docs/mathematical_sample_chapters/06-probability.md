# Expectation and conditional probability

A fair coin pays zero on one outcome and one on the other. Its expected
payoff is one half, even though a single toss never pays one half. Expectation
combines possible values with their weights; it is not a prediction that one
of the possible values must equal the average.

We will derive the affine law for two-point expectation, compute variance,
and then examine a different operation: conditioning on new evidence. A
coherent finite probability table will make Bayes' formula concrete and keep
its denominator condition visible.

## Outcomes, values and weights

Let a random variable have values $X_1,X_2$ on two outcomes, with probabilities
$p_1,p_2\ge0$ and $p_1+p_2=1$. Define

$$\mathbb E[X]=p_1X_1+p_2X_2.$$

The [complete source](../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit)
represents a two-coordinate vector as a function on the positive indices
at most two. Its probability predicate constrains the weight vector, while
the values are allowed to be arbitrary real numbers. This is an excerpt
using that previously declared vector carrier.

<!-- litex-source: ../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit -->
<!-- litex:skip-test -->
```litex
prop is_probability_vector2(p two_point_vector):
    p(1) >= 0
    p(2) >= 0
    p(1) + p(2) = 1

have fn expectation2(values, probs two_point_vector) R = values(1) * probs(1) + values(2) * probs(2)
```

For constants $a,b$ and two value vectors $X,Y$, the affine combination has
coordinates $(aX+bY)_i=aX_i+bY_i$. Expanding the weighted sum gives

$$
\begin{aligned}
\mathbb E[aX+bY]
&=p_1(aX_1+bY_1)+p_2(aX_2+bY_2)\\
&=a(p_1X_1+p_2X_2)+b(p_1Y_1+p_2Y_2)\\
&=a\mathbb E[X]+b\mathbb E[Y].
\end{aligned}
$$

This algebra uses neither positivity nor normalization of the weights.
The source therefore proves `expectation2_affine` for arbitrary real weight
vectors. To interpret the result as an expectation, we additionally establish
the probability-vector conditions. The distinction gives the theorem its
natural generality without treating arbitrary weights as probabilities.

## Variance measures spread around the mean

For a probability vector, define

$$\operatorname{Var}(X)=p_1(X_1-\mathbb E[X])^2+p_2(X_2-\mathbb E[X])^2.$$

In the fair-coin example $X=(0,1)$ and $p=(1/2,1/2)$. Thus
$\mathbb E[X]=1/2$ and

$$\operatorname{Var}(X)=\tfrac12(0-\tfrac12)^2+
\tfrac12(1-\tfrac12)^2=\tfrac14.$$

The complete source checks these values. Nonnegative probabilities ensure
each weighted square is nonnegative. Normalization ensures that the mean
has the familiar behavior under adding a constant.

The same squared-distance idea explains a small statistics result in the
source. For observations $a,b,c$, let $m=(a+b+c)/3$ and
$S(r)=(a-r)^2+(b-r)^2+(c-r)^2$. Write
$a-r=(a-m)+(m-r)$, and similarly for $b,c$. Expanding, the mixed terms sum
to zero because $(a-m)+(b-m)+(c-m)=0$. Hence

$$S(r)=S(m)+3(r-m)^2\ge S(m).$$

The arithmetic mean minimizes total squared error. For data $(1,2,5)$,
$m=8/3$, $S(m)=26/3$, and $S(2)=10=26/3+4/3$.
The source proves the decomposition and its minimizing consequence; the
nonnegative remainder explains why the inequality is true.

## Conditioning changes the reference population

For events $A,B$ with $P(B)>0$, conditional probability is

$$P(A\mid B)=\frac{P(A\cap B)}{P(B)}.$$

If $P(A)>0$ as well, the definition of $P(B\mid A)$ gives
$P(A\cap B)=P(B\mid A)P(A)$. Substitution yields Bayes' formula:

$$P(A\mid B)=\frac{P(B\mid A)P(A)}{P(B)}.$$

The standalone code below includes the source's scalar interfaces, the whole
substitution proof and its concrete numerical use. The functions require
positive evidence to make division valid. The theorem consumes the joint
identity as a premise; it does not assume every tuple of real numbers
describes a probability model.

```litex
have fn conditional_probability(joint, evidence R: evidence > 0) R = joint / evidence

have fn bayes_posterior(prior, likelihood, evidence R: evidence > 0) R = likelihood * prior / evidence

thm bayes_rule:
    ? forall prior, likelihood, evidence, joint R:
        evidence > 0
        joint = likelihood * prior
        =>:
            conditional_probability(joint, evidence) = bayes_posterior(prior, likelihood, evidence)
    conditional_probability(joint, evidence) = joint / evidence
    bayes_posterior(prior, likelihood, evidence) = likelihood * prior / evidence
    joint / evidence = likelihood * prior / evidence

1 / 4 = (3 / 4) * (1 / 3)

release thm bayes_rule(1 / 3, 3 / 4, 1 / 2, 1 / 4)
conditional_probability(1 / 4, 1 / 2) = bayes_posterior(1 / 3, 3 / 4, 1 / 2)

conditional_probability(1 / 4, 1 / 2) = 1 / 2

bayes_posterior(1 / 3, 3 / 4, 1 / 2) = 1 / 2
```

## A coherent example

Here is a finite model that realizes those numbers. Its four cells are
nonnegative and sum to one.

| | $B$ | Not $B$ | Total |
| --- | ---: | ---: | ---: |
| $A$ | $1/4$ | $1/12$ | $1/3$ |
| Not $A$ | $1/4$ | $5/12$ | $2/3$ |
| Total | $1/2$ | $1/2$ | $1$ |

The prior probability of $A$ is $1/3$. Among cases in $A$, the proportion
also in $B$ is $(1/4)/(1/3)=3/4$. Restricting attention to cases in $B$
instead gives $(1/4)/(1/2)=1/2$ for $A$. The posterior differs from the
prior because the evidence changes which population is being normalized.
This table is a mathematical interpretation of the checked scalar example;
the source does not construct a general event probability space.

## Exercises

1. For a zero-or-one payoff with probability $p$ of one, compute its mean
   and variance, assuming $0\le p\le1$.
2. In the table, calculate $P(B\mid\text{not }A)$.
3. Why does the scalar function `joint / evidence` require more conditions
   before it can be interpreted as a probability?

## Answers

1. The mean is $p$. The variance is
   $(1-p)p^2+p(1-p)^2=p(1-p)$.
2. It is $(1/4)/(2/3)=3/8$. Together with $3/4$ on $A$, it recovers
   $P(B)=(3/4)(1/3)+(3/8)(2/3)=1/2$.
3. Positive evidence makes division defined, but arbitrary real inputs can
   give a ratio outside $[0,1]$. A probability model also supplies
   $0\le P(A\cap B)\le P(B)\le1$ and consistency with its other events.

## Continue reading

The [source guide](../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/README.md)
maps the finite expectation, variance, least-squares and Bayes developments.
This sample does not develop sigma-algebras, integration or general
conditional expectation. Its concrete distributions and scalar identities
make the weighting and normalization steps visible before those abstractions.

[Previous](05-number-theory.md) · [Contents](README.md) · [Next: geometry](07-geometry.md)

