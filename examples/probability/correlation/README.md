# Finite real correlation

This strict consumer imports finite correlation from std/probability. The
source function is defined only when both actual variances are strictly
positive; it supplies no value for a zero-variance input.

```ini
[import std]
prob = probability

[export]
main = "./main.lit"
```

This complete independently checked excerpt consumes self-correlation:

```litex
thm positive_variance_self_correlation:
    ? forall Omega set,space &prob::main::FiniteProbabilitySpace<Omega>,X fn(k space.carrier) R:
        \prob::main::finite_variance<Omega,space>(X)>0
        =>:
            \prob::main::finite_correlation<Omega,space>(X,X)=1
    release thm prob::main::finite_correlation_self(Omega,space,X)
```

## Interfaces

The ordinary source function finite_correlation<Omega,space>(X,Y) has two
template parameters and two ordinary arguments. Both X and Y are complete real
functions on the supplied finite space's actual carrier. Each variance must be
strictly positive. The result is the real value Cov(X,Y)/sqrt(Var(X)*Var(Y)).
This is the population/probability-space definition, not a sample estimator.
There is one fixed real contract, without a complex or zero-variance overload.

Eight named source theorems in prob::main provide formula, symmetry, self=1,
square<=1, absolute value<=1, both interval bounds, covariance0 to correlation0
and the converse. Every theorem retains both positivity guards; self needs the
single variance positive. Formula is finite_correlation_formula/4, symmetry
finite_correlation_symmetric/4 and self finite_correlation_self/3. Bounds are
finite_correlation_square_bound/4, finite_correlation_abs_bound/4 and
finite_correlation_bounds/4. The zero directions are
finite_correlation_zero_from_covariance/4 and
finite_covariance_zero_from_correlation/4.

The proof reuses existing covariance symmetry/self/square bound, principal real
square roots and ordinary scalar arithmetic. An internal checked positive-root
fact supplies denominator nonzero evidence during source definition. Private
scalar helpers normalize the square bound and transport the absolute bound to
both interval inequalities. No native object, rule, search permission, trust,
source axiom, AST/state or compiler change is introduced.

## Actual callers and boundaries

The caller constructs a fair bit X on {0,1}, EX=1/2 and Var(X)=1/4. Correlation
with itself is1; with -X it is-1, including the reverse order and attained
absolute bound. A separate uniform three-point space uses U(k)=k-1 and
V(k)=(k-1)^2. Their means are0 and2/3, variances2/3 and2/9, and covariance0;
correlation0 is checked with both variances positive. This is no independence
claim. A constant on the fair space has variance0. The Dirac identity on {0,1}
has variance0 despite distinct values at its actual two points. Both remain
outside correlation's formation domain.

Negative fixtures require accepted prefixes and exactly one final refusal.
They isolate zero variance on either argument, undefined Dirac correlation,
missing positivity/zero premises, nonreal/partial/wrong-domain samplers and
false strict bounds or signs. The checker also runs actual callers under
archive and shared-data installed layouts without LITEX_STD_PATH and compares
all std/WiX files and component references.

```bash
python3 examples/probability/correlation/check.py --binary target/release/litex --output-dir tmp/2026-10-27/correlation-check
```

This adds finite real correlation laws. Distributions, random-variable
independence, statistical estimators, measure probability, full probability
Lean compilation and release/MSI validation remain separate work.


Acceptance on2026-10-28 passes20 focused checks: source113/97thms, ten generic
statements,177 actual statements, one isolated README,14 refusal controls and
two installed layouts. std/WiX80 files and references agree. After correcting
three guarded-assignment phase labels to value_well_defined, four unchanged
cold positive outputs were verified by source hash and reused; all14 controls
and both installed callers reran. The pinned1.1.6-beta executable belongs to
this ongoing task; no claim is made for concurrent compiler changes.
