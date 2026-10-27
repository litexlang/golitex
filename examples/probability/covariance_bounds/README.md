# Finite covariance and variance bounds

This project checks the six bound/zero/parallelogram interfaces in
std/probability over its unchanged finite real probability-space contract.
All new interfaces take Omega,space,X,Y; the two zero-variance interfaces
consume the appropriate variance0 premise. The square and variance bounds
include zero variance and require no independence.

The generic import has this complete interface example:

```litex
thm covariance_square_example:
    ? forall Omega set,space &prob::main::FiniteProbabilitySpace<Omega>,X,Y fn(k space.carrier) R:
        \prob::main::finite_covariance<Omega,space>(X,Y)^2 <= \prob::main::finite_variance<Omega,space>(X)*\prob::main::finite_variance<Omega,space>(Y)
    release thm prob::main::finite_covariance_square_bound(Omega,space,X,Y)
```

Configure the std import as prob = probability under [import std]. The
contracts project calls all six new theorems independently. main.lit constructs
a genuine uniform space on {0,1}, computes EX=1/2 and Var(X)=1/4, and uses
Y=2X+1 with covariance1/2 and variance1. Thus Cov(X,Y)^2=Var(X)Var(Y)=1/4.
Var(X+X)=1 attains its upper bound2Var(X)+2Var(X).

The Dirac space at1 uses the observable k on {0,1}. It has variance0 while
taking different values at its two points. Both zero-variance covariance
interfaces apply to another real observable perturbed at the null point.
There is no claim that variance0 implies everywhere constancy or independence.

Eight controls reject missing zero-variance premises, complex/partial/wrong-
domain samplers, a strict covariance bound, omission of the factor2 in the
variance bound and a strict variance bound at equality. Each checks only the
last statement is rejected after a wholly accepted prefix.

Run python3 examples/probability/covariance_bounds/check.py --output-dir <task-output>.
The checker verifies strict source, generic/actual/README callers, controls,
std/WiX equality and both installed layouts. No Lean replay or full-release
coverage is claimed.

All14 focused CLI checks pass: four positive projects, eight refusal controls
and two installed layouts. The source has97 top-level statements/85 thms;
this project's actual example has90 statements and its generic caller has six.
The std/WiX payload and unique component references match at80 files.
