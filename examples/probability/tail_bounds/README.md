# Finite probability tail bounds

This strict source consumer checks Markov and Chebyshev inequalities on actual
finite probability spaces. Import the library through the installed std path:

```ini
[import std]
prob = probability

[export]
main = "./main.lit"
```

The following complete excerpt consumes Chebyshev without a nonnegative-sampler
or positive-variance assumption:

```litex
thm chebyshev_for_any_real_observable:
    ? forall Omega set,space &prob::main::FiniteProbabilitySpace<Omega>,X fn(k space.carrier) R,a R+:
        space.prob(\prob::main::finite_deviation_tail_event<Omega,space>(X,a)) <= \prob::main::finite_variance<Omega,space>(X)/a^2
    release thm prob::main::finite_chebyshev_tail_bound(Omega,space,X,a)
```

## Source interfaces

All names are in prob::main. Both event constructors have two template parameters
Omega,space and two ordinary arguments X,a. X is a complete real-valued function
on the supplied space's actual carrier. Constructors accept any real a and
return power_set(space.carrier):

- finite_upper_tail_event(X,a) is exactly {k in carrier : X(k)>=a}.
- finite_deviation_tail_event(X,a) is exactly {k in carrier : abs(X(k)-EX)>=a}.

The inequalities require a in R+. finite_markov_event_bound(Omega,space,X,A,a)
requires X>=0 on the whole carrier and X>=a on A. It gives P(A)<=EX/a.
finite_chebyshev_event_bound(Omega,space,X,A,a) requires abs(X-EX)>=a on A
and gives P(A)<=Var(X)/a^2. Both allow empty and nonempty null events.
The four-argument finite_markov_tail_bound and finite_chebyshev_tail_bound
construct their respective events. Markov retains global nonnegativity;
Chebyshev permits signed X and variance0.

Named, explicitly event-valued source functions let generic theorem headers
use the actual native set builders through a declared power-set return type.
Their defining equalities are checked by independent imported contracts. No
extra carrier premise, native object, rule, strategy or trust is introduced.
Direct raw-set probability comparison headers remain outside this acceptance.

## Actual callers and boundaries

main.lit constructs the fair space on {0,1}, with X(k)=k, EX=1/2 and Var(X)=1/4.
Its native upper tail at1 has probability1/2, attaining Markov. The absolute
centered tail at1/2 has probability1, attaining Chebyshev. The sampler -X has
mean-1/2 and variance1/4 and still satisfies Chebyshev despite its negative value
at1. A Dirac space at1 has a nonempty centered tail containing0 with probability0
and variance0. The caller also checks empty supplied events, an actually empty
native upper tail at2, and legal event construction at zero/negative thresholds.

The focused checker passes20 CLI checks: source103/89thms, six contracts,117
actual statements, one README statement,14 refusal controls and two installed
layouts. The std/WiX payload has80 matching files and unique references.
It requires full positive prefixes and exactly one final
refusal in each negative fixture. Controls cover nonpositive inequality
thresholds, missing Markov nonnegativity, missing event bounds, nonreal/partial/
wrong-domain samplers, outside events and false strict bounds. Installed archive
and shared-data layouts run the same actual caller without LITEX_STD_PATH.
The checker also compares the std payload to WiX files and component references.

Run from the repository root:

```bash
python3 examples/probability/tail_bounds/check.py --binary target/release/litex --output-dir tmp/2026-10-27/tail-bounds-check
```

This is finite source mathematics. It does not supply countable/measure
probability, distributions, random-variable independence, limit laws, statistics,
full probability Lean compilation or release/MSI validation.
