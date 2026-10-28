# Finite pushforward probability

A function turns a finite probability space into a distribution on its actual
image. This example follows six equiprobable dice outcomes through their parity,
then collapses them to one value and checks an image containing a zero-mass point.
The same source construction returns a probability-space value in each case.

The event probability is the source probability of its inverse image. The
following complete generic caller is checked independently of the examples:

```litex
thm event_pullback_formula:
    ? forall Omega set,space &prob::main::FiniteProbabilitySpace<Omega>,Target set,F fn(k space.carrier) Target,A power_set(fn_range(F)):
        \prob::main::finite_pushforward_event_probability<Omega,space,Target,F>(A) = space.prob(preimage_set(F,A))
    release thm prob::main::finite_pushforward_event_formula(Omega,space,Target,F,A)
```

The map is a complete unary function on space.carrier. Target may be infinite;
the new carrier is fn_range(F), and its event domain is power_set(fn_range(F)).
The source proves finiteness, nonemptiness, normalization, nonnegativity and
disjoint additivity before constructing the bundled probability space.

In [main.lit](main.lit), parity(k)=k%2 sends the dice to {0,1}, with probability
1/2 at each value. The two fibers are {2,4,6} and {1,3,5}; the singleton theorem
turns each fiber probability into the corresponding image probability. The
constant map always(k)=7 has image {7} and mass1 there, so injectivity and
surjectivity onto the ambient Target are unnecessary.

A Dirac source on {0,1}, concentrated at0, is mapped by observed(k)=k.
The pushed carrier remains {0,1}: point1 belongs to the image and has mass0.
The image is therefore not restricted to positive-mass outcomes.

| Location | Checked mathematical content |
| --- | --- |
| [main.lit](main.lit) | Dice parity, a constant many-to-one map, and a Dirac null image |
| [contracts/main.lit](contracts/main.lit) | Seven theorem signatures, function type, bundled type and defining tuple |
| [readme/main.lit](readme/main.lit) | The isolated generic inverse-image formula above |
| [negative/expected.json](negative/expected.json) | Wrong masses, removed null image, outside-image events, and invalid map/source contracts |

The source names finite_pushforward_event_probability and
finite_pushforward_probability_space have fixed four-parameter template
contracts, with respectively one event argument and no ordinary arguments.
This finite construction does not supply countable/measure probability,
expectation transport, or random-variable independence.
