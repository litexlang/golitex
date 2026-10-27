# Finite event probability consumers

main.lit constructs the six-outcome uniform probability space through the
generic std constructor. It checks even1/2, evidence >3 with probability1/2,
intersection1/3, and the actual conditional probability2/3. Its explicit tuple
equation exposes the constructed fields in a registered module.
contracts/main.lit independently imports all33 generic source theorem
contracts and both bundled constructors, preceded by one proved numeric closure
claim. readme/main.lit checks the isolated std README excerpt. No user trust,
axioms or predicates with omitted definitions are introduced.

The conditional/Bayes contracts retain arbitrary finite supplied spaces,
all event domains and positive-evidence/positive-prior guards. The point mass at1 on {0,1} has nonempty null event {0}; its probabilities,
independence and legal conditioning are checked. Conditioning on this zero
evidence is rejected. The two-branch total-probability formula is checked on the actual dice, with
conditional values2/3 and1/3 and total1/2. Either null branch is rejected.
Zero-event independence, both complement laws and conditional monotonicity
have independent generic contracts and actual callers.

negative/ contains31 final-only controls after a verified prefix: wrong
values (including bundled conditional probability), outside/empty/infinite
carriers, wrong arities, omitted positivity/independence/subset/disjointness,
and empty-event conditioning. Missing-premise controls test obligations,
not countermodels. Both uniform function and bundled constructor reject empty
and infinite sample carriers. Dirac controls also reject outside points and
events, empty/infinite carriers, wrong values and actual null conditioning.

Run python3 examples/probability/finite_events/check.py. It checks source,
contracts, README, controls, std/WiX equality and both installed std layouts.
