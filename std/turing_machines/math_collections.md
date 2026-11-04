# Unary machine: mathematical model

## Purpose and scope

The pilot target is a genuine tape machine that computes unary successor:
input1^n, blank elsewhere, becomes1^(n+1) and halts. The theorem quantifies
over every n in native N, including0. It is a direct source construction,
not a translation of a particular textbook theorem or a complete computability
library.

## Configurations and tape updates

A configuration is a value in `cart({0,1},Z,fn(pos Z) {0,1})`. The complete
integer-indexed function is the tape; the second coordinate is its read/write
head. This representation preserves blank cells and head motion independently
of how the input was encoded. The state codes0 and1 mean scanning and halted.

`configuration(state,head,tape)` and `write_tape(tape,head,symbol)` are ordinary
functions returning actual values. A relation describing a proposed output
would not provide the configuration needed by the next simulation step.
`write_symbol` checks equality with the one written address and preserves every
other address. `configuration_coordinates` exposes the three mathematical
components for repeated consumers.

## Transition and finite execution

`increment_step(c)` checks the state, then the scanned symbol. Reading1 in
state0 moves right without writing. Reading0 writes1 and enters state1.
State1 has an identity transition, making `run(steps,c)` total for all natural
step counts. This is simulation with a supplied finite count, so no function
definition assumes that the machine eventually stops.

`is_halted(c)` is a proposition about the state. `halts(c)` is existential:
some finite execution reaches a halted configuration. It is not a total
function that predicts halting or selects a halting time for arbitrary c.

## Correctness and first halting time

The scanning invariant quantifies both a step count k and an input length n:
if k<=n then the state remains0, the head is k, and the entire tape is the
original tape. A predicate packages the universal n clause for natural
induction; it is proved, not assumed.

At k=n the scanned cell is blank. One more transition writes at n and halts.
Function extensionality proves the output tape equality at every integer
address: addresses before0 remain blank, addresses before n remain1, address
n becomes1, and later addresses remain blank. Thus the output theorem supplies
the full configuration, not just its length or a few inspected cells.

The scan invariant excludes every earlier natural halting time. The exact
configuration theorem supplies the existential witness n+1. Independently,
natural induction proves that an already halted configuration stays fixed.

## A configuration that never halts

`ones_tape` is the complete constant-one tape on Z. The source proves
`ones_tape_scan(steps,head)` for every natural step count and integer initial
head: execution produces `configuration(0,head+steps,ones_tape)`. This is a
different input from the finite unary tapes, since it has no blank cell.
`ones_tape_does_not_halt(head)` uses the scan invariant to refute every possible
finite witness to `halts`. Thus finite simulation is total while halting remains
a substantive existential property. The public `run_zero` and `run_successor`
theorems expose the two recursion equations for explicit source callers.

## Dependencies and boundaries

The signature edges run from binary symbols, integers and complete functions
to configurations. Definition edges lead through a single-cell write and the
transition to finite recursion. Proof edges run from the tape membership
cases and scan invariant to whole-tape equality, exact output and first halt.
Native natural induction and arithmetic are the visible foundations. The
constant-one scan and its nonhalting theorem reuse the same transition and
recursion equations; they do not assume a special infinite execution object.

No machine code is a new native Obj/Fact, and no transition is an unproved
assumption. Invalid state codes and negative step counts remain outside the
actual function domains. The general construction of arbitrary machines,
simulation equivalences, encodings of programs and halting undecidability
are outside this pilot.
