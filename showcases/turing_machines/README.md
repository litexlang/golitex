# A unary increment Turing machine

This showcase defines a fixed deterministic machine on a complete two-way
binary tape and proves its correctness for every natural input length. State
0 scans right across ones. At a blank it writes one and enters state1. State1
is absorbing; subsequent simulation steps leave the configuration unchanged.
The write-and-halt transition uses a stay move, leaving the head on the written cell.

Read [main.lit](main.lit) from configurations and single-cell writes through
the scan invariant, exact unary output and the nonhalting constant-one tape.
The local caller's `validation/litex.config` imports this showcase with:

```ini
[import]
TM = ".."
[alias]
tm = TM::main
[export]
main = "./main.lit"
```

`Symbol={0,1}` and `Configuration=cart(Symbol,Z,fn(pos Z) Symbol)` are actual
carriers. Configuration coordinates are state, head position and tape.
`configuration(state,head,tape)` constructs a configuration; `write_tape`
updates exactly one tape position. `increment_step(c)` is the transition and
`run(steps,c)` iterates it by natural recursion. It does not assume termination.

`unary_tape(n)` has ones exactly at integer positions0 through n-1 and blanks
everywhere else, including negative positions. `unary_initial(n)` starts in
state0 with its head at0. In particular n=0 is the all-blank tape.

| Theorem after `tm::` | Result |
| --- | --- |
| `unary_scan_prefix(steps,n)` | For steps<=n, the state is0, the head is at steps, and the complete tape is unchanged. |
| `unary_tape_append(n)` | Writing1 at n transforms the entire input tape into `unary_tape(n+1)`. |
| `unary_increment_correct(n)` | `run(n+1,unary_initial(n))=configuration(1,n,unary_tape(n+1))`. |
| `unary_increment_first_halt(n,steps)` | For steps<=n the state is0; at n+1 it is1. |
| `unary_increment_halts(n)` | Supplies an actual finite halting time through the `halts` predicate. |
| `halted_runs_are_fixed(steps,c)` | A configuration satisfying `is_halted` remains unchanged for any natural number of further steps. |
| `ones_tape_scan(steps,head)` | The complete constant-one tape stays in state0 and moves the head to head+steps for every natural step count. |
| `ones_tape_does_not_halt(head)` | That constant-one configuration has no finite halting time. |

`ones_tape` is an actual function on all of Z. Unlike the finite unary inputs,
it contains no blank cell. `run_zero(c)` and `run_successor(steps,c)` expose
the simulation equations as callable theorems.

The [independent caller](validation/main.lit) exercises generic n and concrete
empty/nonempty inputs. It explicitly releases imported carrier and callable
definitions before consuming the theorems; those releases are part of its
actual import contract. Run the saved source and caller with:

```bash
target/release/litex -strict -lang en -f showcases/turing_machines/main.lit
target/release/litex -strict -lang en -f showcases/turing_machines/validation/main.lit
```

Focused results and source hashes are recorded in [acceptance.json](validation/acceptance.json).
[negative_cases.json](validation/negative_cases.json) contains final-assertion
controls for early halting, wrong output, invalid state, negative step count
and a false halting claim about the constant-one tape.
They are checked after the positive caller in one live Session.

There are no source axioms, trust statements or kernel changes. The proof uses
native sets, complete functions, natural induction and integer arithmetic.
This showcase covers this fixed machine; universal simulation and undecidability
are further work. No Lean replay is claimed.
