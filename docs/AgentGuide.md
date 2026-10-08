# Litex Agent Guide

> **Keep one live Session while repairing a proof. A normal failed statement
> does not erase the definitions and facts already accepted in that Session.
> Correct the failed statement and submit it to the same process.**

Litex builds a mathematical context statement by statement. Reusing that
context preserves both earlier proof work and the cost of loading chapter or
module dependencies. Restarting creates a new context; editing a source file
alone does not update the running process.

## See why keeping the Session matters

This intentionally artificial example uses an opaque predicate so that
arithmetic cannot prove the result automatically. `ready_at_seven` is an
explicit teaching assumption, not a proof of a mathematical theorem. Never
add an axiom merely to make a real failed proof pass.

From a directory without `litex.config`, start:

```bash
litex -lang en -session -e 'abstract_prop ready(n)'
```

Enter these three statements **one at a time in that same process**. The
transcript abbreviates the failure JSON; the receipt retains the exact output.

```text
litex> axiom ready_at_seven:
...     ? forall n N:
...         n = 7
...         =>:
...             $ready(n)
...
success
litex> $ready(8)
{"success": false, ..., "session_error": null}
litex> $ready(7)
success
```

The last success uses the fact stored by the first statement. The failed
`$ready(8)` does not clear `$ready(7)` and does not become a stored fact.
Retrying `$ready(8)` still fails. If you restart with only the same
`abstract_prop ready(n)` declaration, `$ready(7)` fails too: the new process
has the predicate's signature but lacks the old process's axiom. Replaying the
accepted statements restores that missing context.

Here is that fresh-process comparison explicitly. Start the same command
again, then enter each statement separately:

```text
litex> $ready(7)
{"success": false, ..., "session_error": null}
litex> axiom ready_at_seven:
...     ? forall n N:
...         n = 7
...         =>:
...             $ready(n)
...
success
litex> $ready(7)
success
```

The extra replay is the work a restart creates. Keep the live Session after
an ordinary failed candidate; preserve a journal so an unavoidable restart
can restore the accepted prefix. Failed candidates themselves are not part
of that prefix.

The practical comparison is:

| After a candidate fails | Next attempt |
| --- | --- |
| Keep the same Session | Earlier accepted definitions and facts are available immediately. |
| Start a fresh Session | Reload the module context and replay the accepted prefix before continuing. |

A long textbook prefix behaves the same way as this one stored fact. The
example demonstrates context retention; it does not measure a speedup or
establish automatic proof discovery.

## Use the Session as the proof-writing loop

1. Understand the intended mathematics and inspect the existing builtin,
   library and module interfaces. Load the required context once.
2. Submit one top-level statement at a time, in source order. A `claim` or
   theorem and its entire nested proof form one statement. Consume its response
   before sending the next candidate; terminate multiline input with a blank line.
3. On `success`, journal the accepted source and continue. On an ordinary
   failure with `session_error: null` followed by another `litex>` prompt,
   keep the process and repair the current statement. Failure is missing proof
   or well-definedness evidence, not proof of the proposition's negation.
4. At a coherent checkpoint, save the accepted code and run a separate clean
   file gate. Interactive context is not a substitute for a reproducible file.

**The transaction boundary is the statement, not the entire pasted input.**
A failed statement discards its own tentative parse bindings and execution
state. Successful earlier statements remain. If a frame contains several
top-level statements, its successful statements can commit even when the
frame's overall `success` is false; soft failures do not stop later statements.
Do not assume a whole candidate fragment rolled back, or blindly resubmit names
that already committed. Keep the accepted prefix in a journal outside the live
process so it can be recovered after a restart or interruption.

## Start in the intended context

Use the checked-out version's [CLI contract](cli.md). In a development checkout,
build with `cargo build --release` and use `target/release/litex`.

```bash
target/release/litex -lang en -f accepted-prefix.lit -session
```

`-f` executes its target, including the ordered registered exports through that
target, before entering the REPL. The initial run must succeed; `-session` does
not skip a failing draft file. To work on an unfinished registered file, use a
task-owned scratch module with the exact preceding imports/exports and an
empty target, then submit the target's statements in order. Keep that scratch
configuration outside the canonical module and leave its export order intact.

The current CLI has no `-before`, `-runner`, or `-compact`; do not copy those
historical recipes or introduce a literal `try:` wrapper. The current runtime
already handles each statement's commit/discard boundary.

## Restart deliberately and restore the prefix

Restart when the process exits or cannot accept input, when the loaded module
prefix must change, or when replacing an already committed declaration under
the same name requires a fresh context. A normal proof miss is not a restart
condition. Parsing/tokenization errors and hard session errors can terminate
the REPL; a stopped process cannot retain usable context for the next attempt.

Record the error, reopen the intended module context, replay the journal's
accepted statements in order, confirm their success, then retry the pending
statement. Record unexpected session termination in the source-owned blocker
notes. Do not claim that context survives process exit or that any arbitrary
internal error is recoverable in place.

## Verify the saved artifact and find the right reference

Use a clean `target/release/litex -lang en -f <file>` gate. Require exit 0 and
parsed JSON with `kind: run`, `success: true`, and `session_error: null`.
Use `-strict` when the intended artifact must exclude user axioms and trust;
the artificial axiom above is deliberately rejected in strict mode. Reserve
`-r` for an explicitly requested whole-module gate. See [CLI output](cli.md#json-output-contract).

| Need | Read |
| --- | --- |
| Language, domains, proof commands and mathematical recipes | [Manual](Manual.md) |
| First-contact authoring choices | [Learner Cheatsheet](Litex_Learner_Cheatsheet.md) |
| Small runnable examples and their assumptions | [Examples](../examples/README.md) |
| Module interfaces and chapter dependencies | The owning module's `README.md`, `math_collections.md`, and `litex.config` |
| Repository authorization and local-only boundaries | [AGENTS.md](../AGENTS.md) and the applicable repository policy skill |

Verified example and controls: [2026-10-07 receipt](../tests/tooling/acceptance/agent-session-guide-2026-10-07.json).
The explicit fresh-process replay was also rechecked with the current worktree
release build: [recheck receipt](../tests/tooling/acceptance/agent-session-guide-recheck-2026-10-07.json).
The checks cover same-process retention, a fresh-process rejection, failed
compound-statement rollback, per-statement commit in a mixed frame, hard-error
termination, and the axiom's strict-mode rejection. They change no kernel
semantics and make no agent-performance claim.
