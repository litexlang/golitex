# Litex Agent Guide

<a id="session-first"></a>

> **Required workflow: when writing or repairing Litex code, open `-session`
> and keep the same live process throughout the iterative loop. Never rerun
> the whole file from the beginning whenever you add a few new lines.**
>
> **An ordinary failed statement does not erase the definitions and facts
> already accepted in that Session. Correct only the failed statement and
> submit it to the same process, then continue from the accepted context.**

**Litex is well suited to interactive work with AI.** An agent can propose one
mathematical statement, inspect verification feedback, and revise its next
input while the Session keeps accepted definitions and facts available. This
gives the agent a repeated propose, check, revise, and continue loop.

Litex builds a mathematical context statement by statement. Reusing that
context preserves both earlier proof work and the cost of loading chapter or
module dependencies. Restarting creates a new context; editing a source file
alone does not update the running process.

Load the accepted prefix once, then submit new statements to that live Session.
Use clean full-file runs for a baseline, coherent checkpoints, and final
verification; they must not replace the Session as the per-candidate loop.

## See why keeping the Session matters

From a directory without `litex.config`, start with one accepted declaration:

```bash
litex -lang en -session -e 'have a R = 2'
```

Enter the next statements **one at a time in that same process**. The failure
JSON is abbreviated:

```text
litex> a = 3
{"run_result": "failure", ..., "session_terminated": false, "termination": null}
litex> a + 1 = 3
success
```

The failed `a = 3` does not remove the accepted declaration or its fact `a = 2`.
The next statement uses that fact immediately. Do not repeat the declaration
or restart the process to make the next attempt.

Compare with two independent commands:

```bash
litex -lang en -e 'have a R = 2'
litex -lang en -e 'a + 1 = 3'
```

The first succeeds; the second fails because its new process has no declaration
of `a`. A restart requires loading or replaying the accepted code. Rerunning a
whole file supplies that context again, but repeats every earlier statement.
Keep the live Session for the inner loop instead.

| After a candidate fails | Next attempt |
| --- | --- |
| Keep the same `-session` | Earlier accepted definitions and facts are available immediately. |
| Start a fresh process | Reload the module context and replay the accepted prefix before continuing. |

A long textbook prefix follows the same rule as `a = 2`. This example uses no
user `trust` or `axiom`; it demonstrates context retention, not a measured
speedup or automatic proof discovery. Save the accepted source outside the
process so an unavoidable restart can recover it.

## Use the Session as the proof-writing loop

1. Understand the intended mathematics and inspect the existing builtin,
   library and module interfaces. Open `-session` and load the required
   accepted context once.
2. Submit one top-level statement at a time to that same live Session, in
   source order. A `claim` or theorem and its entire nested proof form one
   statement. Consume its response before sending the next candidate;
   terminate multiline input with a blank line.
3. On the REPL's plain-text `success` response (not a JSON field), journal the
   accepted source and continue. On an ordinary
   failure with `session_terminated: false`, `termination: null` followed by another `litex>` prompt,
   keep the process and repair the current statement. Failure is missing proof
   or well-definedness evidence, not proof of the proposition's negation.
4. At a coherent checkpoint or final verification, save the accepted code and
   run a separate clean file gate while keeping the authoring Session open.
   Do not run the whole file again after each new statement or small batch.
   Interactive context is not a substitute for a reproducible file.

**The transaction boundary is the statement, not the entire pasted input.**
A failed statement discards its own tentative parse bindings and execution
state. Successful earlier statements remain. If a frame contains several
top-level statements, its successful statements can commit even when the
frame's overall `run_result` is `"failure"`; soft failures do not stop later statements.
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

When deliberately adopting a verified rebuilt Litex executable, save the
accepted source first, then restart and replay it. Replacing the binary on
disk does not update the process that is already running. A build or an
ordinary proof miss alone is not a reason to discard the live Session.

Record the error, reopen the intended module context, replay the journal's
accepted statements in order, confirm their success, then retry the pending
statement. Record unexpected session termination in the source-owned blocker
notes. Do not claim that context survives process exit or that any arbitrary
internal error is recoverable in place.

## Verify the saved artifact and find the right reference

Use a clean `target/release/litex -lang en -f <file>` gate. Require exit 0 and
parsed JSON with `kind: run`, `run_result: "success"`, and `session_terminated: false`, `termination: null`.
Use `-strict` when the intended artifact must exclude user axioms and trust;
the accepted declaration and successful follow-up above also pass a clean
strict file check. Omit the rejected candidate from that saved file. Reserve
`-r` for an explicitly requested whole-module gate. See [CLI output](cli.md#json-output-contract).

| Need | Read |
| --- | --- |
| Language, domains, proof commands and mathematical recipes | [Manual](Manual.md) |
| First-contact authoring choices | [Learner Cheatsheet](Litex_Learner_Cheatsheet.md) |
| Small runnable examples and their assumptions | [Examples](../examples/README.md) |
| Module interfaces and chapter dependencies | The owning module's `README.md`, `math_collections.md`, and `litex.config` |
| Repository authorization and local-only boundaries | [AGENTS.md](../AGENTS.md) and the applicable repository policy skill |

Session boundaries include retaining accepted statements in the same process,
replaying them in a fresh process, rolling back a failed compound statement,
committing each successful statement in a mixed frame, stopping on hard errors,
and rejecting axioms in strict mode. These rules separate ordinary
repair from deliberate restart; the example makes no agent-performance claim.
