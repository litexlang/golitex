# A Python agent loop over one Litex Session

This example makes one property of Litex's AI interaction loop observable:
an agent can inspect a rejected statement, revise its next input, and keep
earlier accepted definitions available in the same process. The deterministic
Python driver stands in for an agent's tool loop and reads real CLI responses.

From the repository root, build the current executable once and run:

```bash
cargo build --release
python3 examples/agent_session_demo/run.py
```

The program starts `litex -lang en -strict -session -e 'have a R = 2'`, then
submits one top-level statement per REPL response:

```litex
have b R = a + 1
# b = 99 is submitted here and rejected.
have c R = b + 1
have d R = c + 1
have f R = d + 1
```

It checks the rejected statement's `statement_result`, `why_failed.goal`, and
`session_terminated: false`, then checks that the dependent `c` declaration
succeeds without replaying `a` or `b`. A fresh process given only `c` fails
because `b` is undefined. A soft failure makes the eventual Session exit code
`1`, although the REPL remains usable until exit. After each acceptance, the
driver appends the source to one `accepted.lit` journal; it never appends the
rejected trial. That file gets one clean `-strict -f` check at the end.

For comparison, the program starts a fresh `-e` process for each next step and
replays the growing accepted prefix. With `N` dependent steps, that verifies
the steps `1 + 2 + … + N = N(N + 1)/2` times; the live Session verifies each
new step once (`N` checks). The inner-loop count ratio is `(N + 1)/2`.
The output separately reports initial prefix loads and excludes the deliberate
rejection and final file gate from that ratio. This is a count of checks under
the shown workflow, not a measured speedup or a claim about AI proof quality.

The script uses Python's standard library and a self-cleaning temporary
directory. Its only generated `.lit` file is the accepted source used for the
final gate; no project configuration or repository file is changed by a run.
For an actual long task, keep the accepted-source journal in a persistent
task-owned location so it can be replayed after the driver itself stops.
