# AI Operator Protocol for Litex Proofs

This protocol is suitable for a coding agent, chat model with tool access, or
an orchestrated proof-writing system. The model may propose mathematics; the
Litex verifier decides whether the submitted block is accepted.

## Required inputs

Give the AI:

1. the target theorem statement and its source-facing mathematical meaning;
2. the registered target `.lit` path;
3. the ordered natural-language proof spine;
4. the currently visible imported and local interfaces;
5. the proof journal path; and
6. the exact release commands used for session and final replay.

The AI must not begin syntax search until it can name the current DAG node and
the contract needed by its next consumer.

## Roles in one loop

| Role | Responsibility |
| --- | --- |
| Planner | Writes the proof DAG and selects one current node. |
| Interface reader | Finds the existing definition or theorem whose contract matches the mathematical move. |
| Driver | Emits exactly one current source block inside one literal outermost `try:`. |
| Observer | Reads the JSON event and classifies the earliest failing phase. |
| Journaler | Records materially distinct candidates, concise evidence, dependencies, accepted source, and the next smallest change. |
| Gatekeeper | Materializes only a contiguous accepted prefix and requires a clean registered-file runner. |

One AI can perform all six roles, but it must keep their outputs distinct.

## State machine

```text
write proof spine
      |
      v
start release -session -before target
      |
      v
wait for {event: ready}
      |
      v
send run frame containing outermost try
      |
      +---- ok:false ----> classify earliest phase
      |                         |
      |                         v
      |                  change current block only
      |                         |
      |                         +-------- back to send
      |
      +---- ok:true -----> journal accepted source without try
                                |
                                v
                       send next source block
                                |
                                v
                     materialize accepted prefix
                                |
                                v
                  clean release -runner -f target
```

Restart the session only when the process exits, the registered prefix
changes, or an already committed declaration must be replaced. A failed
outermost `try:` is not a restart condition.

## Candidate output contract

For each iteration, require the AI to return only:

- `intent`: one sentence describing the mathematical move;
- `candidate`: literal Litex without the outer `try:` wrapper;
- `dependencies`: exact earlier declarations or journal block ids;
- after verification, `diagnosis`: the earliest failing phase and decisive
  diagnostic, or `accepted`;
- `next_change`: the smallest correction, if any; and
- `reusable_lesson`: one short searchable pattern after acceptance.

Do not store hidden chain-of-thought. The journal needs reproducible decision
evidence, not an internal monologue.

## JSON-driven repair order

1. **Protocol:** confirm the event is `ready` or `block`, not
   `protocol_error`, `startup_error`, or `skipped`.
2. **Parse:** repair indentation, binder form, or unsupported statement shape.
3. **Name and type:** repair package authorization, namespace, arity,
   callability, or exact carrier.
4. **Well-definedness:** establish domains, refined carriers, nonzero
   denominators, indices, and dependent premises before proof search.
5. **Proof:** try the direct fact, native proof surface, and existing theorem
   with the exact conclusion. Add only the smallest bridge supported by the
   diagnostic.
6. **Storage/use:** after success, test that the next block can consume what
   was committed.
7. **Replay:** materialize the journal's accepted source and require clean
   top-level `ok: true` plus exit code `0`.
8. **Dependency closure:** run the strict audit separately. A strict startup
   error is a dependency-debt result, not a successful clean gate and not a
   reason to mislabel the selected theorem as disproved.

Never answer a parse or carrier error by changing the theorem's mathematics.
Never answer an `unknown` proof result by immediately introducing `trust`.

## Reusable prompt

```text
You are driving one persistent Litex project session.

Target: <registered .lit path>
Current DAG node: <one mathematical node>
Proof spine step: <one ordinary-language move>
Visible interfaces: <exact names and contracts>
Accepted journal prefix: <block ids and declarations>
Latest JSON event: <exact event or decisive trace excerpt>

Produce one materially new candidate for the current top-level source block.
Preserve the intended theorem statement. Repair the earliest failing phase.
Return intent, dependencies, literal Litex without outer try, and the smallest
expected change. Do not replay accepted blocks and do not introduce trust
unless a separately documented real blocker has been established.
```

The caller, not the model, adds the byte-framed `run` header and the literal
outermost `try:` wrapper. Keeping transport deterministic prevents prompt text
from leaking into mathematical source.

## Completion rule

The task is complete only when all of the following agree:

- natural-language proof spine;
- accepted journal source;
- materialized `.lit` source;
- persistent-session evidence;
- clean registered-file runner with `ok: true` and exit `0`; and
- trust/debt statement for the exact selected dependency route; and
- a separate strict dependency-closure result, successful or blocked at an
  exact recorded trust statement.
