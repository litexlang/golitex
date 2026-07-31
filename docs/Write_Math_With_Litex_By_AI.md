# Write Math with Litex by AI

Formalizing mathematics is not a one-shot translation from an idea to a
finished proof. The productive unit of work is a small mathematical move,
tested in a persistent verifier session and preserved as experience before the
next move begins.

This guide describes the workflow that emerged while formalizing Chapters 1
and 2 of *Concrete Mathematics*. It applies both to defining mathematical
concepts and to proving facts about them.

The central principle is:

> Produce two artifacts: a clean mathematical file and a durable record of how
> that file became verifiable.

The `.lit` file contains the mathematics a reader should see. The proof-block
journal contains materially different attempts, decisive verifier evidence,
accepted blocks, and reusable lessons. A final successful proof should not
erase the failed attempts that taught the writer how Litex actually works.

A conventional edit-run loop often has weak memory:

1. generate a large candidate;
2. run it;
3. see an error;
4. replace the candidate;
5. forget why the previous form failed.

That is especially costly for an AI agent. The same wrong assumption can
return later in the file: that a recursive function unfolds deeply, that
mathematical positivity automatically creates an `N+` term, or that a function
accepted in a proposition can be reused inside a new checked definition.

The Litex workflow turns each attempt into explicit evidence:

```text
mathematical spine
        |
        v
one outermost try block
        |
   +----+----+
   |         |
 failure   success
   |         |
diagnose   preserve accepted source
   |         |
smallest     reusable lesson
repair       |
   +----+----+
        |
        v
next source-order block
        |
        v
clean file checkpoint
```

This does not guarantee that an agent will never repeat a mistake. It makes
repetition less likely by giving the next decision a searchable, verifier-based
memory instead of only a rewritten final answer.

### A thirty-second preview: one failed Hanoi calculation

The Tower of Hanoi move count satisfies

```text
H(0) = 0
H(n) = 2 H(n - 1) + 1   for n > 0.
```

An AI can model this correctly and still make its first verification mistake.
The original candidate defined the function and immediately asked Litex to
evaluate three recursive layers:

```text
try:
    have fn hanoi_moves(n N) N by induc n from 0:
        case n = 0: 0
        case n > 0: 2 * hanoi_moves(n - 1) + 1

    hanoi_moves(3) = 7
```

The definition itself verified, but the outer transaction returned
`unknown result` for the last line and therefore committed nothing. The
mathematical idea was not wrong. The mistaken assumption was that a concrete
recursive call would deeply normalize by itself. The smallest repair was to
expose the stored equation one layer at a time:

<!-- litex:skip-test -->

```litex
have fn hanoi_moves(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: 2 * hanoi_moves(n - 1) + 1

hanoi_moves(0) = 0
hanoi_moves(1) = 2 * hanoi_moves(0) + 1 = 1
hanoi_moves(2) = 2 * hanoi_moves(1) + 1 = 3
hanoi_moves(3) = 2 * hanoi_moves(2) + 1 = 7
```

The clean `.lit` file keeps only the accepted calculation. The journal also
keeps the rejected direct evaluation, its exact diagnostic, and the rule
“unfold recursive functions one stored equation at a time.” Later, the
planar-region recurrence used that rule on its first attempt. That transfer
from one failure to a later success is the whole workflow in miniature.

## The four layers

### 1. Write the mathematical spine first

Before writing Litex, state the shortest honest mathematical route.

For a concept, record:

- what mathematical thing is being introduced;
- whether later code uses it as a value, function, relation, structure, or
  theorem;
- its exact domain and codomain;
- one immediate use that the interface must support.

For a proof, record:

- the few meaningful mathematical moves;
- the existing interfaces that justify those moves;
- the smallest local bridge the verifier might need.

This prevents verifier feedback from silently changing the mathematics. A
count-valued function must not become an integer-valued function merely because
subtraction is easier over `Z`. A source-defined function must not become a
`prop` merely because a relational encoding is easier to state.

#### Example: preserve the meaning of a region-count function

The source introduces `B(n)`, the maximum number of regions made by `n` bent
lines. Later mathematics must evaluate `B(3)` and state a closed-form theorem
about `B(n)`. The downstream-use sentence is therefore:

> Introduce one `N`-valued function that callers apply as
> `bent_line_regions(n)`; keep the polynomial as a theorem about that function.

That sentence rules out two tempting shortcuts. A relation such as
`prop has_bent_line_count(n, value)` would force every caller to carry an
extra candidate value. Changing the codomain to `Z` would make subtraction
easier but would misrepresent a count.

The first apparently natural definition was:

```text
have fn bent_line_regions(n N) N = 2 * n^2 - n + 1
```

Litex rejected it because the subtraction-heavy expression was not verified
to lie in return carrier `N`. The proof difficulty must not decide what the
object is. The interface card remained:

- ordinary meaning: a nonnegative region count;
- semantic role: function;
- Litex form: `have fn`;
- exact carrier: `N -> N`;
- use probe: `bent_line_regions(3) = 16`;
- specification: `B(n) = 2n^2 - n + 1`.

The accepted construction used a carrier-preserving recurrence:

<!-- litex:skip-test -->

```litex
have fn bent_line_regions(n N) N by induc n from 0:
    case n = 0: 1
    case n > 0: bent_line_regions(n - 1) + 4 * (n - 1) + 1

bent_line_regions(0) = 1
bent_line_regions(1) = bent_line_regions(0) + 4 * 0 + 1 = 2
bent_line_regions(2) = bent_line_regions(1) + 4 * 1 + 1 = 7
bent_line_regions(3) = bent_line_regions(2) + 4 * 2 + 1 = 16
```

Only after the function and use probe were stable did proof work begin. Its
mathematical spine was short: prove the base value, unfold one recurrence
step, substitute the induction hypothesis, and normalize the polynomial. The
spine preserved both the intended function and the intended theorem even when
verification later exposed a clean-replay performance problem.

### 2. Keep one persistent verification session

Build the release binary once:

```text
cargo build --release
```

For a registered target file, start one process:

```text
target/release/litex -compact -session -before path/to/current-file.lit
```

`-before` loads the configured project prefix strictly before the target,
excludes the target's current contents, and enters the target file's
environment. Submit the target statements in source order.

Wrap each candidate theorem, definition, or small related fragment in one
literal outermost transaction:

```text
try:
    <candidate source>
```

A successful transaction commits its declarations and facts to the live
session. A failed transaction rolls back only that candidate. Repair and
resubmit the current block in the same process; do not reload the whole project
after every ordinary failure.

The machine-readable session transport is length-delimited:

```text
run <id> <utf8-byte-count>
<literal Litex source>
```

The `run` frame is the transport layer. The outermost `try:` inside it is the
Litex transaction boundary. See [CLI: Session Command](cli.md#session-command)
for the complete protocol.

Use `-session -f <file>` when the intended starting state includes that
registered file and later work should continue from it. For constructing or
repairing the file itself, `-session -before <file>` is the safer default
because it does not preload the draft being replaced.

#### Example: repair block 2 without replaying block 1

Suppose the target is the first Concrete Mathematics chapter. Start one
process:

```text
target/release/litex -compact -session -before \
  scripts/textbooks_drafts/Concrete-Mathematics/chapter01-recurrent-problems.lit
```

After the `ready` event, submit the function definition as block `H001`:

```text
run H001 <bytes>
try:
    have fn hanoi_moves(n N) N by induc n from 0:
        case n = 0: 0
        case n > 0: 2 * hanoi_moves(n - 1) + 1
```

The successful block commits `hanoi_moves` to the session. Now submit the
short evaluation as block `H002`:

```text
run H002 <bytes>
try:
    hanoi_moves(3) = 7
```

This block fails, but `try:` discards only `H002`. The loaded project prefix
and the accepted definition from `H001` remain alive. There is no reason to
restart the verifier or resend the definition. Record the failure, then send
only the repair:

```text
run H003 <bytes>
try:
    hanoi_moves(0) = 0
    hanoi_moves(1) = 2 * hanoi_moves(0) + 1 = 1
    hanoi_moves(2) = 2 * hanoi_moves(1) + 1 = 3
    hanoi_moves(3) = 2 * hanoi_moves(2) + 1 = 7
```

`H003` succeeds in the same process. The speed benefit is not that `try:`
makes proof search faster; it is that the expensive prefix and every earlier
accepted target block survive a local mistake. If block 20 fails, repair block
20—not blocks 1 through 19.

The example also shows why raw multiline input and Litex transactions are
different layers. The outer `run H003 <bytes>` header tells the process how
many UTF-8 bytes belong to this request. The inner `try:` tells Litex to commit
all statements atomically or roll all of them back.

### 3. Journal before editing the mathematical file

Initialize one persistent JSON journal for the task. Before submitting a
candidate, record its intent and exact source. After Litex responds, record the
result before repairing the candidate or editing `.lit`.

A compact block record looks like this:

```json
{
  "id": "B004",
  "source_order": 4,
  "intent": "evaluate the recursive Hanoi function at 3",
  "dependencies": ["B001:hanoi_moves"],
  "attempts": [
    {
      "candidate": "hanoi_moves(3) = 7",
      "result": "failed",
      "verifier_evidence": "unknown result: hanoi_moves(3) = 7",
      "diagnosis": "the recursive definition did not normalize through several layers",
      "next_change": "expose one stored recursive equation at each input"
    }
  ],
  "accepted_litex": "hanoi_moves(0) = 0\nhanoi_moves(1) = 2 * hanoi_moves(0) + 1 = 1\nhanoi_moves(2) = 2 * hanoi_moves(1) + 1 = 3\nhanoi_moves(3) = 2 * hanoi_moves(2) + 1 = 7",
  "reusable_lesson": "evaluate recursive functions one stored equation at a time",
  "status": "accepted_unmaterialized"
}
```

Record decision evidence, not hidden chain-of-thought. The journal should make
five things recoverable:

1. the mathematical purpose of the block;
2. the materially different candidates that failed;
3. the first decisive verifier evidence;
4. the smallest change that produced an accepted block; and
5. the lesson or dependency later blocks should reuse.

Do not record identical retries, formatting-only edits, secrets, or enormous
raw traces. Store the decisive excerpt and, when necessary, a path to a larger
artifact.

The journal is the staging source of truth. Do not patch accepted source into
the target file immediately. First mark it `accepted_unmaterialized`; then
continue testing the next source-order block in the same session.

#### Example: the failure becomes input to the next theorem

The Hanoi journal entry does more than preserve an embarrassing first
attempt. It changes how the next proof is generated. The following source
theorem defines `U(n) = H(n) + 1` and proves
`U(n) = 2 U(n - 1)`.

The first candidate jumped directly from the definition of `U` to a rewrite
inside addition:

```text
shifted_hanoi_moves(n)
    = hanoi_moves(n) + 1
    = 2 * hanoi_moves(n - 1) + 1 + 1
    = 2 * shifted_hanoi_moves(n - 1)
```

The verifier rejected the middle step. The previous journal lesson suggested
the smallest next change: materialize the exact recursive value before asking
Litex to rewrite it inside a larger arithmetic context.

<!-- litex:skip-test -->

```litex
have fn shifted_hanoi_moves(n N) N = hanoi_moves(n) + 1

thm shifted_hanoi_recurrence:
    ? forall n N+:
        shifted_hanoi_moves(n) = 2 * shifted_hanoi_moves(n - 1)
    hanoi_moves(n) = 2 * hanoi_moves(n - 1) + 1
    shifted_hanoi_moves(n)
        = hanoi_moves(n) + 1
        = 2 * hanoi_moves(n - 1) + 1 + 1
        = 2 * (hanoi_moves(n - 1) + 1)
        = 2 * shifted_hanoi_moves(n - 1)
```

The journal should record that local equality as the accepted bridge and say
why it exists. It should not dump every internal solver state. If the same
candidate is resent because of a transport retry, that duplicate is not a new
attempt. If a new candidate changes the representation, carrier, proof route,
or failing verifier phase, it is materially different and should be kept.

The journal also protects work from interruption. After `H003` succeeds, its
accepted source is durable even though the target `.lit` file has not yet
changed. A later process crash may require replaying accepted blocks, but it
does not require reconstructing them from memory.

### 4. Materialize and run a clean gate

At a coherent theorem or file checkpoint:

1. take a contiguous accepted prefix from the journal;
2. remove the outer `try:` wrappers;
3. write the blocks into `.lit` in source order;
4. mark them as materialized; and
5. run the clean file gate:

```text
target/release/litex -compact -f path/to/current-file.lit
```

The session result and clean file result are different claims. A block can
verify in a warm session while a cold registered-file replay fails, becomes
pathologically slow, or exposes a generated-fact storage problem. Record both
results.

Use a repository or module run only for an explicit larger checkpoint:

```text
target/release/litex -compact -r path/to/module
```

Do not pay the whole-module cost for every local proof repair.

#### Example: warm success and cold replay answer different questions

After the Hanoi definition and evaluation blocks are accepted, materialize
their contiguous prefix without `try:`:

<!-- litex:skip-test -->

```litex
have fn hanoi_moves(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: 2 * hanoi_moves(n - 1) + 1

hanoi_moves(0) = 0
hanoi_moves(1) = 2 * hanoi_moves(0) + 1 = 1
hanoi_moves(2) = 2 * hanoi_moves(1) + 1 = 3
hanoi_moves(3) = 2 * hanoi_moves(2) + 1 = 7
```

Then run the registered-file checkpoint:

```text
target/release/litex -compact -f \
  scripts/textbooks_drafts/Concrete-Mathematics/chapter01-recurrent-problems.lit
```

This cold run reparses and replays the configured source prefix from disk. It
checks that the materialized source—not merely the accumulated live session—
works in project order.

The bent-line closed-form proof showed why both results are necessary. Its
recursive step, polynomial step, and thin induction assembly each returned
`ok: true` when submitted as segmented session blocks. Yet retaining the full
proof package made the clean registered-file run emit no result for more than
four minutes. The journal therefore preserved the successful proof blocks,
while the runnable chapter kept only the exact proposition behind a narrow
temporary boundary:

<!-- litex:skip-test -->

```litex
thm bent_line_regions_closed_form:
    ? forall n N:
        bent_line_regions(n) = 2 * n^2 - n + 1
    trust:
        bent_line_regions(n) = 2 * n^2 - n + 1
```

The recursive function and its concrete values remained checked. The file
gate became usable again. The honest report is therefore not simply “proved”
or “failed”: the segmented proof was accepted in session; clean replay exposed
a kernel-performance problem; the canonical development draft contains one
visible trust boundary; and the journal retains the proof evidence needed for
a future regression test.

## One workflow for concepts and proofs

The transaction loop is the same, but the first question differs.

When modeling a concept, test the interface before downstream theorems:

```text
ordinary mathematical meaning
        -> semantic role
        -> Litex form and exact carrier
        -> minimal definition
        -> one real use probe
```

For example, a recursively defined counting sequence should normally be a
callable `have fn`, not a proposition relating an input to a candidate result.
If a subtraction-heavy closed form is hard to certify as `N`-valued, keep a
carrier-preserving recurrence as the construction and state the closed form as
a theorem. The verifier difficulty must not redefine the object.

#### Concept example: the triangular sum needs an empty case

The textbook introduces the function

```text
S(n) = 1 + 2 + ... + n
```

with `S(0) = 0`. Later code evaluates `S(4)` and proves a formula for `S(n)`.
Therefore the interface must be an `N`-valued function. The first attempt was
short:

```text
have fn triangular_sum(n N) N =
    sum(1, n, fn(k Z) Z {k})
```

The verifier reported that it could not prove the closed-range condition
`1 <= n`. There was also a second modeling problem: the `Z`-valued summand
selects an integer aggregate, while the public function promises `N`.

The correct response was not to weaken the public interface. It was to encode
the mathematical empty-sum convention and choose the aggregate carrier
deliberately:

<!-- litex:skip-test -->

```litex
have fn triangular_sum(n N) N by cases:
    case n = 0: 0
    case n > 0: sum(1, n, fn(k N+) N {k})
```

Now test the interface through the exact operation later mathematics needs:

<!-- litex:skip-test -->

```litex
triangular_sum(0) = 0
triangular_sum(1) = sum(1, 1, fn(k N+) N {k}) = 1
triangular_sum(2)
    = sum(1, 2, fn(k N+) N {k})
    = sum(1, 1, fn(k N+) N {k}) + fn(k N+) N {k}(2)
    = 1 + 2
    = 3
```

This one probe verifies several interface decisions at once: the declaration
is callable, zero is supported, positive bounds are well-defined, and the
result remains in `N`. Only after those claims pass should the function be
used by a closed-form theorem.

When proving a result, test the proof spine one move at a time:

```text
mathematical move
        -> existing interface
        -> smallest candidate block
        -> exact verifier phase
        -> smallest verified bridge
```

Do not let a two-step mathematical proof grow into a public forest of wrappers
and proof-only helpers. Keep local machinery local. After success, delete-probe
extra lines and retain only source-facing mathematics, genuine proof moves, and
bridges whose necessity was demonstrated in the real context.

#### Proof example: the same triangular sum has a different job

Once `triangular_sum` is stable, the theorem

```text
S(n) = n(n + 1)/2
```

is no longer a modeling question. Its natural proof spine is:

1. verify the positive base case;
2. unfold the final term of the sum;
3. substitute the induction hypothesis;
4. simplify the arithmetic;
5. add the separate zero case.

The first induction attempt stored the definition equality for `S(n + 1)`,
the builtin final-term equation, and the definition equality for `S(n)` as
separate facts. It then expected Litex to compose all of them under addition.
The failed step was the representation bridge
`S(n + 1) = S(n) + (n + 1)`.

The repair kept the mathematical spine unchanged and added only the two
verifier bridges shown necessary by the failure:

<!-- litex:skip-test -->

```litex
? induc:
    triangular_sum(n) = sum(1, n, fn(k N+) N {k})
    fn(k N+) N {k}(n + 1) = n + 1
    triangular_sum(n + 1)
        = sum(1, n + 1, fn(k N+) N {k})
        = sum(1, n, fn(k N+) N {k})
            + fn(k N+) N {k}(n + 1)
        = triangular_sum(n) + fn(k N+) N {k}(n + 1)
        = triangular_sum(n) + (n + 1)
    triangular_sum(n + 1)
        = triangular_sum(n) + (n + 1)
        = n * (n + 1) / 2 + (n + 1)
        = (n + 1) * ((n + 1) + 1) / 2
```

This is a good final proof shape because each extra line has a known job. The
anonymous-function value is an atomic bridge. The continuous chain performs
the contextual rewrite. Neither deserves a new public helper theorem, because
both serve this one local induction step.

## What the Concrete Mathematics experiment taught

The first two chapters produced several lessons that transferred across
independent source items.

### Recursive evaluation is not deep normalization

The first Hanoi probe expected `hanoi_moves(3) = 7` to normalize directly. It
did not. The accepted form exposed one stored recursive equation for each
smaller input.

The same lesson later made a planar-region recurrence work on the first
attempt. This is the ideal experience loop: a failure becomes a rule, and the
rule changes a later first attempt.

The transfer can be seen directly in the next source item. Instead of asking
Litex to jump immediately to `line_regions(3) = 7`, the first candidate already
used the previously learned shape:

<!-- litex:skip-test -->

```litex
have fn line_regions(n N) N by induc n from 0:
    case n = 0: 1
    case n > 0: line_regions(n - 1) + n

line_regions(0) = 1
line_regions(1) = line_regions(0) + 1 = 2
line_regions(2) = line_regions(1) + 2 = 4
line_regions(3) = line_regions(2) + 3 = 7
```

That block returned `ok: true` on its first submission. The journal therefore
captures two different kinds of evidence: the Hanoi failure shows why the
rule is needed, while the planar-region success shows that the rule transfers
to an independent recurrence. A useful experience record needs both.

### Carriers are part of construction

The triangular and bent-line examples showed that mathematical nonnegativity
or integrality is not automatically a verifier-visible `N` construction.
Expressions involving subtraction, division, or refined recursive arguments
may need:

- a carrier-preserving recurrence or finite sum;
- an explicit empty-range case;
- typed selected data plus a representation equality; or
- a theorem that characterizes the constructed value afterward.

Changing the public carrier to make verification easier would have changed the
mathematics. The journal made that modeling error visible.

Chapter 2 repeated the same issue with the coefficient
`n(n + 1)/2`. Mathematically it is always a natural number, but this direct
constructor was not verifier-visible as `N`:

```text
have fn triangular_coefficient(n N) N = n * (n + 1) / 2
```

The accepted implementation again separated construction from
characterization:

<!-- litex:skip-test -->

```litex
have fn triangular_coefficient(n N) N by induc n from 0:
    case n = 0: 0
    case n > 0: triangular_coefficient(n - 1) + n
```

The recurrence constructs an `N` value at every step. The quotient formula
can remain a theorem whose proof explicitly supplies divisibility. This is
not merely a workaround for one expression. It is a general design pattern:

```text
public object = carrier-safe construction
closed form   = theorem characterizing that object
```

The wrong repair would be to change the public result to `R` or `Z`, or to
replace the function with a relation about a proposed coefficient. Those
choices would make later code pay for a verifier problem by weakening the
mathematical interface.

### Atomic rewrites precede contextual rewrites

Several candidates had the right component equalities but expected Litex to
combine them automatically inside addition, multiplication, a recursive call,
or a finite fold.

The reusable repair was:

1. normalize the inner index;
2. state the exact atomic function value;
3. show one continuous equality chain for the surrounding expression.

This is verifier-specific bridge knowledge, not a new mathematical theorem. It
belongs in experience memory and should remain local in the final proof.

The shifted Hanoi proof gives the smallest concrete example. Knowing

```text
hanoi_moves(n) = 2 * hanoi_moves(n - 1) + 1
```

does not mean Litex will automatically rewrite `hanoi_moves(n)` inside
`hanoi_moves(n) + 1`. The first combined chain failed. Stating the atomic
value immediately before its consumer made the surrounding chain pass:

<!-- litex:skip-test -->

```litex
hanoi_moves(n) = 2 * hanoi_moves(n - 1) + 1
shifted_hanoi_moves(n)
    = hanoi_moves(n) + 1
    = 2 * hanoi_moves(n - 1) + 1 + 1
    = 2 * (hanoi_moves(n - 1) + 1)
    = 2 * shifted_hanoi_moves(n - 1)
```

Finite sums add another layer. To evaluate the wrapper
`finite_integer_sum(1, 2, term)`, the accepted chain crossed each boundary
explicitly:

<!-- litex:skip-test -->

```litex
fn(two_index Z) Z {two_index}(1) = 1
fn(two_index Z) Z {two_index}(2) = 2
finite_integer_sum(1, 2, fn(two_index Z) Z {two_index})
    = sum(1, 2, fn(two_index Z) Z {two_index})
    = sum(1, 1, fn(two_index Z) Z {two_index})
        + fn(two_index Z) Z {two_index}(2)
    = 1 + 2
    = 3
```

The path is wrapper selection, builtin fold recurrence, anonymous-function
value, then arithmetic. A journal that records this boundary sequence lets a
later agent search for the missing layer instead of trying unrelated theorems.

### Callability, stored facts, and executability differ

An object may be callable in a proposition. Its stored facts may support
rewriting. Neither fact alone proves that its body can be consumed by a new
checked `have fn`.

The radix and digitwise constructions exposed this difference. Closely related
checked constructors sometimes had to be submitted contiguously in one
transaction. Opaque trusted functions had to remain interfaces rather than
being treated as executable definitions.

The binary digit experiment already had a checked
`binary_digit_offset(beta, gamma, bit)` function. A later block introduced a
typed bit-to-natural conversion and then tried to consume the previously
committed offset helper inside a new checked output-digit definition. The old
helper was callable in facts, but the new definition body reported it as
unavailable. Repeating theorem calls would not solve that problem: it occurred
at definition composition, not proof search.

The successful block declared the full related constructor group together.
The central dependency inside that block was:

<!-- litex:skip-test -->

```litex
have fn binary_digit_as_N_3(bit_16c {0, 1}) N by cases:
    case bit_16c = 0: 0
    case bit_16c = 1: 1

have fn binary_digit_offset_16(beta, gamma Z, bit_offset_16 {0, 1}) Z by cases:
    case bit_offset_16 = 0: beta
    case bit_offset_16 = 1: gamma

have fn typed_binary_value_3(m N, bits fn(bit_index_16c closed_range(0, m)) {0, 1}) N =
    sum(0, m, fn(sum_index_16c closed_range(0, m)) N {
        binary_digit_as_N_3(bits(sum_index_16c)) * 2^sum_index_16c
    })

have fn binary_affine_output_digit_3(
    alpha,
    beta,
    gamma Z,
    m N,
    bits fn(input_index_16c closed_range(0, m)) {0, 1},
    output_index_16c closed_range(0, m)
) Z by cases:
    case output_index_16c = m: alpha
    case output_index_16c < m:
        binary_digit_offset_16(beta, gamma, bits(output_index_16c))
```

The declarations are semantically distinct: one converts a digit into `N`,
one maps a digit to `beta` or `gamma`, one evaluates an input word, and one
constructs an output digit. Operationally, the latter definitions need the
earlier bodies as executable dependencies. Putting the constructor group in
one contiguous transaction made the full interface pass.

The general radix experiment then supplied a useful negative control. A
previously loaded `signed_positional_value` could still appear in ordinary
facts, yet a new stored symbolic definition using its body failed. The right
lesson is not “redeclare every function forever.” It is: test definition
composability separately, keep tightly coupled constructor groups contiguous,
and treat opaque or unavailable bodies as interfaces rather than executable
code.

### Diagnose the failing phase

A rejected candidate can fail during transport, parsing, name or type
resolution, well-definedness, proof search, generated-fact storage, later use,
or clean replay.

The summation-factor experiment was particularly revealing: a higher-order
nonzero condition was available during function verification but disappeared
when a generated recursive equation was stored. A direct control using
branch-local `n > 0` and `1 / n` succeeded through every phase. That contrast
isolated a higher-order refinement problem; it was not evidence that recursive
division was mathematically invalid.

The failed constructor had the mathematical contract

```text
forall n N+:
    b(n) != 0
```

and recursively divided by `b(n)`. Litex accepted the contract while checking
the function body, then failed later while storing the generated successor
equation:

```text
cannot store fact: not well-defined
divisor b(n) must be non-zero
```

That trace places the failure at `generated_fact_storage`. It does not justify
changing the recurrence proof or adding more algebra. The next experiment
used a direct divisor whose nonzero evidence came from the recursive branch:

<!-- litex:skip-test -->

```litex
have fn harmonic_number_213(n N) R by induc n from 0:
    case n = 0: 0
    case n > 0: harmonic_number_213(n - 1) + 1 / n

harmonic_number_213(0) = 0
harmonic_number_213(1) = harmonic_number_213(0) + 1 / 1 = 1
harmonic_number_213(2) = harmonic_number_213(1) + 1 / 2 = 3 / 2
```

This block passed function verification, generated-fact storage, and later
use. The comparison isolates the suspect boundary:

```text
1 / n under branch n > 0       -> passes all tested phases
1 / b(n) under a function prop -> loses evidence during fact storage
```

Only after this control is it reasonable to call the higher-order behavior a
`kernel_problem`. Without the control, “division failed” would be too broad
and would teach the next agent the wrong lesson.

### Session acceptance is not clean replay

Some segmented proofs checked successfully in the persistent session but made
the cold file gate unusably slow. The journal preserved the fully checked
sequence even when the runnable source needed a narrower temporary trust
boundary.

Without the journal, the evidence would have collapsed into either “the proof
works” or “the file hangs.” Neither description is accurate enough to guide a
kernel fix.

For the bent-line theorem, the actual evidence ledger looked like this:

```text
recursive function and B(0..3)       accepted and materialized
recursive successor proof segment    session ok
polynomial identity proof segment    session ok
thin induction assembly              session ok
full registered-file replay          no event after >4 minutes
narrow-trust registered-file replay  exits successfully
```

Each row answers a different question. The first says the public function is
usable. The next three say the proof obligations can be checked separately.
The fourth reveals a cold-path performance problem. The fifth proves that the
localized source boundary restores a runnable chapter.

If only the final `.lit` file survived, a future maintainer would see `trust`
but not know that a segmented checked proof already exists. If only the warm
session log survived, a reader might incorrectly label the chapter
`checkable`. Keeping both artifacts supports the precise status:
`translated`, with a visible narrow trust and a recorded kernel-performance
regression.

## How a local observation becomes shared knowledge

Do not promote every syntax mistake into a global rule. Promote a lesson when
at least one condition holds:

- the same mechanism occurs in two independent mathematical items;
- missing it changes the intended object, carrier, or public interface; or
- a minimal reproduction and control isolate stable parser, verifier, storage,
  use, or replay behavior.

Promote the mechanism, not the book-specific name. Keep source or block ids as
evidence so the rule can be retested after a kernel or library change.

Route the result to its real consumer:

- modeling mistakes improve concept-modeling guidance;
- repeated proof bridges improve proof-writing guidance;
- missing reusable mathematics becomes a library theorem;
- unclear failures motivate diagnostic work;
- isolated verifier behavior becomes a kernel regression.

### Example: promote the mechanism, not “the Hanoi trick”

After the first Hanoi failure, “write out `H(1)`, `H(2)`, and `H(3)`” was only
a local repair. It would be a bad global rule because most recursive
functions are not named `H` and most tasks do not stop at three.

The evidence became reusable only after separating the mechanism:

```text
CM-1.1-HANOI
  failure: direct H(3) did not deeply normalize
  repair: expose one stored recursive equation per step

CM-1.2-E1.4
  transfer: line-region values used the same shape
  result: first candidate accepted

CM-2.2-E2.6
  transfer: higher-order prefix sums needed the exact recursive RHS
  result: exact function argument retained before evaluation
```

The promoted rule can now be written without any textbook-specific name:

> Separate definition acceptance from recursive evaluation. Unfold one stored
> equation at a time, and keep the exact function argument until its value has
> been materialized.

A promotion record can retain source ids without storing a long narrative:

```json
{
  "lesson": "unfold recursive definitions one stored equation at a time",
  "promotion_evidence": [
    "CM-1.1-HANOI",
    "CM-1.2-E1.4",
    "CM-2.2-E2.6"
  ],
  "consumer": "proof-writing guidance"
}
```

Carrier preservation followed a slightly different route. The first bent-line
failure already qualified as high-risk because changing `N -> N` into
`N -> Z` would alter the public mathematical object. Later triangular-sum and
triangular-coefficient failures provided independent confirmation. That lesson
belongs partly in concept-modeling guidance, not only in a list of proof
tricks.

By contrast, a one-off misspelled binder or formatting-only retry remains in
the local journal. Promoting it would add noise without changing a future
mathematical decision.

## Handling real blockers

Once a direct real-context attempt identifies a genuine proof, library,
inference, syntax, or formulation blocker:

1. keep the intended source-facing statement;
2. place `trust` only around the blocked substep;
3. record the exact debt and evidence;
4. continue with the main mathematical line.

Use `kernel_problem` only when a minimal reproduction or control isolates
verifier, runtime, storage, or replay behavior. Diagnostic phases are not a
second blocker taxonomy.

A file containing `trust` is translated but not fully checkable. A successful
Litex run also remains relative to Litex's current builtin rules, inference
rules, imported interfaces, kernel implementation, and declared assumptions.

### Example: keep a guarded theorem and a checked specialization

Chapter 2's general summation factor would recursively divide by an arbitrary
higher-order coefficient `b(n)`. Repeated real-context attempts showed that
nonzero evidence was lost during generated-fact storage. Continuing to invent
wrapper types would have hidden the actual boundary and delayed the rest of
the chapter.

The source mathematics was therefore split at its natural interface. The
general formula keeps the nonzero denominator visible as a premise:

<!-- litex:skip-test -->

```litex
thm summation_factor_product_formula_211:
    ? forall a, b, s fn(product_formula_index_211 N) R, n N+:
        $is_summation_factor_29(a, b, s)
        finite_coefficient_product_211(2, n, b) != 0
        =>:
            s(n)
                = s(1)
                    * finite_coefficient_product_211(1, n - 1, a)
                    / finite_coefficient_product_211(2, n, b)
    trust:
        s(n)
            = s(1)
                * finite_coefficient_product_211(1, n - 1, a)
                / finite_coefficient_product_211(2, n, b)
```

The specialization whose divisor is structurally the literal `2` remains
fully executable:

<!-- litex:skip-test -->

```litex
have fn hanoi_summation_factor_211(n N+) R by induc n from 1:
    case n = 1: 1 / 2
    case n > 1: hanoi_summation_factor_211(n - 1) / 2

hanoi_summation_factor_211(1) = 1 / 2
hanoi_summation_factor_211(2)
    = hanoi_summation_factor_211(1) / 2
    = 1 / 4
hanoi_summation_factor_211(3)
    = hanoi_summation_factor_211(2) / 2
    = 1 / 8
```

This boundary is narrow and informative. The general source theorem is still
present with its true domain condition. Concrete mathematics that the current
verifier can execute remains checked. The journal records the failed
higher-order constructor and the `kernel_problem`; the todo points to the
future refinement-propagation fix. Nothing requires trusting the whole
section, weakening the theorem, or pretending the general constructor works.

## Complete walkthrough: from a textbook TXT to a checked Litex draft

Suppose a user has one local plain-text book and asks an AI agent to formalize
it:

```text
/absolute/path/to/my_discrete_math_notes.txt
```

The right first goal is not “translate the whole file.” First inventory the
whole source, then complete one small vertical slice all the way through the
workflow. A useful first slice contains roughly one definition, one immediate
example, and one theorem that uses the definition. Once its source records,
interfaces, journal, chapter file, and clean gates all work, the same machinery
can advance through the remaining items in source order.

This walkthrough uses the project slug `My-Discrete-Math-Notes` and a fictional
source slice about the recurrence

```text
A(0) = 0,
A(n) = 2 A(n - 1) + 1 for n > 0,
A(n) = 2^n - 1.
```

The mathematics is intentionally small. The example is about the complete book
workflow: source custody, selection, modeling, proof experiments,
materialization, and scaling. Replace the paths, source anchors, names, and
mathematics with those from the real book.

### What will exist at the end

Keep source-facing records and verifier-experience artifacts outside the
mathematical module. Keep the clean Litex draft, its configuration, and its one
documentation pair inside the draft module:

```text
scripts/My-Discrete-Math-Notes/
    source/book.txt
    source_manifest.yaml
    formalization_plan.md
    items/chapter01.yaml
    proof_journals/chapter01-recurrences.json
    experience/problem_notes/
    todo.md

scripts/textbooks_drafts/My-Discrete-Math-Notes/
    litex.config
    README.md
    math_collections.md
    chapter01-recurrences.lit
```

These two directories have different jobs. The first preserves what was read,
what was selected, how attempts behaved, and what remains unfinished. The
second is the canonical development draft a mathematical reader can run. Do
not put a private source transcript, failure log, or chain-of-thought dump into
the `.lit` module. Do not edit `textbooks/My-Discrete-Math-Notes/` unless the
user explicitly requests publication.

### Step 1: enter the repository and lock the source

Run the following commands from the repository root. Change only the source
path and project slug:

```bash
cd /absolute/path/to/golitex

BOOK_SLUG=My-Discrete-Math-Notes
SOURCE_FILE=/absolute/path/to/my_discrete_math_notes.txt
SOURCE_WORKSPACE="scripts/$BOOK_SLUG"
DRAFT_DIR="scripts/textbooks_drafts/$BOOK_SLUG"

test -f Cargo.toml
test -f "$SOURCE_FILE"
mkdir -p \
  "$SOURCE_WORKSPACE/source" \
  "$SOURCE_WORKSPACE/items" \
  "$SOURCE_WORKSPACE/proof_journals" \
  "$SOURCE_WORKSPACE/experience/problem_notes"
cp "$SOURCE_FILE" "$SOURCE_WORKSPACE/source/book.txt"

wc -l "$SOURCE_WORKSPACE/source/book.txt"
shasum -a 256 "$SOURCE_WORKSPACE/source/book.txt"
file "$SOURCE_WORKSPACE/source/book.txt"
```

The copy under `source/` is the locked input for this formalization. Record its
hash before interpreting or normalizing it. If OCR cleanup is necessary, keep
the original and create a separately named corrected working copy; never
silently replace the source of truth. Also confirm that the user is entitled
to use the source. A source manifest should normally record anchors and concise
mathematical reformulations, not reproduce long copyrighted passages.

Give the AI this first prompt:

```text
We are starting a Litex textbook translation in the golitex repository.

Input:
- locked source: scripts/My-Discrete-Math-Notes/source/book.txt
- source workspace: scripts/My-Discrete-Math-Notes/
- canonical draft: scripts/textbooks_drafts/My-Discrete-Math-Notes/

For this stage, do not write any .lit code and do not modify textbooks/.
Read the locked TXT as evidence. Create source_manifest.yaml and
formalization_plan.md in the source workspace.

In source_manifest.yaml record:
1. title and author if the TXT supports them;
2. local source path, SHA-256, source kind, and a source-lock rule;
3. chapter and section line anchors;
4. where standalone exercises begin;
5. known OCR or encoding defects;
6. a rule that source reconstruction errors are not Litex errors.

In formalization_plan.md:
1. describe the source and artifact boundary;
2. inventory the whole book at chapter level;
3. propose one small first vertical slice;
4. exclude standalone exercises unless I explicitly request them;
5. state the release-session, try-block, journal, file-gate, and whole-module
   verification protocol.

Use rg, wc, file, shasum, and numbered line views as needed. Cite source line
ranges for every retained item. Report uncertainties instead of silently
repairing the text.
```

A compact manifest for the example might look like this:

```yaml
source:
  title: "My Discrete Math Notes"
  local_file: "source/book.txt"
  sha256: "<paste the recorded hash>"
  source_kind: "plain-text transcript"
  source_lock: "Do not silently replace or normalize this file."
  copyright_handling: "Store anchors and concise mathematical reformulations; do not reproduce long passages."

scope:
  standalone_exercises: excluded
  first_slice:
    title: "A doubling recurrence"
    body_lines: "120-147"
    exercises_begin_line: 148

source_quality:
  known_issues:
    - "Superscripts are flattened, so 2^n may appear as 2n."
    - "Displayed equations may be split across physical lines."
  attribution_rule: "Resolve source reconstruction before classifying a Litex failure."
```

The exact fields can grow with the project, but the source hash, retained line
range, exercise boundary, and source-quality notes should be settled before
formalization begins.

### Step 2: inspect the whole book, then choose one slice

Use line-numbered searches instead of reading an unbounded TXT into one AI
context:

```bash
rg -n \
  '^(CHAPTER|Chapter|[0-9]+(\.[0-9]+)*[[:space:]])|Definition|Theorem|Proposition|Example|Exercises?' \
  "$SOURCE_WORKSPACE/source/book.txt"

nl -ba "$SOURCE_WORKSPACE/source/book.txt" | sed -n '100,175p'
```

If the source has poor headings, search for several independent signals such
as equation numbers, repeated section typography, “Proof,” and the beginning
of the exercise list. Record ambiguous boundaries in the manifest instead of
letting a guessed page break become a mathematical fact.

For this example, assume lines 120--147 contain:

```text
Definition 1.1. Let A(0)=0 and, for n>0, let
A(n)=2A(n-1)+1.

Example 1.2. A(1)=1, A(2)=3, and A(3)=7.

Theorem 1.3. For every nonnegative integer n,
A(n)=2^n-1.

Exercises ...
```

This yields three retained items: the definition, the source-facing example,
and the theorem. The exercise section is inventoried but omitted. On a real
book, select a small coherent batch rather than an isolated theorem whose
definitions live hundreds of lines earlier.

Ask the AI to turn the slice into stable records:

```text
Read scripts/My-Discrete-Math-Notes/source_manifest.yaml and only source lines
120-147 from the locked TXT.

Create scripts/My-Discrete-Math-Notes/items/chapter01.yaml. Preserve source
order. Every retained record must contain:
- source and a stable source_id;
- problem;
- proof_idea;
- semantic_role;
- chosen_form;
- one downstream use_probe;
- litex_code, initially empty;
- comments;
- status and blocker.

Retain Definition 1.1, Example 1.2, and Theorem 1.3. Omit the standalone
exercise section. Do not invent a Litex proof yet. In proof_idea write only the
shortest ordinary mathematical spine and existing interface needs.
```

The first item should be concrete enough to constrain later code:

```yaml
chapter:
  id: 1
  title: "Recurrences"
  source_lines: "120-147"
  exercises_excluded: true

items:
  - source: "Chapter 1, Definition 1.1"
    source_id: "MDMN-1.1-RECURRENCE"
    problem: "Define the nonnegative sequence A(0)=0 and A(n)=2*A(n-1)+1."
    proof_idea: "Use the zero value as the base case and the displayed recurrence for positive indices."
    semantic_role: "function"
    chosen_form: "have fn by induc"
    use_probe: "doubling_recurrence(3) = 7"
    litex_code: ""
    comments: "Planned; source reconstructed from lines 120-124."
    status: "planned"
    blocker: ""
```

The record prevents a common modeling drift. Later lines apply `A(n)`, so the
definition must expose a callable function. A proposition relating `n` to a
candidate value would not preserve the source interface.

### Step 3: create the canonical draft without publishing it

There are two different initialization cases.

If a published module already exists under
`textbooks/My-Discrete-Math-Notes/`, use the repository initializer exactly
once:

```bash
scripts/textbooks_drafts/init_draft.sh My-Discrete-Math-Notes
```

That script intentionally refuses to overwrite an existing draft and
intentionally refuses to initialize a book that has never been published.

For a genuinely new local TXT with no public module, create a new draft
workspace:

```bash
mkdir -p "$DRAFT_DIR"
touch \
  "$DRAFT_DIR/README.md" \
  "$DRAFT_DIR/math_collections.md" \
  "$DRAFT_DIR/chapter01-recurrences.lit"
```

Create `scripts/textbooks_drafts/My-Discrete-Math-Notes/litex.config` with:

```text
[hierarchy]
module

[export]
chap1 = "./chapter01-recurrences.lit"
```

Export order is mathematical execution order. When Chapter 2 is added later,
append it after Chapter 1. Do not add `README.md`, `math_collections.md`,
source manifests, or journals to `[export]`.

Now initialize the module documentation with this prompt:

```text
Create the initial README.md and math_collections.md for
scripts/textbooks_drafts/My-Discrete-Math-Notes/.

README.md must describe only the API that is actually implemented now. Because
the chapter file is still empty, say that no public mathematical API is
implemented yet. Include the run entrypoint and explain checked, trusted, and
axiom boundaries.

math_collections.md is the design manual. For the first source slice, record:
- the ordinary meaning of the sequence;
- why it must be a callable N -> N function;
- the intended `have fn ... by induc` shape;
- dependencies, exact carrier, and the probe A(3)=7;
- the later closed-form theorem;
- any proof or well-definedness holes still unknown.

Maintain exactly this one README.md and one math_collections.md for the whole
book draft. Do not create per-chapter copies and do not modify textbooks/.
```

At this point the project is registered but the chapter is empty. That is the
correct moment to test the interface in a session.

### Step 4: model the concepts before proving them

Ask the AI for interface cards and a typed dependency graph before it generates
Litex:

```text
Apply Litex concept modeling to the retained items in
scripts/My-Discrete-Math-Notes/items/chapter01.yaml.

Do not edit the .lit file yet. For each item state:
1. ordinary mathematical meaning;
2. semantic role;
3. exact domain and codomain;
4. chosen Litex form and why the nearest alternative is wrong;
5. a minimal use probe;
6. dependencies and typed dependency edges;
7. source-order implementation order;
8. trust/source boundaries, if any.

Reject any formulation that changes the source-defined N-valued function into
a relation or a Z-valued workaround. Write the shortest ordinary proof spine
for the closed form, but do not turn that spine into Litex code yet.
```

For the example, the useful output is small:

```text
Nodes
  N
  doubling_recurrence : N -> N
  small_values
  doubling_recurrence_closed_form

Edges
  N -> doubling_recurrence                    signature
  doubling_recurrence -> small_values         proof/use
  doubling_recurrence -> closed_form          signature + proof
  arithmetic exponent laws -> closed_form     proof

Implementation order
  function -> small values -> closed-form theorem
```

The theorem's proof spine is equally short:

```text
1. Base case: A(0)=0=2^0-1.
2. Induction step: unfold A(m+1) once.
3. Rewrite (m+1)-1 to m.
4. Substitute A(m)=2^m-1.
5. Normalize to 2^(m+1)-1.
```

That spine is the invariant. A verifier failure may justify one explicit
rewrite bridge, but it must not silently replace the source theorem with a
different claim.

### Step 5: build once and initialize the proof journal

Build the current release binary once:

```bash
cargo build --release
```

The registered file baseline should also succeed while the file is empty:

```bash
target/release/litex -compact -f \
  "$DRAFT_DIR/chapter01-recurrences.lit"
```

Before sending a candidate, create
`scripts/My-Discrete-Math-Notes/proof_journals/chapter01-recurrences.json`.
Its initial content should be one valid JSON object:

```json
{
  "schema_version": 1,
  "target": "scripts/textbooks_drafts/My-Discrete-Math-Notes/chapter01-recurrences.lit",
  "session_command": "target/release/litex -compact -session -before scripts/textbooks_drafts/My-Discrete-Math-Notes/chapter01-recurrences.lit",
  "proof_spine": [
    "define the N-valued recurrence",
    "check source small values one stored equation at a time",
    "prove the closed form by induction"
  ],
  "blocks": [],
  "materialization": {
    "block_ids": [],
    "file_gate_command": "",
    "file_gate_result": "not_run"
  }
}
```

The journal is not optional scratch space. It is the recoverable staging source
of truth until accepted blocks are materialized. Store concise rationale and
decision evidence, not hidden chain-of-thought.

### Step 6: start one persistent session for the current chapter

For a new, partial, or failing registered chapter, start:

```bash
target/release/litex -compact -session -before \
  "$DRAFT_DIR/chapter01-recurrences.lit"
```

Wait for a `ready` JSON event. Keep that same process alive. The transport
protocol and the Litex transaction have two separate wrappers:

```text
run B001 <utf8-byte-count>
try:
    <one source-order candidate>
```

The `run` header is the session frame. Its byte count covers only the UTF-8
Litex payload after the newline. The outermost `try:` is the mathematical
transaction. An AI client should compute the byte count, send the frame to the
existing process, and retain the process handle for the next frame. Sending
raw Litex without the `run` header causes a protocol error; sending a failing
top-level statement without `try:` poisons the session for later frames.

`-session -before` is the default while constructing the target file because
it loads the registered prefix but excludes the target. After a file is clean,
`-session -f <file>` is useful when the desired starting state should include
that complete file. Do not use `-session -f` to redefine declarations already
loaded from the same file.

This is the execution prompt to give the AI:

```text
Start exactly one release session:
target/release/litex -compact -session -before
scripts/textbooks_drafts/My-Discrete-Math-Notes/chapter01-recurrences.lit

Wait for the ready event and keep the process alive. Before every submission:
1. append the planned candidate to the JSON journal;
2. use one stable block id;
3. send one length-delimited `run` frame;
4. wrap the Litex candidate in one literal outermost `try:`.

After every response, update the journal before touching the .lit file. Record
the exact concise diagnostic, failed verifier phase, diagnosis, and next
smallest change. Failed try blocks stay in the same session. Successful blocks
become accepted_unmaterialized and store their exact accepted Litex without
the outer try wrapper. Do not edit the chapter until I ask for a checkpoint.
```

### Step 7: let the first useful mistake happen

The first candidate can define the function and ask for the source's final
small value directly:

```text
try:
    have fn doubling_recurrence(n N) N by induc n from 0:
        case n = 0: 0
        case n > 0: 2 * doubling_recurrence(n - 1) + 1

    doubling_recurrence(3) = 7
```

Assume the function is accepted internally but the last equality is unknown.
Because the whole candidate is inside one outer `try:`, nothing from B001 is
committed. Record the attempt before changing it:

```json
{
  "id": "B001",
  "source_order": 1,
  "intent": "Define the recurrence and verify the source's A(3)=7 example.",
  "dependencies": ["N", "integer arithmetic"],
  "attempts": [
    {
      "candidate": "have fn doubling_recurrence ...; doubling_recurrence(3) = 7",
      "result": "failed",
      "verifier_evidence": "unknown result for doubling_recurrence(3) = 7",
      "diagnosis": "the definition is plausible, but the probe expected deep recursive normalization",
      "next_change": "resubmit the complete block and expose one stored recurrence equation per value"
    }
  ],
  "accepted_litex": "",
  "reusable_lesson": "",
  "status": "failed"
}
```

The failed candidate is valuable because it isolates a reusable assumption.
Do not respond by changing `N` to `Z`, replacing the function with a relation,
or deleting the source example.

Use this repair prompt:

```text
Repair only block B001 in the same live session.

Preserve:
- semantic role: callable function;
- domain and codomain: N -> N;
- source recurrence;
- source example A(3)=7.

The failure is in concrete recursive evaluation, not in the mathematics.
Resubmit the whole atomic block because the failed try committed nothing.
Expose the base value and one stored recursive equation at each input 1, 2,
and 3. Do not invent helper theorems. Update the journal before and after the
submission.
```

The repaired candidate is:

```text
try:
    have fn doubling_recurrence(n N) N by induc n from 0:
        case n = 0: 0
        case n > 0: 2 * doubling_recurrence(n - 1) + 1

    doubling_recurrence(0) = 0
    doubling_recurrence(1) = 2 * doubling_recurrence(0) + 1 = 1
    doubling_recurrence(2) = 2 * doubling_recurrence(1) + 1 = 3
    doubling_recurrence(3) = 2 * doubling_recurrence(2) + 1 = 7
```

After it succeeds, B001 becomes `accepted_unmaterialized`. Preserve the exact
unwrapped source and the lesson “concrete recursive evaluation unfolds one
stored equation at a time.” Only then submit the theorem as B002.

### Step 8: prove the theorem in the same session

The earlier accepted B001 is now committed in the live Runtime, so B002 can
use the function without replaying it:

<!-- litex:skip-test -->

```litex
try:
    thm doubling_recurrence_closed_form:
        ? forall n N:
            doubling_recurrence(n) = 2^n - 1
        by induc n from 0:
            ? doubling_recurrence(n) = 2^n - 1
            doubling_recurrence(0) = 0 = 2^0 - 1

            forall m Z:
                m >= 0
                doubling_recurrence(m) = 2^m - 1
                =>:
                    (m + 1) - 1 = m
                    doubling_recurrence(m + 1)
                        = 2 * doubling_recurrence((m + 1) - 1) + 1
                        = 2 * doubling_recurrence(m) + 1
                        = 2 * (2^m - 1) + 1
                        = 2 * 2^m - 1
                        = 2^m * 2^1 - 1
                        = 2^(m + 1) - 1
```

If this fails, do not ask for an entirely new proof. First classify the phase.
For example, an unknown rewrite of
`doubling_recurrence((m + 1) - 1)` suggests that the inner index equality must
be made explicit before rewriting the outer function. A carrier error suggests
that the induction binder or exponent domain needs attention. A parse error
should be reduced without changing the proof spine.

Give the AI this general failure prompt:

```text
Block B002 failed. Read the first decisive verifier evidence and classify the
failed phase as parse, name/type resolution, well-definedness, proof,
generated-fact storage, or later use.

Keep the theorem statement and its five-step mathematical spine unchanged.
Compare the failing line with the nearest accepted line in the same real
context. Propose and run only the smallest correction. Record the rejected
candidate, exact evidence, diagnosis, and next change in the JSON journal
before resubmission. If a genuine non-kernel blocker is established, retain
the intended theorem, use the narrowest legal trust on the blocked substep,
update todo.md, and continue. Classify kernel_problem only after a minimal
reproduction and a passing control isolate verifier behavior.
```

Once B002 succeeds, update the corresponding `chapter01.yaml` records with the
accepted code and an honest status. “Translated” means the intended statement
has a Litex form; “checkable” requires the relevant code to verify without
`trust`.

### Step 9: materialize a contiguous checkpoint

After B001 and B002 are both durable in JSON, materialize that contiguous
accepted prefix into `chapter01-recurrences.lit` in source order. Strip only
the outer `try:` wrappers. Add mathematical source comments if they help the
reader; do not add verifier-debug narration.

Then run a clean registered-file gate:

```bash
target/release/litex -compact -f \
  "$DRAFT_DIR/chapter01-recurrences.lit"
```

The warm session and the cold file gate answer different questions. Session
success says that the submitted blocks work in the accumulated Runtime. The
file gate says that the materialized source replays from a clean project
prefix, with the real export order and file namespace.

Ask the AI to checkpoint with:

```text
Materialize only the contiguous accepted prefix B001-B002 from
scripts/My-Discrete-Math-Notes/proof_journals/chapter01-recurrences.json into
scripts/textbooks_drafts/My-Discrete-Math-Notes/chapter01-recurrences.lit.

Requirements:
- preserve source order;
- copy accepted_litex exactly;
- remove outer try wrappers;
- keep failure history only in the journal;
- update block status to materialized;
- run the release -compact -f gate;
- record the exact gate command and result in materialization;
- if the gate fails, keep JSON as the source of truth and resume at the first
  affected block instead of overwriting the journal.

After a clean gate, run a proof-liveness audit. Remove result echoes, dead facts,
wrapper facts, and bypassable rewrite chains only after a deletion probe in
the real context. Update README.md with only the now-implemented API. Reconcile
math_collections.md if the verified interface differs from the design.
```

The end of the journal should name the materialized blocks and the clean gate:

```json
{
  "materialization": {
    "block_ids": ["B001", "B002"],
    "file_gate_command": "target/release/litex -compact -f scripts/textbooks_drafts/My-Discrete-Math-Notes/chapter01-recurrences.lit",
    "file_gate_result": "ok"
  }
}
```

### Step 10: scale from one slice to the rest of the book

Do not now ask the AI to translate every remaining line in one response.
Advance in bounded source-order batches:

```text
whole-book inventory
    -> chapter inventory
    -> 20--50 retained source items
    -> concept and dependency pass
    -> one session per current target file
    -> one journaled try block at a time
    -> clean chapter checkpoint
    -> next chapter
```

Before Chapter 2, add its registered export after Chapter 1:

```text
[hierarchy]
module

[export]
chap1 = "./chapter01-recurrences.lit"
chap2 = "./chapter02-counting.lit"
```

Then use:

```bash
target/release/litex -compact -session -before \
  "$DRAFT_DIR/chapter02-counting.lit"
```

This loads the checked Chapter 1 prefix once, excludes the unfinished Chapter
2 target, and enters Chapter 2's file environment. If instead the purpose is
to explore new consequences after the already checked Chapter 1 file itself,
start:

```bash
target/release/litex -compact -session -f \
  "$DRAFT_DIR/chapter01-recurrences.lit"
```

At every chapter checkpoint, run `-f`. At a complete-book milestone, run:

```bash
target/release/litex -compact -r "$DRAFT_DIR"
```

If the book is claimed to be free of user trust and axioms, also run the
stricter audit:

```bash
target/release/litex -compact -strict -r "$DRAFT_DIR"
```

Publication is a separate, explicit operation. A clean draft does not by
itself authorize copying it into `textbooks/`.

### Step 11: turn the book's attempts into reusable experience

After each clean checkpoint, compare independent journal entries. A useful
local rule should say more than “this theorem was hard.” It should name the
failed assumption, decisive evidence, smallest verified correction, and where
the correction transferred.

Use this mining prompt:

```text
Read the accepted and materially distinct failed attempts in
scripts/My-Discrete-Math-Notes/proof_journals/ and the current clean .lit
chapter. Do not modify mathematical source.

Group repeated mechanisms across independent source items. For each candidate
lesson report:
- the incorrect assumption;
- two or more supporting source ids, or why one case is high-risk enough;
- the failed verifier phase and decisive evidence;
- the smallest verified correction;
- whether the lesson concerns concept modeling, proof writing, parser/kernel
  behavior, or only this local book;
- a short reusable rule;
- one regression probe.

Promote only repeated mechanisms, high-risk semantic errors, or stable
verifier behavior. Keep one-off repairs in
scripts/My-Discrete-Math-Notes/experience/problem_notes/. Update todo.md for
unresolved trust or kernel_problem boundaries, and remove a todo only after its
resolution has a durable experience note.
```

For the example, the first failure alone is a local note:

```text
Direct evaluation of a recursive call at 3 did not unfold multiple stored
equations. The accepted calculation exposed values 0, 1, 2, and 3 in order.
```

If a later counting recurrence independently fails in the same way and the
same correction succeeds, the stronger cross-item rule becomes justified:

```text
For concrete recursive evaluation, expose one stored base or successor
equation at a time; do not assume deep normalization.
```

### One master prompt for an autonomous AI agent

The staged prompts above give the user maximum control. When the source and
scope are already clear, the following prompt can delegate the same workflow
while preserving its gates:

```text
Formalize a bounded first slice of my local textbook TXT in the golitex
repository.

Input source:
  /absolute/path/to/my_discrete_math_notes.txt
Project slug:
  My-Discrete-Math-Notes
Initial scope:
  inventory the whole book, then fully translate only the first coherent
  non-exercise slice containing roughly one definition, one example, and one
  theorem.

Apply the repository policy, textbook translation, concept modeling, and
proof-writing workflows.

Required artifacts:
1. locked source copy, SHA-256, source_manifest.yaml, and formalization_plan.md
   under scripts/My-Discrete-Math-Notes/;
2. source item records with source, problem, proof_idea, litex_code, and
   comments;
3. canonical draft under
   scripts/textbooks_drafts/My-Discrete-Math-Notes/ with exactly one README.md,
   one math_collections.md, litex.config, and the first chapter .lit file;
4. one persistent JSON proof journal for the chapter;
5. concise experience notes and todo entries for unresolved boundaries.

Hard boundaries:
- do not edit textbooks/ or publish anything;
- do not reproduce long source passages;
- record OCR/source reconstruction separately from Litex failures;
- omit standalone exercises;
- preserve source theorem identity, semantic role, domain, and codomain;
- do not weaken a function into a relation or widen a carrier as a workaround;
- do not write .lit code until the interface card, use probe, typed dependency
  order, and ordinary proof spine are recorded.

Execution protocol:
- build once with cargo build --release;
- run target/release/litex only;
- for the current registered chapter start one
  `-compact -session -before <chapter>` process;
- before each candidate, persist a planned journal entry;
- send source-order candidates using `run <id> <utf8-byte-count>` and one
  literal outermost `try:`;
- after each result, update the journal before editing .lit;
- after ordinary failure keep the same session, classify the failed phase, and
  make the smallest correction;
- after success store accepted_litex as accepted_unmaterialized;
- when a real blocker is identified, keep the intended statement, use the
  narrowest legal trust, update todo.md, and continue;
- materialize only a contiguous accepted prefix at a coherent checkpoint;
- run clean `-compact -f <chapter>` and record warm versus cold results;
- run the proof-liveness audit;
- run `-compact -r <draft-module>` at the bounded-slice milestone.

Do not hide failed attempts by overwriting them. Record concise rationale and
decision evidence, not private chain-of-thought. Stop after the selected slice
is cleanly checkpointed and report: retained source ids, implemented API,
checkable/trusted status, journal path, exact verification commands, remaining
todos, and the proposed next source-order batch.
```

The expected handoff is not merely “the theorem passed.” It is a small,
auditable package: a locked source, a bounded source inventory, honest item
records, a modeled interface, a durable attempt history, a readable `.lit`
chapter, a clean replay result, and a precise next batch. That package is what
makes book-scale formalization repeatable instead of one long generation that
forgets its own mistakes.

## The practical checklist

Before the first block:

- write the mathematical spine;
- choose the semantic role and exact carrier;
- identify one use probe;
- build the release binary;
- start one project-aware session;
- initialize the JSON journal.

For each block:

- record the exact candidate before execution;
- wrap it in one outermost `try:`;
- keep the same session after ordinary failure;
- record the decisive result before repair;
- make the next smallest correction;
- preserve accepted source and its reusable lesson before continuing.

At a checkpoint:

- materialize only a contiguous accepted prefix;
- run the clean release `-f` gate;
- record warm-session and cold-replay results separately;
- audit proof liveness and remove echoes or dead bridges;
- promote only lessons supported by repeated or high-risk evidence.

The result is more than a verified file. It is a reproducible mathematical
writing process in which ideas, verifier feedback, corrections, and reusable
experience remain connected.

### A complete micro-cycle: an empty-aware finite sum

The checklist becomes easier to remember as one small end-to-end example.
Chapter 2 needs finite sums over integer intervals and adopts the convention
that a reversed interval has sum zero.

**Before the first block**, write the interface sentence:

> `finite_integer_sum(first, last, term)` is a `Z`-valued function. It uses
> builtin `sum` when `first <= last` and returns `0` otherwise. Immediate
> probes are the empty interval `(3, 2)` and the singleton `(1, 1)`.

Start the session before the chapter and create the journal. The first
candidate defines the wrapper and tries both probes:

```text
try:
    have fn finite_integer_sum(first, last Z, term fn(term_index_21 Z) Z) Z by cases:
        case first <= last: sum(first, last, term)
        case first > last: 0

    finite_integer_sum(3, 2, fn(empty_index Z) Z {empty_index}) = 0
    finite_integer_sum(1, 1, fn(one_index Z) Z {one_index}) = 1
```

The verifier reaches the definition and empty case, but the singleton equality
is unknown. Because the outer `try:` is atomic, the whole candidate rolls
back. Record the materially distinct result:

```json
{
  "candidate": "singleton wrapper evaluation without unfolding",
  "result": "failed",
  "failed_phase": "proof",
  "verifier_evidence": "unknown singleton equality",
  "diagnosis": "the wrapper, builtin sum, and lambda value were compressed",
  "next_change": "expose all three representation boundaries"
}
```

Keep the same session and resubmit the corrected current block. The complete
resubmission contains the definition and both probes; the changed part is the
explicit singleton chain:

<!-- litex:skip-test -->

```litex
finite_integer_sum(1, 1, fn(one_index Z) Z {one_index})
    = sum(1, 1, fn(one_index Z) Z {one_index})
    = fn(one_index Z) Z {one_index}(1)
    = 1
```

After success, store this source as `accepted_unmaterialized` and record the
lesson “unfold wrapper, fold, and anonymous-function value separately.” Do not
yet mix it with unrelated chapter edits.

At the checkpoint, materialize the accepted wrapper and probes in source
order, remove the outer `try:`, and run:

```text
target/release/litex -compact -f \
  scripts/textbooks_drafts/Concrete-Mathematics/chapter02-sums.lit
```

Finally, audit the source. The wrapper is source-facing and has later
consumers, so it stays public. The explicit singleton chain is a useful
pedagogical example of the three boundaries, so it stays as a reader bridge.
The verifier diagnosis and failed candidate do not belong in `.lit`; they
remain in the journal. This one cycle exercises every checklist item without
turning the mathematical file into a debugging transcript.
