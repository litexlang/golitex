# What numeric type bridges cost in these examples

This experiment tests a narrow explanation for the earlier Litex/Lean timing
differences: could numeric type conversions and their proofs be expensive?
The four controls below keep each Lean proposition unchanged while varying
its proof. All variants are retained, including one where the direct lemma
is slower. Measurement date: **2026-10-24**.

The result is mixed. Removing an explicit cast annotation did not remove any
part of the resulting proof. Replacing cast automation with a direct lemma
roughly halved checking time in one example, modestly improved another, and
was slower in a third. The matching Litex arithmetic claims checked faster
in this run, but these measurements do not isolate object-model design as
the cause of the cross-system difference.

## 1. An explicit cast versus an inferred cast

The proposition in both Lean variants is:

```lean
∀ (a : Int) (d : Nat), 0 < d →
  a = (d : Int) * (a / (d : Int)) + a % (d : Int)
```

The two proofs use the same lemma:

```lean
-- Explicit annotation in the proof.
fun a d _ => (Int.mul_ediv_add_emod a (d : Int)).symm

-- The elaborator inserts the coercion.
fun a d _ => (Int.mul_ediv_add_emod a d).symm
```

The ordinary validation compares the elaborated proof expressions with
`explicit.value == inferred.value`: **they are identical**, each with 123
expression-tree nodes. Total medians are **4.148 ms** and **4.346 ms**.
Their median absolute deviations are 0.280 ms and 0.440 ms, and the ordering
reverses in one of the three processes. There is no stable speed advantage
from omitting this annotation. Both variants still contain the coercion.

The Litex statement is:

```litex
forall a Z,d N+:
    a=d*quot(a,d)+a%d
```

[Explicit Lean source](sources/type-bridge/cast_annotations__explicit.lean) ·
[Inferred Lean source](sources/type-bridge/cast_annotations__inferred.lean) ·
[Litex source](sources/type-bridge/cast_annotations.lit)

## 2. Cast automation versus a direct library fact

For natural addition viewed in the reals, both Lean proofs establish:

```lean
∀ m n : Nat, ((m + n : Nat) : Real) = (m : Real) + (n : Real)
```

The proof variants are:

```lean
by
  intro m n
  norm_cast
```

```lean
fun m n => Nat.cast_add m n
```

The total median falls from **8.011 ms to 4.053 ms**, about **1.98×**.
The proof-elaboration median falls from **4.795 ms to 1.361 ms**; target-type
elaboration remains about 2.38 ms. The proof trees have 585 and 21 nodes.
This is evidence that general bridge automation can add avoidable work in
Lean. It is not evidence that Lean must pay that automation cost.

[Automation source](sources/type-bridge/cast_addition__automation.lean) ·
[Direct lemma source](sources/type-bridge/cast_addition__direct.lean)

The order-lifting control has a different outcome. Its proposition is
`∀ m n : Nat, m < n → (m : Real) < (n : Real)`, with these proofs:

```lean
by
  intro m n h
  exact_mod_cast h
```

```lean
fun _ _ h => Nat.cast_lt.mpr h
```

Here the direct lemma is slower: **10.107 ms versus 9.174 ms** for automation,
about 10% more time. The direction is the same in all three processes.
A smaller proof tree, 135 versus 203 nodes, does not itself guarantee faster
checking. We did not separately profile the instance searches or reductions
responsible for this result.

[Automation source](sources/type-bridge/cast_order__automation.lean) ·
[Direct lemma source](sources/type-bridge/cast_order__direct.lean)

These two controls are representation-specific obligations inside Lean.
There is deliberately no timed Litex reflexive equality opposite them:
checking a reflexive fact would not measure the same bridge obligation.

## 3. Prove a square nonnegative before or after embedding

Both Lean variants prove `∀ n : Nat, (0 : Real) ≤ (n : Real)^2`.
One proves a natural-number fact and transports it:

```lean
by
  intro n
  have h : 0 ≤ n^2 := Nat.zero_le _
  exact_mod_cast h
```

The other applies the real-square lemma directly:

```lean
fun n => sq_nonneg (n : Real)
```

The total median falls from **17.806 ms to 15.048 ms**, about **1.18×**.
The proof-elaboration median improves from 14.350 ms to 9.135 ms, but the
final declaration-check median increases from 0.946 ms to 3.268 ms.
The overall gain is consequently smaller than the proof-construction gain.

Litex checks the corresponding arithmetic statement directly:

```litex
forall n N:
    n^2 >= 0
```

[Transport proof](sources/type-bridge/square_nonnegative__bridge.lean) ·
[Direct real proof](sources/type-bridge/square_nonnegative__direct.lean) ·
[Litex source](sources/type-bridge/square_nonnegative.lit)

## Phase measurements

Times are milliseconds, with **33 measured samples per variant**: three
processes, eleven samples each, after two warmups per variant per process.
Variants are interleaved in a reproducibly shuffled order inside each Lean
process. All share `import Mathlib`, `import Lean`, and the same options.
Startup and imports are outside the interval.

| Lean variant | Target elaboration | Proof elaboration / synthesis | Finalization | Final declaration check | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Quotient, explicit cast | 3.310 | 0.590 | 0.051 | 0.174 | 4.148 |
| Quotient, inferred cast | 3.340 | 0.523 | 0.050 | 0.182 | 4.346 |
| Addition, `norm_cast` | 2.384 | 4.795 | 0.020 | 0.662 | 8.011 |
| Addition, direct lemma | 2.372 | 1.361 | 0.068 | 0.214 | 4.053 |
| Order, `exact_mod_cast` | 1.248 | 7.098 | 0.022 | 0.632 | 9.174 |
| Order, direct lemma | 1.284 | 7.731 | 0.213 | 0.626 | 10.107 |
| Square, transported proof | 2.142 | 14.350 | 0.029 | 0.946 | 17.806 |
| Square, direct real proof | 2.151 | 9.135 | 0.327 | 3.268 | 15.048 |

Every raw sample's four phase durations sum exactly to its total. The table
reports each column's median separately, so displayed phase medians need not
sum to the displayed total median.

The instrumented checker elaborates a closed proposition with `Term.elabType`,
elaborates and synthesizes its proof with `Term.elabTermEnsuringType`, then
checks the resulting declaration with
`Lean.Environment.addDeclCore 0 declaration none true`. The final `true`
enables kernel checking. Each process also submits a closed false equality,
`1 = 2` with the proof of `1 = 1`, and requires rejection.

These boundaries are not a complete call-level profiler. Proof elaboration
can also check generated auxiliary declarations. Target and proof elaboration
both involve type inference; the target column is not the total cost of
typing. The final column includes checked declaration insertion. This custom
expression-checking path also differs from the older full `elabCommand`
measurements, so their totals should not be spliced into one series.
The [official Lean processing stages](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
describe the distinction between elaboration and kernel checking; the exact
instrumented boundaries are visible in this experiment's harness.

## Matching arithmetic targets across systems

Only the two arithmetic targets have Litex timings in this experiment.
The Lean rows below use the fastest measured variant for each target.

| Arithmetic target | Litex (ms) | Lean (ms) | Lean ÷ Litex |
| --- | ---: | ---: | ---: |
| Integer quotient and remainder | 0.733 | 4.148 | 5.66× |
| Natural square, nonnegative as a real | 0.828 | 15.048 | 18.18× |

Litex uses a fresh strict Runtime per sample, with Runtime construction
outside the timer. Its interval includes parsing, well-definedness,
verification, storage, and evidence construction. Lean's interval starts after
parsing the probe command. These are distinct checking mechanisms and trusted
bases, not equal-cost implementations of one kernel.

The pooled ratios also hide process variation: quotient ratios range from
about **2.93× to 6.26×**, and square ratios from **9.91× to 18.52×** when
calculated from each process's medians. This is an exploratory measurement on
one machine, not a controlled hardware-performance claim. All outcomes are
retained rather than filtered by which system or variant wins.

The evidence supports a narrow conclusion: some bridge-proof automation has
measurable overhead, and the unified Litex source does not ask the author for
those representation bridges. Much of the measured Lean time lies before
the final declaration check. The experiment does **not** establish how much
of the cross-system gap is caused specifically by numeric type design,
rather than inference, automation, rule interfaces, or implementation choices.

## Reproduce and inspect

From the repository root:

```sh
cargo build --release
python3 examples/litex_vs_lean_speed/harness/type_bridge.py
```

The harness checks the ordinary Lean theorem declarations with no `sorry`,
then runs the phase checker and its kernel rejection control. It writes only
the `type-bridge-*` result files and its task-owned draft area under `tmp/`.
The source statements and proof variants are owned by the case file; the
individual source files are readable snapshots of those accepted cases.

- [Cases and exact proof variants](cases/type-bridge.json)
- [Phase timer and loaded Litex harness generator](harness/type_bridge.py)
- [Raw samples, including warmups](results/type-bridge-raw.json)
- [Medians, ranges, deviations, and proof sizes](results/type-bridge-summary.json)
- [Versions, timing boundaries, ordering seed, and hashes](results/type-bridge-environment.json)
- [Ordinary proof validation and kernel negative controls](results/type-bridge-validation.json)
- [Strict Litex Session journal and clean-file evidence](results/type-bridge-litex-journal.json)

Litex's strict mode excludes user-written trust and axiom statements, while
builtin and inference rules remain trusted. The ordinary Lean validation
records its axiom dependencies. The two Lean-only bridge controls have no
matched Litex verification claim.
