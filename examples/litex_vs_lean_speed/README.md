# Litex / Lean checking-time comparisons

This directory collects the Litex / Lean timing experiments conducted so far. Each case states the same mathematics in both systems, measures their respective checking paths, and retains source files, raw samples and environment snapshots for reproduction.

The newer [summation expansion and arithmetic context-load batch](search-and-expansion.md) contains 6 complete Litex examples and 15 Lean routes, comparing expansion/full-context proofs with direct Lean baselines. It retains all results, without the older batches' Litex-faster-only filter. Checking-path and whole-process times remain separate.

<!-- quantitative-iteration-table:start -->
## Quantitative iteration: whole-process time in seconds

| Problem | Litex median time (s) ↓ | Lean median time (s) ↓ | Whole-process ratio (Lean ÷ Litex) |
| --- | ---: | ---: | ---: |
| [Parametric Newton step](#iteration-parametric-newton) | 0.213 | 60.180 | 283.09× |
| [Gradient descent on a quadratic](#iteration-quadratic-descent) | 2.905 | 21.303 | 7.33× |
| [Perturbed geometric recurrence bound](#iteration-perturbed-geometric) | 1.352 | 17.130 | 12.67× |

Measured on 2026-10-24, with 3 samples per problem per system; ratios use unrounded medians. The interval runs from starting a fresh process to completing the file check, **including Lean's Mathlib import**. These results are separate from the older millisecond tables that exclude startup/imports. Their ratios do not measure isolated verifier or proof-search acceleration.

[Raw samples](results/quantitative-iteration-raw.json) · [Summary](results/quantitative-iteration-summary.json) · [Environment and source hashes](results/quantitative-iteration-environment.json) · [Validation](results/quantitative-iteration-validation.json). This batch used the recorded release binaries; moving the source files here did not involve new timing runs.
<!-- quantitative-iteration-table:end -->

For an explanation through actual proof terms, see [Proof terms and the checking pipeline for 1 + 1 = 2](lean-proof-pipeline.md). It traces source, explicit core terms, lambda abstraction and the kernel's definitional-equality check. This explanatory experiment adds no timing data and does not infer performance from lambda calculus itself.

Four comparisons of types and object notation appear in [Types, objects, and ordinary mathematical notation](types-and-objects.md): reasoning across number sets, integer quotient-remainder decomposition, guarded function calls and finite-set counting. Each pairs source lengths with existing checking times.

[What numeric type bridges cost in these examples](type-bridge-experiment.md) tests whether type bridging explains the timing differences. It compares explicit conversion annotations, conversion automation and direct lemmas for the same Lean statement, with separate measurements of target elaboration, proof construction and final declaration checking. It retains all controls, regardless of which system is faster.

```text
cases/            Case definitions (JSON: Litex source, Lean statement, Lean proof routes)
sources/          Per-case Litex and Lean files, grouped by batch and domain
harness/bench.py  Timing runner (validate / measure / all)
results/          Raw samples, summaries, validation and environment snapshots
```

## How to read the measurements

- The older checking-path tables report warm-sample medians in milliseconds. **Ratio = Lean ÷ Litex**; a value above 1 means Litex took less time.
- Both sides of those checking-path batches **exclude** process startup and `import Mathlib`. Whole-command times are recorded separately and are not mixed into these tables.
- Litex: release build, with a fresh strict `Runtime` for each sample. The interval covers tokenization, parsing, well-definedness checking, verification, storage and evidence construction.
- Lean: a custom `#probe` command uses a nanosecond clock around `elabCommand`; `Elab.async=false` makes proof construction and kernel checking synchronous. Command parsing is outside the interval.
- These compare two **checking paths**. They do not establish an overall language/kernel ranking or a proportional reduction in the time needed to finish a mathematical task.

<a id="de-bruijn-factor"></a>

### De Bruijn factors: how much longer is the formal text?

**De Bruijn factor = formal-text length ÷ informal mathematical-text length.** Lower factors mean less additional text: 1.5 means 50% longer, and 0.8 means 20% shorter. Length and checking time are reported separately for the same case. [Wiedijk's paper](https://www.cs.ru.nl/~freek/factor/factor.pdf) discusses the ratio and different uncompressed/compressed file-size measures.

The **DF\*** variant here follows the existing source comparisons' character-counting method: remove whitespace, full-line comments, imports, `set_option` and validation directives starting with `#`, then count Unicode characters. Declarations, names, statements and proofs are included; loaded library/builtin implementations are excluded on both sides. Informal text loses only whitespace. Both systems share the same English mathematical text, including the statement, conditions and proof or calculation explanation. DF\* is a character-based variant, not the paper's original byte-count or gzip factor.

For example, the shared text for quotient-remainder decomposition is:

> For an integer a and a positive integer d, a = d⌊a/d⌋ + (a mod d), by quotient-remainder decomposition.

**The two length columns on the left compare de Bruijn factors; the three timing columns on the right compare elapsed time.** Their directions are:

- **Length:** Litex factor = Litex characters ÷ informal mathematical characters; Lean factor = Lean characters ÷ the same informal mathematical characters. Lower is shorter on both sides.
- **Time:** both times are milliseconds, with lower being faster. The Litex speedup ratio is Lean time ÷ Litex time; a higher ratio means a shorter Litex checking time.

| Case | Length: Litex DF* ↓ | Length: Lean DF* ↓ | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Integer quotient-remainder decomposition | 0.35 | 1.24 | 1.135 | 3.341 | 2.94× |
| Complete proof that √2 is irrational | 1.73 | 4.91 | 199.285 | 779.754 | 3.91× |

For the first row, the factors are **30÷85 = 0.35 and 105÷85 = 1.24**, and the timing ratio is **3.341375÷1.135042 = 2.94×**, using unrounded data. The Lean routes follow each table's existing timing selection. Longer Lean sources are not selected to enlarge the length difference, and the sources are not claimed to be the shortest possible.

**These are retrospective examples.** The [shared informal texts](cases/informal-baselines.json) were written after the formal sources, rather than fixed before a translation experiment. They do not establish a fixed de Bruijn factor for Litex or directly measure readability or ease of writing. The denominator's language, notation and level of detail affect the result; a prospective study should fix the source text before independent formalization. The results retain cases where Lean is shorter, including power-set cardinality, the oddness predicate and the reciprocal sequence.

This record covers 24 cases from three generated batches plus the guarded reciprocal in the types guide. Two multi-step `.lit` sources have acquired proof steps beyond their saved timing-case definitions, so their factors are **—**. The other older batches still lack shared informal baselines. The [per-case character counts, source hashes and two drift records](results/de-bruijn-factors.json) can be checked with `python3 examples/litex_vs_lean_speed/harness/de_bruijn.py --check`. `--write` rebuilds the length record and three result tables from saved data without rerunning timings.

## Overview

This table summarizes only the older checking-path batches. The three whole-process experiments are listed separately at the beginning of this page.

| Domain | Cases | Checking-time ratio range (Lean ÷ Litex) |
| --- | ---: | ---: |
| Natural-number arithmetic and radicals | 2 | 14× – 37× |
| Finite sums | 4 | 3.5× – 7.3× |
| Trigonometry | 3 | 10× – 19× |
| Elementary calculations: logarithms, radicals, large numbers | 5 | 7× – 217× |
| Number theory: primality and greatest common divisors | 2 | 2.2× – 147× |
| Quantifiers, witnesses, unique existence, existence elimination | 21 | 1.1× – 77× |
| Definitions and proof commands (functions, predicates, structures, contradiction, cases, induction) | 9 | 4.0× – 51× |
| Sets | 3 | 1.6× – 82× |
| Functions (range) | 1 | 2.9× |
| Integer arithmetic and divisibility | 2 | 2.8× – 2.9× |
| Finite combinatorics | 2 | 4.2× – 73× |
| Calculus (continuity, derivatives) | 2 | 24× – 30× |
| Classical proof (√2 irrational, same steps on both sides) | 1 | 3.9× |
| Multi-step statements (second round: inequalities, algebra, arithmetic, existence construction) | 7 | 1.7× – 306× |
| Other statement forms and small showcase problems (third round: predicate definitions, witnesses, ε-N, set equality) | 4 | 3.7× – 8.8× |

**Selection in the older checking-path batches:** only cases where Litex checked faster (ratio > 1) were retained, comparing the same statement and workload. Directions favoring Lean, such as definitional reduction of function equality, explicit recursive expansion and direct reuse of a large proved theorem, were not systematically covered in those batches. The [unscreened summation/context-load batch](search-and-expansion.md) retains both directions; Lean's direct route was faster in five of its six cases.

---

## 1. The five earlier batches

Raw samples for these five batches remain in local batch records (five `2026-10-22-*` / `2026-10-23-*` directories). This directory publishes per-case sources and aggregate results read from those records, without new measurements. Environment records are in `results/`.

### 1.1 Basic arithmetic and radicals (2026-10-22)

| Mathematical statement | Litex time (ms) ↓ | Fastest tested Lean time (ms) ↓ | Lean time ÷ Litex time | Lean route | Source |
| --- | ---: | ---: | ---: | --- | --- |
| `1 + 1 = 2` (Mathlib already loaded) | 0.037 | 1.361 | **36.66×** | `rfl` | [lit](sources/arithmetic/add.lit) · [lean](sources/arithmetic/mathlib_nat.lean) |
| `sqrt(1) = 1` | 0.039 | 0.555 | **14.28×** | `Real.sqrt_one` | [lit](sources/arithmetic/sqrt.lit) · [lean](sources/arithmetic/sqrt_exact.lean) |

### 1.2 Finite sums and trigonometry (2026-10-22)

| Mathematical statement | Litex time (ms) ↓ | Fastest tested Lean time (ms) ↓ | Lean time ÷ Litex time | Lean route | Source |
| --- | ---: | ---: | ---: | --- | --- |
| `sum(1,10,fn(k Z) Z {k}) = 55` | 1.623 | 5.622 | **3.46×** | `decide` | [lit](sources/sums/sum_id_10.lit) |
| `sum(1,10,fn(k Z) Z {k^2}) = 385` | 2.224 | 8.266 | **3.72×** | `decide` | [lit](sources/sums/sum_sq_10.lit) |
| `sum(1,10,fn(k Z) Q {1/3}) = 10/3` | 2.123 | 11.277 | **5.31×** | `sum_const` + `norm_num` | [lit](sources/sums/sum_rat_10.lit) |
| `finite_set_sum({1,3,5,7,9}, fn(k Z) Z {k}) = 25` | 1.108 | 8.051 | **7.26×** | `decide` | [lit](sources/sums/finite_set_5.lit) |
| `sin(0) = 0` | 0.041 | 0.757 | **18.43×** | `Real.sin_zero` | [lit](sources/sums/sin_zero.lit) · [lean](sources/sums/sin_zero__exact.lean) |
| `sin(pi) = 0` | 0.040 | 0.736 | **18.50×** | `Real.sin_pi` | [lit](sources/sums/sin_pi.lit) · [lean](sources/sums/sin_pi__exact.lean) |
| `forall x R: sin(x)^2 + cos(x)^2 = 1` | 0.446 | 4.636 | **10.40×** | `fun x => Real.sin_sq_add_cos_sq x` | [lit](sources/sums/sin_identity.lit) · [lean](sources/sums/sin_identity__exact.lean) |

Finite sums have some of this batch's smallest ratios. Both systems sum terms individually; Litex checks without constructing Lean proof terms. These timings do not isolate the contribution of that architectural difference.

### 1.3 Elementary calculations, number theory and large numbers (2026-10-22)

| Mathematical statement | Litex time (ms) ↓ | Fastest tested Lean time (ms) ↓ | Lean time ÷ Litex time | Lean route | Source |
| --- | ---: | ---: | ---: | --- | --- |
| `log(2,8) = 3` | 0.064 | 13.992 | **217.01×** | Explicit rewriting (`logb_pow`, etc.) | [lit](sources/elementary/log_2_8.lit) · [lean](sources/elementary/log_2_8_explicit.lean) |
| `sqrt(2)*sqrt(8) = 4` | 0.240 | 7.077 | **29.50×** | `sqrt_mul` + `norm_num` | [lit](sources/elementary/radical_product.lit) |
| `$prime(1000000007)` | 0.027 | 4.029 | **147.19×** | `native_decide` | [lit](sources/elementary/prime_1000000007.lit) · [lean](sources/elementary/prime_1000000007_native_decide.lean) |
| `factorial(50) = 30…000` (exact value) | 0.107 | 2.501 | **23.41×** | `norm_num` | [lit](sources/elementary/factorial_50.lit) · [lean](sources/elementary/factorial_50_norm_num.lean) |
| `95800^4+217519^4+414560^4 = 422481^4` | 0.264 | 11.098 | **42.03×** | `rfl` | [lit](sources/elementary/fourth_power_eq.lit) · [lean](sources/elementary/fourth_power_eq_rfl.lean) |
| `witness exist a,b,c,d N+ st {a^4+b^4+c^4=d^4} from …` | 2.094 | 14.718 | **7.03×** | `decide` | [lit](sources/elementary/fourth_power_witness.lit) |
| `gcd(2178309,1346269) = 1` | 0.455 | 0.992 | **2.18×** | `rfl` | [lit](sources/elementary/gcd_2178309.lit) |

The primality case uses `native_decide` in Lean: native compiled evaluation adds a generated axiom dependency reported by `#print axioms`. The same goal took 718 ms with `norm_num`. The table uses the **fastest tested** route, giving Lean the favorable measured comparison.

### 1.4 Quantifiers, witnesses, unique existence and existence elimination (2026-10-23; 21 cases)

Each case tested several tactic, direct-lemma and compact proof-term routes. The table uses the fastest tested Lean route for each problem. The statement-form column identifies the main Litex construct exercised.

| Statement form | Mathematical statement | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | ---: | ---: | ---: |
| Universal + positivity of addition | The sum of two positive reals is positive | 0.394 | 9.305 | **23.60×** |
| Universal + positivity of multiplication | The product of two positive reals is positive | 0.408 | 4.986 | **12.23×** |
| Universal + transitivity | Transitivity of strict inequalities | 0.256 | 1.240 | **4.84×** |
| Universal + inequality translation | Add the same real number to both sides | 0.469 | 9.537 | **20.33×** |
| Universal + powers | Every real square is nonnegative | 0.597 | 13.491 | **22.60×** |
| Universal + absolute value | The absolute-value triangle inequality | 5.261 | 7.338 | **1.39×** |
| Universal + reciprocal | The reciprocal of a positive real is positive | 0.287 | 8.167 | **28.43×** |
| Universal + division | A nonzero real divided by itself is one | 0.387 | 3.301 | **8.52×** |
| Universal + antisymmetry | Opposite weak inequalities imply equality | 0.287 | 1.217 | **4.24×** |
| Universal + disjunctive conclusion | A zero product has a zero factor | 0.203 | 6.860 | **33.83×** |
| Universal + polynomial identity | Expanding a square | 1.589 | 15.006 | **9.44×** |
| Universal + instantiation | Apply a universal function property at 0 | 0.675 | 1.238 | **1.83×** |
| Witness | A real number whose square is four | 0.512 | 4.789 | **9.36×** |
| ∀∃ construction | Construct a larger real for every real | 1.071 | 1.384 | **1.29×** |
| ∀∃ + positivity | Construct a smaller positive real from a positive real | 1.628 | 10.215 | **6.28×** |
| Unique existence | Every real has a unique additive inverse | 1.422 | 3.795 | **2.67×** |
| ∀∃ with two constraints | Construct two reals with prescribed sum and difference | 3.219 | 21.098 | **6.56×** |
| Existence elimination | Existence of a square root implies nonnegativity | 4.148 | 14.026 | **3.38×** |
| Existence elimination + scaling | Extract a square root and construct one for four times the value | 9.502 | 14.557 | **1.53×** |
| ∀∃ + upper bound | Construct a common upper bound for two reals | 1.745 | 1.871 | **1.07×** |
| Nonempty-set witness | Prove the positive-real set is nonempty by a witness | 0.084 | 6.439 | **76.88×** |

Sources are in `sources/quantifiers/`: one `.lit` per case and one `<id>_<method>.lean` per Lean route.

In this selected batch, some larger ratios occur when a statement combines well-definedness, scope and several rules. With specialized one-line Lean lemmas such as `lt_trans`, `le_antisymm`, `exists_gt` and `abs_add_le`, the measured ratios are around 1–5. These observations do not isolate a general cause of the timing differences.

### 1.5 Definitions and proof commands (2026-10-23; 10 programs screened)

Timings cover the complete program: definition plus use, or the full proof block.

| Program | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time | Source |
| --- | ---: | ---: | ---: | --- |
| Expression function: define a square and evaluate it | 0.730 | 7.609 | **10.42×** | [lit](sources/declarations/expression_function.lit) · [lean](sources/declarations/expression_function.lean) |
| Reciprocal function with a domain condition | 1.823 | 8.583 | **4.71×** | [lit](sources/declarations/guarded_function.lit) · [lean](sources/declarations/guarded_function.lean) |
| Define and use an open-interval predicate | 0.189 | 8.223 | **43.45×** | [lit](sources/declarations/predicate.lit) · [lean](sources/declarations/predicate.lean) |
| Define absolute value by positive/negative branches | 0.729 | 7.330 | **10.05×** | [lit](sources/declarations/piecewise_function.lit) · [lean](sources/declarations/piecewise_function.lean) |
| Two-dimensional point: structure, construction and field access | 0.573 | 7.615 | **13.30×** | [lit](sources/declarations/structure.lit) · [lean](sources/declarations/structure.lean) |
| Define and call the theorem that positive reals are nonzero | 0.158 | 8.018 | **50.74×** | [lit](sources/declarations/named_theorem.lit) · [lean](sources/declarations/named_theorem.lean) |
| Contradiction: no real has square -1 | 4.127 | 49.472 | **11.99×** | [lit](sources/declarations/contradiction.lit) · [lean](sources/declarations/contradiction.lean) |
| Cases: absolute value equals the value or its negation | 0.757 | 10.576 | **13.97×** | [lit](sources/declarations/cases_proof.lit) · [lean](sources/declarations/cases_proof.lean) |
| Induction: sum of the first n positive integers | 43.626 | 174.986 | **4.01×** | [lit](sources/declarations/induction_proof.lit) · [lean](sources/declarations/induction_proof.lean) |

This batch also measured definition-only declarations and uses in fresh contexts with definitions already loaded. Those measurements are in the original records beyond `results/selected-cases-2026-10-22-23.csv`.

---

## 2. Additional domains (2026-10-23)

This round extends the first five batches to sets, functions, integer arithmetic and divisibility, finite combinatorics, calculus, and a longer classical proof. Cases are in `cases/new-round.json`, sources in `sources/new-round/`, and raw samples in `results/new-round-raw.json`.

| Domain | Mathematical statement | Litex approach | Lean approach | Length: Litex DF* ↓ | Length: Lean DF* ↓ | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| Classical proof | √2 is irrational | `by contra:` + unique reduced fraction + prime divisibility of powers, forcing p and q even | Same five steps: coprimality of `Rat.num`/`Rat.den`, parity, `Nat.Prime.dvd_of_dvd_pow` | 1.73 | 4.91 | 199.285 | 779.754 | **3.91×** |
| Sets | Union distributes over intersection | `union(A,intersect(B,D))=intersect(union(A,B),union(A,D))` | `Set.union_inter_distrib_left` | 1.08 | 1.09 | 0.286 | 1.380 | **4.83×** |
| Sets | De Morgan's law for difference from a union | `set_minus(A,union(B,D))=intersect(set_minus(A,B),set_minus(A,D))` | `ext` + `simp` + `tauto` | 0.85 | 1.16 | 0.279 | 22.842 | **81.96×** |
| Sets | Intersection preserves inclusion | `A $subset B =>: intersect(A,D) $subset intersect(B,D)` | `Set.inter_subset_inter_left` | 0.99 | 1.00 | 0.934 | 1.500 | **1.61×** |
| Functions | A function value belongs to the range | `f(x) $in fn_range(f)` | `Set.mem_range_self` | 0.68 | 1.36 | 0.313 | 0.920 | **2.94×** |
| Integer arithmetic | Integer quotient-remainder decomposition | `a=d*quot(a,d)+a%d` | `Int.mul_ediv_add_emod` | 0.35 | 1.24 | 1.135 | 3.341 | **2.94×** |
| Divisibility | An integer product is divisible by its factor | `$dvd(a*c,c)` | `dvd_mul_left` | 0.52 | 1.24 | 0.604 | 1.712 | **2.83×** |
| Finite combinatorics | Cardinality of `{1,2,3}` | `finite_set_size({1,2,3})=3` | `by decide` | 0.44 | 0.75 | 0.049 | 3.597 | **73.43×** |
| Finite combinatorics | An n-element set has 2ⁿ subsets | `finite_set_size(power_set(A))=2^finite_set_size(A)` | `Finset.card_powerset` | 0.84 | 0.78 | 0.250 | 1.047 | **4.19×** |
| Combinatorics | A natural-number factorial is positive | `factorial(n)>0` | `Nat.factorial_pos` | 0.42 | 0.98 | 0.165 | 0.582 | **3.54×** |
| Calculus | The derivative of x² at 3 is 6 | `$has_derivative_at(fn(t R) R {t^2},3,6)` | `hasDerivAt_pow` + `congr_deriv` + `norm_num` | 0.80 | 3.07 | 1.555 | 46.258 | **29.75×** |
| Cartesian products | Reconstruct an ordered pair from its coordinates | `(p(1),p(2))=p` | `Prod.mk.eta` | 0.35 | 0.67 | 0.170 | 0.567 | **3.34×** |
| Calculus | x² is continuous at 3 | `$is_continuous_at(fn(t R) R {t^2},3)` | `continuousAt_pow` | 0.59 | 1.14 | 0.377 | 8.986 | **23.83×** |

Different Lean proofs of the same statement can have very different timings, so each alternative route was measured separately:

| Case | Lean route | Approach | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | --- | ---: | ---: |
| Union distributes over intersection | `lemma` (main table) | Reuse a Mathlib lemma matching the goal | 1.380 | 4.83× |
| Union distributes over intersection | `ext_simp` | Decompose the sets with `ext x` + `simp` + `tauto` | 34.521 | 120.85× |
| Intersection preserves inclusion | `lemma` (main table) | Reuse a Mathlib lemma matching the goal | 1.500 | 1.61× |
| Intersection preserves inclusion | `term` | Supply a proof term directly | 2.053 | 2.20× |
| Cardinality of {1,2,3} | `decide` (main table) | `by decide` | 3.597 | 73.43× |
| Cardinality of {1,2,3} | `norm_num` | `by norm_num` | 19.045 | 388.83× |
| Reconstruct a pair from its coordinates | `term` | Supply a proof term directly | 0.632 | 3.72× |
| Reconstruct a pair from its coordinates | `lemma` (main table) | Reuse a Mathlib lemma matching the goal | 0.567 | 3.34× |

The selected Lean routes are listed in the approach columns above and in the fastest-route column of `results/new-round.md`. All ratios use unrounded medians.

Each row has complete sources, with one file per Lean route: `sources/new-round/<id>.lit` and `sources/new-round/<id>__<method>.lean`.

### √2 irrational: the same proof steps on both sides

Both sides follow five steps: assume √2 is rational; obtain its unique reduced fraction p/q with gcd(p,q)=1; derive p² = 2q², hence 2 | p² and p even; substitute to obtain q² = 2(p/2)², hence q even; contradict gcd(p,q)=1. Litex uses `release thm` for two supporting results (unique reduced fractions and prime divisibility of powers); Lean uses `Rat.reduced` and `Nat.Prime.dvd_of_dvd_pow`.

Litex (199.285 ms):

```litex
# sqrt(2) is not rational.
by contra:
    ? not sqrt(2) $in Q
    release thm rational_has_unique_reduced_fraction(sqrt(2))
    obtain p, q from exist! p Z, q N+ st {sqrt(2) = p / q, gcd(p, q) = 1}

    p^2 = (sqrt(2) * q)^2 = sqrt(2)^2 * q^2 = 2 * q^2
    p^2 % 2 = (2 * q^2) % 2 = 0
    release thm prime_divides_power(p, 2, 2)

    p / 2 $in Z
    q^2 = p^2 / 2 = 2 * (p / 2)^2
    q^2 % 2 = (2 * (p / 2)^2) % 2 = 0
    release thm prime_divides_power(q, 2, 2)

    impossible 2 <= gcd(p, q) = 1
```

Lean (779.754 ms; [source](sources/new-round/sqrt_two_irrational__scratch.lean)):

```lean
import Mathlib

example : Irrational (Real.sqrt 2) := by
  rintro ⟨q, hq⟩
  have h2 : (q : Real) ^ 2 = 2 := by
    rw [hq, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  -- Unique reduced fraction: p = |num|, m = den, gcd p m = 1
  set p : Nat := q.num.natAbs with hp
  set m : Nat := q.den with hm
  have hden : (m : Real) ≠ 0 := by
    have : (0 : Nat) < m := q.den_pos
    exact_mod_cast this.ne'
  -- Substitute (q : ℝ) = num / den
  have hqeq : (q : Real) = (q.num : Real) / (m : Real) := by
    rw [Rat.cast_def, hm]
  -- p² = 2 m² (transfer the equality from ℤ to ℕ)
  have hnat : p ^ 2 = 2 * m ^ 2 := by
    have hreal : (q.num : Real) ^ 2 = 2 * (m : Real) ^ 2 := by
      rw [hqeq] at h2
      field_simp at h2
      nlinarith [h2]
    have hint : q.num ^ 2 = 2 * (m : Int) ^ 2 := by
      exact_mod_cast hreal
    have habs : ((p : Int)) ^ 2 = 2 * (m : Int) ^ 2 := by
      have hnum : q.num ^ 2 = ((p : Int)) ^ 2 := by
        rcases Int.natAbs_eq q.num with h | h
        · rw [h, hp]
        · rw [h, hp]; ring
      rw [← hnum, hint]
    exact_mod_cast habs
  -- p is even
  have hp2 : 2 ∣ p ^ 2 := ⟨m ^ 2, hnat⟩
  have hp_even : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hp2
  -- Then the denominator m is even as well
  obtain ⟨k, hk⟩ := hp_even
  have hm2 : m ^ 2 = 2 * k ^ 2 := by
    rw [hk] at hnat
    nlinarith
  have hm2dvd : 2 ∣ m ^ 2 := ⟨k ^ 2, hm2⟩
  have hm_even : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hm2dvd
  -- Contradiction with gcd(p, m) = 1
  have hcop : p.Coprime m := q.reduced
  have hgcd : 2 ∣ p.mgcd m := Nat.dvd_gcd ⟨k, hk⟩ hm_even
  rw [hcop] at hgcd
  omega
```

For these proofs with corresponding steps, the ratio is **3.91×: Litex 199.285 ms, Lean 779.754 ms**. The Lean proof was the first version written from scratch in this round and was not optimized for speed; `field_simp`, `nlinarith` and `exact_mod_cast` are substantial operations. A skilled Lean author may improve it; any optimized measured version should replace the entry in the same table.

## 3. Multi-step statements without matching Lean theorems (2026-10-23, second round)

Direct reuse of a matching theorem is a different workload from deriving the result through several steps. This round selected statements for which no matching Lean theorem was used. Cases are in `cases/multi-step.json`, sources in `sources/multi-step/`, and each alternative Lean route was timed separately.

| Domain | Mathematical statement | Litex approach | Lean approach | Length: Litex DF* ↓ | Length: Lean DF* ↓ | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| Inequalities | A sum of two squares is zero only if both values are zero | `x^2+y^2=0 =>: x=0 and y=0` | `constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]` | 0.42 | 1.19 | 0.685 | 209.744 | **306.11×** |
| Inequalities | `x/(x+1)` is positive for positive x | Prove `x+1 > 0`, then `x/(x+1) > 0` | `have h1 : 0 < x+1 := by linarith`; `div_pos hx h1` | 0.37 | 1.11 | 0.949 | 29.170 | **30.75×** |
| Algebra | Cancel multiplication by 2 from an equality | `2*x = 2*y =>: x = y` | `mul_left_cancel₀ (by norm_num) h` | 0.43 | 1.54 | 0.335 | 10.726 | **32.01×** |
| Inequalities | A real square plus one is positive | `x^2 + 1 > 0` | `positivity` | 0.39 | 1.07 | 2.189 | 17.404 | **7.95×** |
| Inequalities | `x² + y² ≥ 2xy` | `(x-y)^2 >= 0` → expand → `x^2+y^2 >= 2*x*y` | `nlinarith [sq_nonneg (x-y)]` | 1.02 | 1.34 | 52.271 | 87.954 | **1.68×** |
| Existence construction | An even integer above every positive integer | `witness … from 2*n`, then prove divisibility and the strict bound | `⟨2*n, by omega, by omega, ⟨n, by ring⟩⟩` | — | — | 4.426 | 34.877 | **7.88×** |
| Arithmetic | A positive integer is smaller than its double | `2*n > n` | `omega` | — | — | 0.885 | 14.761 | **16.69×** |

Complete sources are in `sources/multi-step/`: `<id>.lit` and `<id>__<method>.lean`.

Other Lean routes for the same statements (the main table uses the fastest):

| Case | Lean route | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | ---: | ---: |
| Cancel multiplication by 2 from an equality | `linarith` | 37.737 | 112.63× |
| Cancel multiplication by 2 from an equality | `mul_left_cancel₀` (main table) | 10.726 | 32.01× |
| A real square plus one is positive | `positivity` (main table) | 17.404 | 7.95× |
| A real square plus one is positive | `nlinarith` | 49.474 | 22.60× |
| A positive integer is smaller than its double | `omega` (main table) | 14.761 | 16.69× |
| A positive integer is smaller than its double | `nlinarith` | 63.217 | 71.47× |

One case deserves a closer look:

- **`x² + y² ≥ 2xy` has a ratio of only 1.68×.** Litex takes three steps: the initial square inequality, expansion to `x^2 + y^2 - 2*x*y >= 0`, and rearrangement. Each step is checked separately; Lean's `nlinarith` handles all three together. A low cost per statement does not guarantee a low total cost when more statements are needed.

Some candidate statements failed automatic verification on the Litex side in this round and remain here as historical boundary records:

| Candidate statement | Litex result | Treatment |
| --- | --- | --- |
| `∀ a b c, a \| b → a \| (c*(b+a))` | The addition step failed (`$dvd` did not directly combine a sum) | Replaced by a product-of-two-even-numbers divisibility problem, with explicit witnesses obtained using `obtain` |
| `∀ x, x^2 = x → x = 0 ∨ x = 1` | Proof search failed | Excluded |
| `∀ x y, x*y = 1 → x ≠ 0` | Proof search failed | Excluded |
| `∀ a, ∃ b, a = 2b ∨ a = 2b+1` | Proof search failed | Excluded |

These are failed Litex authoring attempts in the recorded batch, rather than measured Lean-faster cases. Including them would require a checkable proof, possibly with more explicit steps or additional verifier support. They are retained so the selected table is not mistaken for an exhaustive result set.

In this selected batch without direct matching-theorem reuse, Litex's ratios range from 1.7× to 306×. The number of proof statements and the available general Lean tactics vary between cases.

## 4. Other statement forms and small problems (2026-10-23, third round)

The first two rounds focused on fact statements such as `forall … =>: …`. This round adds other statement forms and small showcase problems: defining a predicate and providing a witness, extracting a witness and reasoning from it, an ε-N limit-style problem from `showcases/Functions_and_Change/reciprocal.lit`, and set equality (one of Litex's three equality obligations). Cases are in `cases/statement-forms.json`, sources in `sources/statement-forms/`.

| Statement form | Problem | Litex approach | Lean approach | Length: Litex DF* ↓ | Length: Lean DF* ↓ | Litex time (ms) ↓ | Lean time (ms) ↓ | Lean time ÷ Litex time |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| Predicate definition + witness | Define oddness and witness that 7 is odd | `prop odd(a Z): exist t Z st {a = 2*t+1}`; `witness $odd(7) from 3` | `∃ t : Int, (7:Int) = 2*t + 1`; `⟨3, by norm_num⟩` | 0.70 | 0.63 | 0.521 | 4.575 | **8.77×** |
| Custom-predicate reasoning | Three times an odd number plus 2 is odd | `obtain k from $odd(n)`; `witness $odd(3*n+2) from 3*k+2:` + equality chain | `rintro n ⟨k, hk⟩`; `⟨3*k + 2, by omega⟩` | 1.14 | 0.70 | 6.810 | 36.353 | **5.34×** |
| Limit-style reasoning (ε-N) | The reciprocal sequence `1/n` becomes arbitrarily small | Define `a(n)=1/n`, do two concrete calculations, then `claim ? forall ε R+: exist n N+ st {a(n) < ε}` | `obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε`; take `n+1` | 1.29 | 0.95 | 9.553 | 35.269 | **3.69×** |
| Set-equality obligation | `A ∪ B = B` when `A ⊆ B` | `forall A,B power_set(R): A $subset B =>: union(A,B) = B` | `ext x` in both directions, or `Set.union_eq_right.mpr h` | 0.46 | 0.63 | 0.186 | 1.217 | **6.53×** |

Three measurement details matter:

- **Definitions are charged differently.** Litex's `prop`/`have fn` must appear in its session, so their definitions are included in its timing. The Lean side uses an expanded statement for the predicate example or an already-loaded lemma for the limit example. In those three examples, Litex also performs a definition step and still has lower measured times.
- **The set-equality case has two Lean routes:** `ext` with both directions takes 2.321 ms (12.5×), while `Set.union_eq_right` takes 1.217 ms (6.53×). The main table uses the faster route.
- **More showcase problems were tried:** parity-by-cases from `The-Mechanics-of-Litex-Proof`, SAS from `2D_Geometry`, and problems from `imo_inequalities` did not meet the selection criteria (ratio below 1, or unequal workloads), so they are excluded.

## 5. Historical coverage of the measured batches

Against the Litex manual's statement dictionary (S01–S52) and object dictionary (O01–O62), the following features **were measured**:

| Litex feature | Coverage |
| --- | --- |
| Atomic facts, conjunction, disjunction, equality chains | Measured (zero products, exact calculation chains, polynomial identities) |
| Universal facts, shared premises, `=>:` scopes | Measured (21 quantifier cases) |
| Existence, witnesses, unique existence, existence elimination (S35–S38) | Measured (including a nonempty-set witness) |
| Local `claim`, `obtain`, theorem release (S25, S33) | Measured (√2, existence elimination, named-theorem reuse) |
| Contradiction, cases, induction (S39, S40, S42) | Measured (one case each) |
| Expression functions, guarded functions, piecewise definitions, cases (S01, S11, S21, S22) | Measured (4 included cases; the recursive case did not meet selection criteria) |
| Concrete predicates and `by def` (S14) | Measured |
| Structures and field access (S16) | Measured |
| Named-theorem declaration and use (S18) | Measured |
| Exact evaluation and closed calculation (S51) | Measured (arithmetic, logarithms, factorials, primality, radicals) |
| Set operations: union, intersection, difference, power sets, inclusion (O54–O59) | Measured (distributivity, De Morgan, monotonicity, power-set cardinality) |
| Functions: range, composition, universal quantification over functions | Measured |
| Finite sums and finite-set sums (related to S44) | Measured (4 forms of summation) |
| Trigonometry, logarithms, exponentials, radicals, factorials, gcd, primality, continuity, derivatives | Measured (1–3 cases each) |

Directions **not covered in those batches**, suggested for later measurement:

| Direction | Motivation | Expected difficulty |
| --- | --- | --- |
| Limits and integrals (continuity was covered) | Analysis is a focus of native Litex interfaces; substantial proofs are useful comparison candidates | The original attempt used `lim(fn(t R) R {t^2},3)=9` (now `fn_lim(fn(t R) R {t^2},3)=9`). It failed Litex WD before proof checking; it needed the real accumulation-point condition at 3 and a continuity-to-limit step. Compare complete programs rather than a bare limit expression |
| Strong induction and minimal counterexamples (S43) | Contrast with ordinary induction (4.01×) | Establish the exact Litex induction-scope pattern first |
| Function preimages and replacement images (S09, S10) | Distinct Litex statement forms | Choose corresponding `Set.image`/`Set.preimage` encodings in Lean |
| Set and function extensionality (S45, S46) | Compare with Lean's direct treatment of function equality | Litex needs the full domain conditions, which add source text |
| Template declaration families and reusable proof strategies (S17, S20) | Compare reuse mechanisms with Lean `variable`/`macro`/tactics | Fix the same-task criterion before choosing one of several possible correspondences |
| Reflexive, symmetric and transitive rule registration (S48–S50) | Compare custom-predicate rules with Lean `instance`/`simp` lemmas | Construct a minimal custom-predicate example |
| Trust, axioms, choice and Zorn's lemma (S23, S24, S30–S32) | Compare with Lean's `Classical.choice`/`propext` dependencies | This concerns trust boundaries as well as time |
| Multi-file projects and `-r` loading (module_manager) | Real mathematical libraries use modules | Compare an initial whole-library check and incremental checks |
| `-lean` compilation and subsequent Lean rechecking | Measure the Litex-to-Lean path | Include both Litex checking and Lean checking in the total |
| `-extractpython` / `-extractc` | Compare numerical/algorithmic extraction | Contrast with Lean's `native_decide` and `#eval` |
| `-latex` and reading mode | Reader/textbook output | Compare output quality rather than checking speed |
| Feedback for unverifiable input (negative cases) | Rejection latency and explanation quality matter in AI/interactive workflows | Define diagnostic-quality measures as well as milliseconds |
| Large theorem libraries (AM-GM, Cauchy–Schwarz, geometry) | A library-building workload from scratch | Both systems need comparable initial mathematical contexts; authoring may take hours |

The coverage list was chosen to investigate statements combining domains, quantifiers and several reasoning steps, where Lean may need tactics or explicit proof terms. Direct one-line lemmas remain important controls; they do not determine which system is faster without measurement.

---

## 6. Reproduction

From the repository root:

```sh
cargo build --release
python3 examples/litex_vs_lean_speed/harness/bench.py validate   # Validate both sides case by case
python3 examples/litex_vs_lean_speed/harness/bench.py measure    # Measure timings (about 2–3 minutes)
```

- `validate` runs each Litex file with the release executable and compiles every Lean route into a `#print axioms` file, checking that `sorryAx` is absent.
- `measure` reuses the same sources. Litex compiles a Rust timer linked to `liblitex.rlib` (30 warm samples per process, three processes); Lean uses `#probe` (7 warm samples per process, three processes).
- The Lean environment gets `LEAN_PATH` through `lake env` in `showcases/litex_to_lean_adapter`. Without that Adapter project, set the `LEAN_PATH` environment variable explicitly.
- To change cases, edit `cases/new-round.json` (or pass `--cases`). `validate` generates per-case files under the configured `sources/` directory.

## 7. What these measurements do not establish

- No overall speed ranking of Litex and Lean. Cases are selected, and sample counts, binary snapshots and machine loads differ. The five earlier batches used binaries built at different times.
- No isolated kernel-reduction comparison. Lean includes proof construction and synchronous kernel checking; Litex includes parsing, WD, verification and evidence construction. Their interval definitions differ.
- The older checking-path tables exclude mathematical authoring time, editor incremental checking, memory use, startup and imports. The newer whole-process table includes startup and imports.
- Each Lean route is only the **tested route in that round**, not a lower bound on attainable Lean time. Litex also uses its default builtin-rule/strategy search rather than a hand-optimized proof for every statement.
- The second round's 7 multi-step statements were selected without matching-theorem reuse, not systematically enumerated. A different collection may have a different ratio distribution. Other first/second-round cases were chosen for domain coverage and do not estimate domain averages.
- The older checking-path batches retain only Litex-faster cases (ratio > 1), so those tables omit directions where Lean is faster. The newer unscreened batch linked above retains both directions.

<!-- quantitative-iteration-code:start -->
## 8. Quantitative iteration: complete sources for both systems

The six files below are byte-identical to the inputs of the historical measurements above. Each pair proves the same mathematical statement. Litex uses guarded functions; Lean's conclusions are restricted to the same valid parameters. The record does not equate their underlying out-of-domain conventions.

See [math_collections.md](sources/quantitative-iteration/math_collections.md) for the mathematical design and support boundaries. These prove single-step formulas and bounds on supplied recurrences; they do not construct general algorithm trajectories or verify floating-point rounding.

<a id="iteration-parametric-newton"></a>

### 8.1 Parametric Newton step

Positivity, an exact residual identity and a post-update square lower bound for arbitrary a>0 and x>0, reused at a=9 and x=4.

#### Litex

[Source](sources/quantitative-iteration/litex/01_parametric_newton.lit); whole-process samples (s): `0.216478, 0.212586, 0.191081`.

```litex
# Exact-real comparison experiment; see ../math_collections.md.

have fn newton(a R+, x R+) R = (x + a / x) / 2

thm newton_positive:
    ? forall a, x R+:
        newton(a, x) > 0
    a / x > 0
    x + a / x > 0

thm newton_residual_identity:
    ? forall a, x R+:
        4 * x^2 * (newton(a, x)^2 - a) = (x^2 - a)^2

thm newton_above_root:
    ? forall a, x R+:
        newton(a, x)^2 >= a
    4 * x^2 > 0
    newton(a, x)^2 - a = (x^2 - a)^2 / (4 * x^2) >= 0

newton(9, 4) = (4 + 9 / 4) / 2 = 25 / 8

by thm newton_above_root(9, 4) => newton(9, 4)^2 >= 9
```

#### Lean / Mathlib

[Source](sources/quantitative-iteration/lean/01_parametric_newton.lean); whole-process samples (s): `14.163907, 60.180296, 67.659174`.

```lean
import Mathlib
set_option Elab.async false

namespace ParametricNewton
noncomputable section

def newton (a x : ℝ) : ℝ := (x + a / x) / 2

theorem newton_positive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < newton a x := by
  unfold newton
  positivity

theorem newton_residual_identity {a x : ℝ} (_ha : 0 < a) (hx : 0 < x) :
    4 * x ^ 2 * (newton a x ^ 2 - a) = (x ^ 2 - a) ^ 2 := by
  unfold newton
  field_simp [ne_of_gt hx] <;> ring

theorem newton_above_root {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    a ≤ newton a x ^ 2 := by
  have hp : 0 < 4 * x ^ 2 := by positivity
  have hid : newton a x ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
    apply (eq_div_iff (ne_of_gt hp)).2
    calc
      (newton a x ^ 2 - a) * (4 * x ^ 2) =
          4 * x ^ 2 * (newton a x ^ 2 - a) := by ring
      _ = (x ^ 2 - a) ^ 2 := newton_residual_identity ha hx
  have hnonneg : 0 ≤ newton a x ^ 2 - a := by
    rw [hid]
    positivity
  linarith

example : newton 9 4 = 25 / 8 := by norm_num [newton]
example : (9 : ℝ) ≤ newton 9 4 ^ 2 :=
  newton_above_root (by norm_num) (by norm_num)

#print axioms newton_positive
#print axioms newton_residual_identity
#print axioms newton_above_root
end
end ParametricNewton
```

<a id="iteration-quadratic-descent"></a>

### 8.2 Gradient descent on a quadratic

The exact decrease for a one-dimensional positive-curvature quadratic, nonincrease under a stable step size, and strict decrease away from the minimizer.

#### Litex

[Source](sources/quantitative-iteration/litex/02_quadratic_descent.lit); whole-process samples (s): `2.880947, 2.905032, 2.952233`.

```litex
# Exact-real comparison experiment; see ../math_collections.md.

have fn energy(a R+, b, x R) R = a * (x - b)^2 / 2

have fn gradient_step(a R+, b, eta, x R) R = x - eta * a * (x - b)

thm gradient_error_identity:
    ? forall a R+, b, eta, x R:
        gradient_step(a, b, eta, x) - b = (1 - eta * a) * (x - b)

thm gradient_drop_identity:
    ? forall a R+, b, eta, x R:
        energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, gradient_step(a, b, eta, x)) = a * (gradient_step(a, b, eta, x) - b)^2 / 2 = a * ((1 - eta * a) * (x - b))^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = a * (x - b)^2 / 2 - a * ((1 - eta * a) * (x - b))^2 / 2 = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2

thm gradient_descent:
    ? forall a R+, b, eta, x R:
        eta > 0
        eta * a < 2
        =>:
            energy(a, b, gradient_step(a, b, eta, x)) <= energy(a, b, x)
    eta * a^2 > 0
    eta * a^2 * (2 - eta * a) >= 0
    eta * a^2 * (2 - eta * a) * (x - b)^2 >= 0
    by thm gradient_drop_identity(a, b, eta, x) => energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) >= 0

thm gradient_strict_descent:
    ? forall a R+, b, eta, x R:
        eta > 0
        eta * a < 2
        x != b
        =>:
            energy(a, b, gradient_step(a, b, eta, x)) < energy(a, b, x)
    x - b != 0
    eta * a^2 > 0
    eta * a^2 * (2 - eta * a) > 0
    eta * a^2 * (2 - eta * a) * (x - b)^2 > 0
    by thm gradient_drop_identity(a, b, eta, x) => energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) = eta * a^2 * (2 - eta * a) * (x - b)^2 / 2
    energy(a, b, x) - energy(a, b, gradient_step(a, b, eta, x)) > 0

by thm gradient_strict_descent(2, 3, 1 / 4, 5) => energy(2, 3, gradient_step(2, 3, 1 / 4, 5)) < energy(2, 3, 5)
```

#### Lean / Mathlib

[Source](sources/quantitative-iteration/lean/02_quadratic_descent.lean); whole-process samples (s): `13.893024, 28.775592, 21.303137`.

```lean
import Mathlib
set_option Elab.async false

namespace QuadraticDescent
noncomputable section

def energy (a b x : ℝ) : ℝ := a * (x - b) ^ 2 / 2
def gradientStep (a b eta x : ℝ) : ℝ := x - eta * a * (x - b)

theorem gradient_error_identity {a b eta x : ℝ} (_ha : 0 < a) :
    gradientStep a b eta x - b = (1 - eta * a) * (x - b) := by
  dsimp [gradientStep]
  ring

theorem gradient_drop_identity {a b eta x : ℝ} (ha : 0 < a) :
    energy a b x - energy a b (gradientStep a b eta x) =
      eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
  unfold energy
  rw [gradient_error_identity ha]
  ring

theorem gradient_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) :
    energy a b (gradientStep a b eta x) ≤ energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hdrop : 0 ≤ eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

theorem gradient_strict_descent {a b eta x : ℝ} (ha : 0 < a)
    (heta : 0 < eta) (hstep : eta * a < 2) (hxb : x ≠ b) :
    energy a b (gradientStep a b eta x) < energy a b x := by
  have hpos : 0 < 2 - eta * a := by linarith
  have hne : x - b ≠ 0 := sub_ne_zero.mpr hxb
  have hdrop : 0 < eta * a ^ 2 * (2 - eta * a) * (x - b) ^ 2 / 2 := by
    positivity
  have hid := gradient_drop_identity (b := b) (eta := eta) (x := x) ha
  linarith

example : energy 2 3 (gradientStep 2 3 (1 / 4) 5) < energy 2 3 5 :=
  gradient_strict_descent (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms gradient_error_identity
#print axioms gradient_drop_identity
#print axioms gradient_descent
#print axioms gradient_strict_descent
end
end QuadraticDescent
```

<a id="iteration-perturbed-geometric"></a>

### 8.3 Perturbed geometric recurrence bound

From a supplied real sequence indexed by natural numbers and a recurrence inequality, prove a closed-form upper bound and specialize it to zero perturbation. Perturbations may be arbitrary real numbers.

#### Litex

[Source](sources/quantitative-iteration/litex/03_perturbed_geometric.lit); whole-process samples (s): `1.319137, 1.484209, 1.351820`.

```litex
# Exact-real comparison experiment; see ../math_collections.md.

forall q R:
    q < 1
    =>:
        1 - q > 0
        1 - q != 0

have fn bound(q R+, c, d R, n N: q < 1) R = q^n * c + d * (1 - q^n) / (1 - q)

thm bound_zero:
    ? forall q R+, c, d R:
        q < 1
        =>:
            bound(q, c, d, 0) = c
    1 - q != 0

thm bound_step:
    ? forall q R+, c, d R, n N:
        q < 1
        =>:
            bound(q, c, d, n + 1) = q * bound(q, c, d, n) + d
    1 - q != 0
    have t R+ = q^n
    q^(n + 1) = q^n * q^1 = t * q
    (t * q) * c + d * (1 - t * q) / (1 - q) = q * (t * c + d * (1 - t) / (1 - q)) + d
    bound(q, c, d, n + 1) = q * (t * c + d * (1 - t) / (1 - q)) + d = q * bound(q, c, d, n) + d

thm affine_recurrence_bound:
    ? forall err fn(idx N) R, q R+, d R, n N:
        q < 1
        forall j N:
            err(j + 1) <= q * err(j) + d
        =>:
            err(n) <= bound(q, err(0), d, n)
    by induc n from 0:
        ? err(n) <= bound(q, err(0), d, n)
        ? from n = 0:
            by thm bound_zero(q, err(0), d) => bound(q, err(0), d, 0) = err(0)
        ? induc:
            err(n + 1) <= q * err(n) + d <= q * bound(q, err(0), d, n) + d = bound(q, err(0), d, n + 1)

thm noiseless_affine_bound:
    ? forall err fn(idx N) R, q R+, n N:
        q < 1
        forall j N:
            err(j + 1) <= q * err(j)
        =>:
            err(n) <= q^n * err(0)
    claim:
        ? forall j N:
            err(j + 1) <= q * err(j) + 0
        q * err(j) + 0 = q * err(j)
    1 - q != 0
    bound(q, err(0), 0, n) = q^n * err(0) + 0 * (1 - q^n) / (1 - q) = q^n * err(0) + 0 = q^n * err(0)
```

#### Lean / Mathlib

[Source](sources/quantitative-iteration/lean/03_perturbed_geometric.lean); whole-process samples (s): `13.798624, 36.547467, 17.129896`.

```lean
import Mathlib
set_option Elab.async false

namespace PerturbedGeometric
noncomputable section

def bound (q c d : ℝ) (n : ℕ) : ℝ :=
  q ^ n * c + d * (1 - q ^ n) / (1 - q)

theorem bound_zero {q c d : ℝ} (_hq0 : 0 < q) (_hq1 : q < 1) :
    bound q c d 0 = c := by
  simp [bound]

theorem bound_step {q c d : ℝ} (_hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    bound q c d (n + 1) = q * bound q c d n + d := by
  have hden : 1 - q ≠ 0 := by linarith
  dsimp [bound]
  rw [pow_succ]
  field_simp [hden] <;> ring

theorem affine_recurrence_bound (err : ℕ → ℝ) {q d : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j + d) :
    err n ≤ bound q (err 0) d n := by
  induction n with
  | zero => simp [bound]
  | succ n ih =>
      calc
        err (n + 1) ≤ q * err n + d := hrec n
        _ ≤ q * bound q (err 0) d n + d :=
          by linarith [mul_le_mul_of_nonneg_left ih (le_of_lt hq0)]
        _ = bound q (err 0) d (n + 1) := (bound_step hq0 hq1 n).symm

theorem noiseless_affine_bound (err : ℕ → ℝ) {q : ℝ} (n : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrec : ∀ j, err (j + 1) ≤ q * err j) :
    err n ≤ q ^ n * err 0 := by
  have h := affine_recurrence_bound err n hq0 hq1 (d := 0)
    (fun j => by simpa using hrec j)
  simpa [bound] using h

#print axioms bound_zero
#print axioms bound_step
#print axioms affine_recurrence_bound
#print axioms noiseless_affine_bound
end
end PerturbedGeometric
```

The recorded batch passed six positive validations, twelve expected-rejection checks and eighteen repeated positive checks. Controls for zero inputs, an incorrect residual, excessive step size, strict decrease at the minimizer, q=1, and a missing noise term remain in the raw records. Negative fixtures, platform binaries and local work logs are not published here as positive source examples.

The copies can be checked with release Litex's `-strict -f <file>` and a Mathlib-configured `lake env lean <file>`. The existing `harness/bench.py` continues to measure its original checking-path cases; these three whole-process records are not merged into the older millisecond samples.

[Validation after relocation](results/quantitative-iteration-promotion.json): the three Litex copies separately passed strict checks with the recorded binary. The Lean copies retain their earlier successful checks through identical source hashes; relocation checks are not presented as new timing samples.
<!-- quantitative-iteration-code:end -->
