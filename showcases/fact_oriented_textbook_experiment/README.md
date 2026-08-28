# What Do Textbook Sentences Do?

<!-- 蓝图主线：fact-oriented claim → measurable discourse question → transparent annotation protocol → stratified pilot → genre-sensitive result → honest boundary → book-scale replication -->

Litex calls its authoring interface *fact-oriented*: source preserves objects,
conditions, and facts that should hold, while the verifier searches for and
records local grounds. That design claim suggests an empirical question about
ordinary mathematical writing:

> How much textbook discourse states **what holds next**, and how much mainly
> controls **how the proof proceeds**?

This showcase makes the question measurable. It provides a public annotation
rubric, source-linked pilot data, a dependency-free validator and reporter,
and a preregistered path from a small demonstration to a defensible book-level
study.

## Run the pilot

From the repository root:

```bash
python3 -B showcases/fact_oriented_textbook_experiment/run_experiment.py validate
python3 -B showcases/fact_oriented_textbook_experiment/run_experiment.py report
python3 -B -m unittest discover \
  -s showcases/fact_oriented_textbook_experiment \
  -p 'test_*.py'
```

The corpus is the repository's local text extraction of Tao's *Analysis I* at
`scripts/Analysis/analysis-one.txt`. The CSV stores line references, short
cues, labels, and rationales; it does not republish the selected passages.
The `scripts` git submodule must therefore be checked out before validation;
a missing corpus fails closed instead of silently skipping source checks.

## The tracer result

The primary tracer is the pair of induction proofs for Lemmas 2.2.2 and 2.2.3
at source lines 1681-1703. Its 18 units produce:

| `F` | `H` | `FH` | `E` | Fact midpoint | How midpoint |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 6 | 8 | 0 | 44.4% | 55.6% |

This is a useful negative control against an easy sales story: a proof-heavy
passage does not automatically look fact-dominant at sentence level. Eight of
the eighteen units are mixed, so the result is also highly sensitive to how
mixed sentences are treated.

The complete purposive pilot adds an introductory definition/exposition slice
and an advanced definition/worked-example slice. Its generated result is in
[`RESULTS.md`](RESULTS.md). The contrast, not the pooled percentage, is the
first finding: genre changes the balance sharply.

## Experimental contract

The unit is a sentence-like discourse unit rather than a raw OCR sentence.
Displayed theorem statements and formula-led sentences count as units;
`Proof.`, page headers, and page numbers do not.

Each unit receives one label:

- `F`: a fact, condition, definition, hypothesis, intermediate claim, or goal;
- `H`: proof strategy, navigation, closure, or route availability;
- `FH`: both a mathematical assertion and explicit proof control or grounds;
- `E`: motivation, history, organization, terminology, or pedagogy outside the
  fact/how balance.

The full decision rules and edge cases are in
[`ANNOTATION_GUIDE.md`](ANNOTATION_GUIDE.md).

### Why preserve `FH`?

“By definition, the left side equals A, which equals B by the induction
hypothesis” is neither honestly pure fact nor pure method. Forced binary labels
would bury the central ambiguity. The report therefore shows raw categories,
fact-bearing/how-bearing rates, and a sensitivity interval. Its midpoint gives
half of each `FH` unit to each orientation; that split is explicitly a
convention.

## Pilot sampling design

The v0 annotations are three purposively chosen contrasts from one book:

1. introduction of the natural numbers and Peano axioms;
2. two consecutive induction proofs about addition; and
3. limit-point, limsup, and liminf definitions plus a worked example.

They test whether the rubric behaves sensibly across genres. They are not a
random sample and carry no population weights, so their pooled percentage is
not an estimate of *Analysis I* or of mathematical textbooks generally.

## Book-scale experiment

A defensible next round should freeze the following protocol before seeing its
result:

1. **Sampling frame.** Keep the mathematical body; exclude front matter,
   contents, bibliography, index, page furniture, and publisher notices.
2. **Structural strata.** Separate theorem/definition statements, proofs,
   worked examples, general exposition, and exercises.
3. **Probability sample.** Draw sentence-like units with a fixed seed within
   each stratum. Record inclusion probabilities so the pooled estimate can be
   weighted back to the book.
4. **Calibration.** Double-annotate at least 100 units and refine examples in
   the guide without changing the four label meanings.
5. **Reliability.** Double-annotate at least 20% of the final sample; publish
   the confusion matrix and agreement statistic.
6. **Primary analysis.** Report all four categories by stratum and the
   fact/how lower-midpoint-upper sensitivity bands.
7. **Unitization sensitivity.** Re-annotate a held-out subset at clause level.
   This tests whether short phrases such as “by definition” make an otherwise
   fact-rich sentence look method-heavy.
8. **Replication.** Repeat on a different author and subject before making a
   claim about textbook mathematics in general.

Preregistered hypotheses for that round:

- fact midpoint exceeds how midpoint in the weighted mathematical body;
- proof strata contain more `H` and `FH` than definition and exposition
  strata; and
- clause-level annotation raises the measured fact share relative to
  sentence-level annotation.

These are hypotheses, not conclusions from the pilot.

## Interpretation boundary

The experiment measures a discourse interface, not foundations. A textbook
may be reconstructible in set theory while rarely mentioning sets, and a
fact-oriented surface can still require author-supplied induction, cases,
witnesses, estimates, and theorem selection.

Even a fact-dominant result would not prove that Litex can verify the prose or
that its kernel is sound. It would support only a narrower motivation: a
substantial part of ordinary mathematical writing may already be organized as
objects and facts, making a fact-oriented checked interface worth testing.
