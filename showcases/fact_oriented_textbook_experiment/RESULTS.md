# Analysis I Pilot Results

This file is generated from `annotations/pilot_analysis_i.csv` by
`run_experiment.py`. The three slices are purposive contrasts, not a
probability sample of the book.

## Overall label distribution

| Label | Count | Share of all units |
| --- | ---: | ---: |
| F | 28 | 38.9% |
| H | 6 | 8.3% |
| FH | 16 | 22.2% |
| E | 22 | 30.6% |

Total annotated units: **72**.

Fact-bearing units (`F` or `FH`): **61.1%**.  
How-bearing units (`H` or `FH`): **30.6%**.  
These two bearing rates overlap because every `FH` unit belongs to both.

## Sensitivity band among proof-relevant units

`E` units are excluded here. The lower bound assigns every `FH` unit to
the opposite side; the midpoint splits `FH` equally; the upper bound
assigns every `FH` unit to the named side.

| Orientation | Lower | Midpoint | Upper |
| --- | ---: | ---: | ---: |
| Fact | 56.0% | 72.0% | 88.0% |
| How | 12.0% | 28.0% | 44.0% |

## Slice contrast

| Slice | Stratum | Units | F | H | FH | E | Fact midpoint | How midpoint |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `peano_definition_exposition` | definition_exposition | 34 | 14 | 0 | 1 | 19 | 96.7% | 3.3% |
| `addition_induction_proofs` | proof | 18 | 4 | 6 | 8 | 0 | 44.4% | 55.6% |
| `limsup_definition_example` | advanced_definition_example | 20 | 10 | 0 | 7 | 3 | 79.4% | 20.6% |

## What this pilot establishes

The same rubric detects a sharp genre effect: the induction-proof tracer
contains more explicit proof control than the definition and example
slices. Mixed units are common enough that a forced binary count would
hide material uncertainty.

It does **not** estimate the whole book. A book-level result requires the
probability sampling, double annotation, weighting, and clause-level
sensitivity analysis specified in the README.
