# Annotation Guide

This guide operationalizes one narrow question: when a mathematical textbook
sentence-like unit advances the discourse, is its main payload a mathematical
fact, proof control, both, or neither?

## Unit of analysis

Annotate a sentence-like discourse unit. A unit may be a complete prose
sentence, a displayed definition or theorem statement, or a short formula-led
sentence broken across OCR lines. Ignore structural tokens such as `Proof.`,
page headers, page numbers, and footnote markers.

The pilot records repository-relative source line ranges and a cue of at most
twelve words. It does not copy the source passage. When an OCR line contains
multiple units, the cue distinguishes them.

## Labels

### `F` — fact-oriented

The unit's main payload states what holds, what is assumed, what is defined,
or what must be shown. This includes:

- definitions, axioms, theorem statements, and explicit goals;
- hypotheses and derived intermediate claims;
- equations, inequalities, membership, existence, and uniqueness claims; and
- formal notation declarations whose mathematical meaning is the point.

A goal sentence such as “we wish to show ...” is `F`: its payload is the next
fact, even though it occurs inside a proof.

### `H` — how-oriented

The unit's main payload controls or evaluates the proof route without also
asserting a substantial mathematical fact. This includes:

- choosing induction, contradiction, cases, or a fixed parameter;
- opening or closing a proof phase;
- explaining why a tempting proof route is unavailable; and
- pure proof-navigation language.

### `FH` — mixed fact and how

The unit both states a substantial mathematical fact and exposes its proof
role or local justification. Typical forms include:

- a fact followed by “by definition”, “since”, or a theorem citation;
- an induction hypothesis paired with the next goal; and
- a conclusion paired with an explicit closure or consequence marker.

Do not use `FH` merely because a fact occurs inside a proof. Both payloads
must be visible in the same unit.

### `E` — exposition outside the fact/how balance

The unit is primarily historical, motivational, organizational, pedagogical,
or terminological commentary. Forward references, rhetorical questions, and
“see exercise” proof placeholders are `E`. A formal definition remains `F`;
discussion about why a convention is convenient is normally `E`.

## Decision test

Ask two independent questions:

1. If proof-control and justification words were removed, would a substantial
   mathematical assertion remain?
2. If the mathematical assertion were replaced by a placeholder, would a
   meaningful proof move or verification route remain?

Answer yes/no as follows:

| Fact payload | How payload | Label |
| --- | --- | --- |
| yes | no | `F` |
| no | yes | `H` |
| yes | yes | `FH` |
| no | no | `E` |

## Aggregation

Keep the four raw counts. Among proof-relevant units (`F + H + FH`), report:

```text
fact lower    = F / relevant
fact midpoint = (F + 0.5 * FH) / relevant
fact upper    = (F + FH) / relevant
```

The how-oriented band is symmetric. The midpoint is a descriptive convention,
not a discovered truth; the lower and upper bounds expose sensitivity to mixed
units.

For a book-level study, annotate clauses as a second unitization and compare
the result. A sentence can contain several fact clauses and one short proof cue,
so sentence-only counts may overstate the surface area of proof control.

## Adjudication

Two annotators should independently label at least 20% of the probability
sample. Resolve disagreements only after preserving both original labels.
Report the confusion matrix and Cohen's kappa (or an equivalent nominal-label
agreement statistic). Do not automate the remaining book unless held-out
agreement is acceptable and failure patterns are disclosed.
