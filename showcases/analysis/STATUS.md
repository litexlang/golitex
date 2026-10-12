# Coverage and assumptions

This showcase follows natural-number induction → maps and equal cardinality →
finite products → sequence limits. Its public module is a selected development,
not a completed formalization of Terence Tao’s *Analysis I*.

## Included content

The registered sources contain a natural-number induction proof,
map/cardinality definitions and finite-product representation proofs. The
existing public sequence-limit module supplies constant convergence,
uniqueness and the `lim` selector. [README.md](README.md) and
[math_collections.md](math_collections.md) describe their statements and domains.

## Omitted for space

Decimal encodings and the proof of real uncountability are not included.
Further series, general countability and choice developments are also outside
this selected module. Partial proof fragments and examples with an unclear
statement or unspecified conditions are omitted. Omission does not establish
that a result has been proved; the broader local manuscripts remain unfinished
and contain explicit proof debt. No complete chapter or book coverage is claimed.

## Verification boundary

[verification.json](verification.json) records the strict check of the selected
sources and their reused limit dependency. Those sources contain no user
`trust`, `axiom`, `abstract_prop` or named foundation releases. The check relies
on Litex’s builtin mathematics and verifier; no Lean check or independent
kernel soundness result is claimed.

The finite-product results use positive finite lengths and supplied coordinate
conditions; they do not establish arbitrary infinite-product existence. The
limit selector applies to convergent sequences. The reused sequence-limit
source does not certify the broader local Chapter 6 translation.
