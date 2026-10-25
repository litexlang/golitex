# IMO inequalities in Litex

Five official IMO inequality problems, each with a standalone Litex proof. Each
problem page gives its full hypotheses, mathematical proof idea when available,
and official source links. The proof files contain no user trust or axioms.

| Problem | Topic | Litex proof |
|---|---|---|
| [1983 P6](imo_1983_p6.md) | Triangle-side polynomial inequality and equality cases | [Proof](imo_1983_p6.lit) |
| [1995 P2](imo_1995_p2.md) | Reciprocal cubic inequality | [Proof](imo_1995_p2.lit) |
| [2001 P2](imo_2001_p2.md) | Radical inequality | [Proof](imo_2001_p2.lit) |
| [2005 P3](imo_2005_p3.md) | Fifth-power rational inequality | [Proof](imo_2005_p3.lit) |
| [2006 P3](imo_2006_p3.md) | Least constant in a quartic inequality | [Proof](imo_2006_p3.lit) |

For 1983 P6 the proof includes both directions of the equality characterization.
For 2006 P3 it proves the universal bound for all real triples and optimality of
$M=9\sqrt{2}/32$, using an explicit extremizing triple.

Run from the repository root:

```sh
cargo build --release
target/release/litex -lang en -strict -f examples/imo/inequalities/imo_2006_p3.lit
```

Replace the filename to verify another problem. Each file runs independently;
there is no module manifest or shared loading order. Commands are kept here
rather than in the mathematical proof sources.

[math_collections.md](math_collections.md) describes the proof dependencies.
[source_records.jsonl](source_records.jsonl) records the source, statement,
proof idea, exact Litex code, and verification status for each item.
[verification-2026-10-11.json](verification-2026-10-11.json) records historical
clean showcase-path runs and source hashes. Timings measure verification of supplied explicit proofs,
including their supporting lemmas; they do not measure automatic proof discovery.

The statements and proof sources were collected and developed on 2026-10-11.
The five proof files were originally promoted unchanged into the showcase and
now live in this examples collection. The separate local experiment workspace
is retained.

All five files also passed strict verification at their new paths on 2026-10-25.
See the [combined IMO index](../README.md) and [current verification record](../verification.md).
