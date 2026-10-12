# IMO inequalities in Litex

Six official IMO inequality problems, with five standalone Litex proofs. Each
problem page gives its full hypotheses, mathematical proof idea when available,
and official source links. The proof files contain no user trust or axioms.

| Problem | Topic | Litex proof |
|---|---|---|
| [1975 P1](imo_1975_p1.md) | Ordered sequences and permutations | Statement only; not attempted |
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
target/release/litex -lang en -strict -f showcases/imo_inequalities/imo_2006_p3.lit
```

Replace the filename to verify another problem. Each file runs independently;
there is no module manifest or shared loading order. Commands are kept here
rather than in the mathematical proof sources.

[math_collections.md](math_collections.md) describes the proof dependencies.
[source_records.jsonl](source_records.jsonl) records the source, statement,
proof idea, exact Litex code, and verification status for each item.
[verification.json](verification.json) records clean showcase-path runs and
source hashes. Timings measure verification of supplied explicit proofs,
including their supporting lemmas; they do not measure automatic proof discovery.

The statements and proof sources were collected and developed on 2026-10-11.
The five proof files were promoted unchanged into this showcase. The separate
local experiment workspace is retained; this directory is the maintained
showcase for these problems.
