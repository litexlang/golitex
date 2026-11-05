# A field as its scalar-line vector space

Status: accepted checkpoint, 2026-10-31.

The scalar field itself is a vector space over that same field (LADR 1.20).
Expose scalar_space<K,F> as an actual VectorSpace<K,F,K> with tuple
(F.zero,F.add,F.mul), keeping the supplied field operations. K is nonempty
and F is an existing Field<K>. This also supplies a reusable scalar target for
coordinate evaluations, polynomial sums and later linear-map spaces.

Reuse the Field laws, field::add_mul and its explicit additive-inverse map;
do not build a second field or extend the VectorSpace struct. Publish a carrier
theorem before imported typed bindings. Probe actual R/C instances, generic
zero/negative scalar actions and false sign/carrier boundaries.

Use the current pinned Session 78083 after the inherited-space consumer.
Journal each statement, retain normal failures, materialize accepted source
under vector_space.lit, and verify saved source and imported use independently.
All new state is std source; no native or protected-type changes.

Accepted canonical source: 34 statements. Independent imported consumer: 32
statements. Three expected refusals retain context; check_scalars.py records
the exact source and pinned-binary hashes. This completes the scalar-space
increment and 1B correspondence, not the entire selected A–B/FTA target.
