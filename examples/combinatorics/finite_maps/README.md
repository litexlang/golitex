# Finite maps and counting from std

The 50-statement caller obtains an actual collision pair for a three-to-two
map, then an omitted value for an inclusion from two to three elements.
It checks a surjective collision bound, equal-size injection and surjection
criteria, disjoint partition counts, singleton deletion and empty sets.

identity_three and cycle_three are injections in opposite directions and
individually bijective, but cycle_three(identity_three(0))=1, so the two supplied
maps are not asserted to be mutual inverses. An empty-to-singleton function
also exercises the omitted-value result.

contracts/main.lit independently cites all ten complete theorem signatures;
it has no concrete caller prefix. readme/main.lit checks the std excerpt.
Each of 24 negative projects must accept all setup and reject only its last
statement at negative/expected.json's semantic phase. The infinite-source
case rejects invalid use of a finite theorem; it does not deny an infinite
map may have a collision.

```bash
python3 examples/combinatorics/finite_maps/check.py
```

The checker includes strict source/callers/contracts/README, actual archive
and shared-data installed imports with LITEX_STD_PATH absent, and full std/WiX
payload/component agreement. No Lean or global release certification is implied.
