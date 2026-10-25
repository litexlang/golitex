# Imported topology foundations

main.lit compares discrete and indiscrete topologies on the same two points,
proves the reverse identity discontinuous, verifies a nonidentity swap and its
self-composition as homeomorphisms, and checks connectedness/clopen behavior.
Both named space constructors are exercised on empty carriers too.

contracts/main.lit is an independent project with all 28 full-domain theorem
calls. readme/main.lit is exactly the short std README excerpt. Each of 22
negative projects verifies its entire setup, then rejects only the last
statement at the phase in negative/expected.json. They test topology laws,
actual carrier/codomain bounds, missing continuity/closedness/inverse equations,
non-surjective image claims and continuous bijections with discontinuous inverse.

Run from the repository root:

```bash
python3 examples/topology/foundations/check.py
```

The checker also copies std into archive and shared-data installation layouts,
removes the LITEX_STD_PATH override, runs the real CLI there, and compares all
std/WiX payload paths and component references. All positive source excludes
trust and user axioms. This is a focused topology gate.
