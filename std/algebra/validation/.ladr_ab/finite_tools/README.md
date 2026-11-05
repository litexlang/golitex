# Finite-space tools acceptance

The strict source checkpoint targets infinite_dimension.lit and verifies all
registered algebra predecessors. The independent subspace file has 15 claims
matching the original source hypotheses. The main caller has 66 statements,
including coordinate laws, actual zero/whole complements, a dependent singleton,
empty independent lists, actual infinite R/C scalar sequence spaces, nonreal
zero extension and length zero.

Four expected refusals check an independent empty list, a false direct sum,
false infinite dimension for the plane and a false nonzero extension tail.
The valid tail remains available after each refusal. See check.py.

Run check.py with LITEX_CHECK_BINARY set to the current release executable. Each
clean file requires strict exit 0 and successful Normal JSON, with all target
statements accepted and no errors or hard termination. Source snapshots include
the executable, algebra manifest and registered source files. Every invocation
executes the source, subspace, imported-caller and refusal checks. No disk JSON
cache or receipt is read or written.

The initial main-caller failure lacked an explicit scalar_space tuple equality
before projecting its zero; the corrected caller adds that equality. No source
theorem was weakened. New source files contain no axiom or trust.
