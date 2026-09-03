# Extract verified executable code from Litex

`litex -extractpython 'have a R = 1'` emits `a = 1.0`, while
`litex -extractc 'have a R = 1'` emits `double a = 1.0;`.

```text
verify Litex statements
  -> select the deliberately small executable subset
  -> build one target-independent extracted program
  -> render that program through the Python or C backend
  -> reject unsupported target shapes instead of approximating them silently
```

The shared extraction boundary lives in [`program.rs`](program.rs) and
[`source_extraction.rs`](source_extraction.rs). Target syntax belongs only in
[`python/`](python/) and [`c/`](c/). These backends extract computations; they
do not replay proofs and do not share the whole-system responsibility of the
StmtResult-to-Lean compiler.

The current numerical contract is intentionally narrow. Python emits ordinary
Python floating-point expressions. C emits a C99 translation-unit fragment
using `double`, without a generated `main`. Litex verification establishes the
source mathematics, not IEEE-754 rounding, overflow, or target compiler
behavior.

Example commands use direct source, marked file, or repository extraction:

```sh
litex -extractpython 'have a R = 1'
litex -extractpython -f example.lit
litex -extractpython -r project

litex -extractc 'have a R = 1'
litex -extractc -f example.lit
litex -extractc -r project
```

The `-f` forms require explicit source regions:

```litex
# [-extract]
have fn increment(x R) R = x + 1
# [end of -extract]

increment(1) = 2

# [-extract]
have algo for increment(x):
    x + 1
# [end of -extract]
```

Whole trimmed marker lines delimit each region. File extraction replaces every
unselected line with a blank line, concatenates the selected statements in
source order, and gives only that self-contained virtual source to the existing
verifier and backend. Blank-line padding preserves original source locations.
Missing or malformed markers fail instead of falling back to whole-file
extraction. Inline and repository extraction keep their existing whole-input
semantics.

The retired `-python -e` command is not an alias for the new interface.
