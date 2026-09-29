# Extract verified executable code (Python / C)

Experimental route: turn checked numeric definitions and `algo … by cases`
fragments into runnable Python or C. This is not a whole-Litex compiler and not
the Litex-to-Lean path.

```text
verify Litex statements
  -> select the deliberately small executable subset
  -> build one target-independent extracted program
  -> render that program through the Python or C backend
  -> reject unsupported target shapes instead of approximating them silently
```

## CLI

```sh
litex -extractpython 'have a R = 1'
litex -extractpython -f example.lit
litex -extractpython -r project

litex -extractc 'have a R = 1'
litex -extractc -f example.lit
litex -extractc -r project
```

File extraction (`-f`) requires `# [-extract]` / `# [end of -extract]` marker
pairs. Inline (`-e`) and repository (`-r`) use whole-input semantics.

## Layout

| File / dir | Role |
| --- | --- |
| `program.rs` | Target-independent IR + AST → IR |
| `source_extraction.rs` | Input shapes, markers, verify via `exec_stmt`, dispatch render |
| `python/` | Python API + rendering |
| `c/` | C99 API + rendering |

## Numerical contract

Python emits ordinary floating-point expressions. C emits a C99 translation-unit
fragment using `double`, without a generated `main`. Litex verification
establishes the source mathematics, not IEEE-754 rounding, overflow, or target
compiler behavior.

## v1 extractable surface (new kernel)

- Constants: `have a R = 1` (numeric param types)
- Functions: `algo f(x R) R by cases:` (parameters and return must be `R`)
- `have fn …` may appear in an extract block for verification but does not emit code
- Unsupported shapes fail loudly

Legacy memorial logic lived in
`scripts/memorial_legacy_src/extract_code_of_other_languages_from_litex/`.
