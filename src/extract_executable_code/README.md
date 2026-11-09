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

The launch parser produces `LaunchCommand::ExtractExecutableCode { target,
input: ExtractInput, language }`; `run_extract_executable_code` returns an
`ExtractExecutableCodeResult`. LaTeX has its own `CompileToLatex` command,
`LatexInput`, runner and result, because it renders parsed mathematics without
the verification and executable-subset selection used here.

```sh
litex -extractpython 'have a R = 1'
litex -extractpython -f example.lit
litex -extractpython -r project

litex -extractc 'have a R = 1'
litex -extractc -f example.lit
litex -extractc -r project
```

File extraction (`-f`) requires `# [-extract]` / `# [end of -extract]` marker
pairs. Inline source and repository (`-r`) use whole-input semantics.

The CLI emits one artifact JSON document. Success and failure retain `format`
(`python` / `c`), `target` (`eval` / `file` / `repository`), `path`,
`output_path`, and `language`. Success has string `content` and null `error`;
failure has null `content` and an `extraction_error` payload. `-lang` localizes
artifact keys on both paths. Example: `litex -lang zh -extractpython 'have a R = 1'`.

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

The C `lcm` helper accepts finite integer-valued doubles in
`[-2^63, 2^63)`. It checks that range before converting, computes magnitudes and
the Euclidean algorithm with unsigned integers, and forms the result as a
`double`. Inputs outside that machine range abort instead of invoking undefined
integer conversion or overflow. The C factorial helper likewise checks its
integer domain before conversion; results above `170!` are positive infinity.
These are executable-backend limits, not restrictions on mathematical Litex
integers. Nested `sign` calls evaluate each argument once through a helper.

## Naming constraints

Choose distinct names across all files included in one extraction. Repository
extraction (`-r`) combines exports into one Python or C namespace and keeps
plain declaration names; it does not add export prefixes. Duplicate constant or
algorithm names are rejected before an artifact is returned.
For example, `have shared R = 1` in one export and `have shared R = 2` in
another both verify in Litex, but extraction reports the duplicate. Use names
such as `first_shared` and
`second_shared`, and apply the same convention to `algo` names.

Python names colliding with the used `math` module and builtins are emitted
with a reserved `__litex_user_` prefix. For example, `have math R = 2` emits
`__litex_user_math = 2.0`, leaving `math.pi` available to subsequent expressions.
The source lexer reserves `__` names, so user names cannot collide with this
generated prefix.

C names colliding with C99 `math.h`, `stdlib.h`, or generated helper symbols
are emitted with `litex_user_`. Names already starting with that prefix gain
one more copy of it, which keeps the mapping distinct. Definitions, parameters,
and references all use the same mapping. Other valid source names are retained.

## v1 extractable surface (new kernel)

- Constants: `have a R = 1` (numeric param types)
- Functions: `algo f(x R) R by cases:` (parameters and return must be `R`)
- `have fn …` may appear in an extract block for verification but does not emit code
- Unsupported shapes fail loudly

Legacy memorial logic lived in
`scripts/memorial_legacy_src/extract_code_of_other_languages_from_litex/`.
