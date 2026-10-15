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

## Naming constraints

Choose distinct names across all files included in one extraction. Repository
extraction (`-r`) combines exports into one Python or C namespace and keeps
plain declaration names; it does not add export prefixes or detect collisions.
For example, `have shared R = 1` in one export and `have shared R = 2` in
another both verify in Litex, but Python overwrites the first value and C
rejects the duplicate definition. Prefer names such as `first_shared` and
`second_shared`, and apply the same convention to `algo` names.

For Python, avoid naming a constant, algorithm or parameter `math`. The
renderer uses `import math` and references such as `math.pi` and `math.floor`.
For example, `have math R = 2` followed by `have tau R = pi` emits
`math = 2.0` followed by `tau = math.pi`, which raises `AttributeError`.
Use a descriptive name such as `scale` for that constant instead. Also avoid
shadowing Python builtins used by generated code, such as `int`, `min` and
`max`.

C fragments may `#include <stdlib.h>` (and similar) and call helpers such as
`abort()`. Avoid Litex `have` / `algo` names that collide with those library
symbols (`abort`, `exit`, `malloc`, …); the backend does not rename or reject
them.

These naming collisions can still produce an artifact marked successful.
Check the generated program in the target language before relying on it.

## v1 extractable surface (new kernel)

- Constants: `have a R = 1` (numeric param types)
- Functions: `algo f(x R) R by cases:` (parameters and return must be `R`)
- `have fn …` may appear in an extract block for verification but does not emit code
- Unsupported shapes fail loudly

Legacy memorial logic lived in
`scripts/memorial_legacy_src/extract_code_of_other_languages_from_litex/`.
