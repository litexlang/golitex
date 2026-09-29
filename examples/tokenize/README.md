# Tokenize tracers

Surface tokenization / line-joining acceptance files.

## Acceptance

```bash
target/release/litex -f <this-file>
```

Exit 0 is enough.

## Layout

```text
line_continuation.lit      trailing \\ joins the next physical line
unicode_math_aliases.lit   Unicode math aliases share ASCII Litex semantics
```

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  target/release/litex -f "$f" || fail=1
done < <(find examples/tokenize -name '*.lit' | sort)
exit $fail
```

Also: `unicode_math_aliases.lit` (Unicode input aliases).
