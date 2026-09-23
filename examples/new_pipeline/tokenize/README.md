# new_pipeline tokenize tracers

Surface tokenization / line-joining acceptance files.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough.

## Layout

```text
line_continuation.lit   trailing \\ joins the next physical line
```

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline/tokenize -name '*.lit' | sort)
exit $fail
```
