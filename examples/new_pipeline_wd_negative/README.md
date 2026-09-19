# new_pipeline WD negatives

These files must **fail** (non-zero exit). They catch “fake Success” WD bugs
such as the former `CompositePending` path for forall under `trust`, or
applying a non-function (`have f R` then `f(a)`).

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <file>
# expect exit != 0
```
