# new_pipeline WD negatives

These files must **fail** (non-zero exit). They catch “fake Success” WD bugs
such as the former `CompositePending` path for forall under `trust`, applying
a non-function (`have f R` then `f(a)`), or binder objects whose `dom_facts` /
SetBuilder `facts` are themselves ill-defined.

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <file>
# expect exit != 0
```
