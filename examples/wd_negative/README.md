# WD negatives

These files must **fail** (non-zero exit). They catch “fake Success” WD bugs
such as the former `CompositePending` path for forall under `trust`, applying
a non-function (`have f R` then `f(a)`), binder objects whose `dom_facts` /
SetBuilder `facts` are themselves ill-defined,
`fn_range` / `index_union` with a non-function argument, undefined names,
or an ordinary tuple call outside its complete `closed_range(1,n)` domain.
The zero and out-of-domain coordinate files use `pair(0)` / `pair(3)` after
a successful tuple declaration, so their rejection checks actual call WD.
Legacy `proj` and `t[i]` files test retired syntax; they do not establish
mathematical rejection of the corresponding new function-call forms.

`function_projection_return_domain.lit` rejects an unchecked `Z → N`
parameter projection before its signature can imply `-1 $in N`.
`struct_argument_domain.lit` rejects `&Box<-1>` when the header declares
`n N`, even though `-1` is a well-defined scalar expression.

```bash
target/release/litex -f <file>
# expect exit != 0
```
