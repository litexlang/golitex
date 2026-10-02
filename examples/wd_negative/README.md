# WD negatives

These files must **fail** (non-zero exit). They catch “fake Success” WD bugs
such as the former `CompositePending` path for forall under `trust`, applying
a non-function (`have f R` then `f(a)`), binder objects whose `dom_facts` /
SetBuilder `facts` are themselves ill-defined, `proj` on a non-cart,
`fn_range` / `index_union` with a non-function argument, undefined names,
or tuple index outside `N+` / beyond `tuple_dim`.

`function_projection_return_domain.lit` rejects an unchecked `Z → N`
parameter projection before its signature can imply `-1 $in N`.
`struct_argument_domain.lit` rejects `&Box<-1>` when the header declares
`n N`, even though `-1` is a well-defined scalar expression.

```bash
target/release/litex -f <file>
# expect exit != 0
```
