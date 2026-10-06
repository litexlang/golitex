# Finite-product branch audit and fresh-insertion author repair

Task: continue the broad legacy/current migration audit. Scope: finite product member removal, fresh insertion, empty/list/range, constants, multiplication, pointwise and bijective reindex consumers.

The exact R/C/Q/Z member-removal multiplication identities verify, including zero factors. Insertion's direct source still misses equality search after parent WD passes. A same-target claim needs only the independently derived `a $in union(S,{a})`; its original forall reuses the actual stored proposition. Generic pointwise product equality uses `by fn_extension f=g`; the same-target claim and exact reuse pass.

The formal `finite_product_fresh_insertion.lit` previously ended with a redundant local forall and `release thm fn_set_member(f,fn(x S)R)`. The latter asks the union-domain source function to inhabit the smaller complete input domain and fails at `forall p union(S,{a}): p $in S`. Retain the literal callback restriction in the original target and the independently derived union member; remove those two proof steps. The repaired strict formal file passes. No Runtime, AST, search, domain or Rust change.

## Remaining authoring investigation (trust)

```litex
forall A finite_set,x A,f fn(k A)R:
    f(x)!=0
    =>:
        finite_set_product(set_minus(A,{x}),fn(k set_minus(A,{x}))R{f(k)})=finite_set_product(A,f)/f(x)
```

Both legacy/current direct sources fail. An explicit multiplication-removal proof passes its first step but fails the final division goal at search. This true statement is not a false control or a confirmed legacy omission. Next owner: bounded known-product/division consumer with actual scalar carrier/nonzero evidence; global permissions or state changes need discussion. This was audit triage, no trust was inserted and no exhaustive author search is claimed.

The unique-preimage enumeration fallback remains untested. List duplicates fail the distinctness WD in both versions and are not restored. [Full code, classifications, exact commands and current gates](../../../../plan/迁移的plan/legacy-finite-product-branches-audit-2026-10-06.md) and its journal retain all attempts and the prior formal failure.
