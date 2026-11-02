# Set laws and the Russell diagonal

This module adds four source proofs above native sets, bounded builders,
union, intersection, relative complement and extensional equality. Ordinary
Boolean algebra laws remain native; their operations are not redefined here.

```ini
[import std]
Sets = set_laws
[alias]
sets = Sets::main
[export]
main = "./main.lit"
```

| Theorem after `sets::` | Contract |
| --- | --- |
| `set_with_member_is_nonempty(S,x)` | A supplied member `x in S` proves `$is_nonempty_set(S)` using the existing native nonempty-set witness interface. |
| `singleton_union_display(a,b)` | If `a!=b`, the displayed set `{a,b}` equals `union({a},{b})`. The parameters are arbitrary objects in Litex's pure-set foundation, including numbers. |
| `relative_complement_partition(X,A)` | For `A in power_set(X)`, its union with `X` minus `A` is `X`, and their intersection is empty. |
| `russell_diagonal_outside(U)` | For every set `U`, the bounded diagonal `{x U:not x $in x}` is not a member of `U`. Its proof uses bounded separation and logic, without Regularity. |

For an unordered pair allowing equal entries, use the existing expression
`union({a},{b})`. This is defined even when `a=b`, when it equals `{a}`.
The displayed form `{a,b}` requires `a!=b`; that syntactic condition is not
added to the mathematical concept of an unordered pair.

For example, the Russell result excludes the diagonal from a powerset too:

```litex
release thm sets::russell_diagonal_outside(power_set(N))
not {x power_set(N):not x $in x} $in power_set(N)
```

The results follow the source order of Tao, *Analysis I*, the nonempty-set
convention preceding 3.1.6, then 3.1.13, 3.1.28(g)
and the rejection of unrestricted comprehension in 3.2. The last theorem
constructs a bounded counterexample for every proposed universal set; it
does not introduce an unrestricted builder or treat the rejected Axiom 3.8
as a foundation. These proofs use the existing pure-set interpretation.

Verification records and unfinished chapter material remain in the local
`experiments/` workspace. No kernel change, user axiom, source trust or Lean
replay is included.
