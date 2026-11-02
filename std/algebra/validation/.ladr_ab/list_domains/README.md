# Equal functions and their complete input domains

Status: reproduced proof gap; user selected std-only scope and deferred this item.
No kernel repair is authorized or implemented.

LADR 1.8 requires equal lists to have the same length. Native finite_seq(S,n)
uses the exact complete input domain closed_range(1,n). Fixed-length pointwise
extensionality passes, including n=0, but the checked current routes do not
recover equality of complete domains from equality of functions.

The independent main.lit gate first accepts fixed-length extensionality, then
rejects InputA=InputB under equal unary functions with complete domains InputA
and InputB. The two codomains are arbitrary upper bounds and need not be equal.
The replay receipt records one accepted control, one expected proof failure,
and the exact source and pinned binary hashes. This is observed current
behavior; it is not a proof that no further std derivation could exist.

A general proposal, not implemented syntax, is a proved builtin theorem with
one fixed six-argument contract:

```litex
# PROPOSED contract, not an available declaration.
# InputA, InputB, OutputA, OutputB: sets.
# first_map: fn(x InputA) OutputA; second_map: fn(x InputB) OutputB.
# Premise: first_map = second_map. Conclusion: InputA = InputB.
# Proposed name/arity: equal_functions_have_equal_domains/6.
```

The evidence should cite the actual function equality and both checked complete
unary signatures through shared verify. Do not infer equality of codomain upper
bounds, insert a list-specific WD branch, change AST/Env/Runtime owners, or
assume the conclusion in std. With the bridge, ordinary interval membership
proves the two natural length parameters equal, and the existing pointwise
function-extensionality direction supplies the converse.

The user selected the std-only route: keep this item deferred and continue
independent std work. A general kernel route is only a proposal and has no
authorization for implementation. The repository AGENTS.md requires separate
explicit authorization for Rust, Lean replay and targeted tests outside std.
The missing reverse implication remains unaccepted.

The source-owned todo.md preserves the provisional kernel_problem classification,
exact reproduction and the resolved scope decision.
