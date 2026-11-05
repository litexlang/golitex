# Finite untyped lambda calculus

This showcase constructs finite de Bruijn syntax, capture-avoiding binder
instantiation, and full one-step beta reduction under term contexts. It uses
ordinary Litex sets, functions and source proofs; it introduces no native AST,
binder, inference or runtime change. Read [main.lit](main.lit) from constructor
encodings and structural induction through substitution and the reduction examples.
The local caller's `validation/litex.config` imports this showcase with:

```ini
[import]
Lambda = ".."
[alias]
lc = Lambda::main
[export]
main = "./main.lit"
```

## Actual syntax and operations

`Term` is the least subset of native N closed under three injective,
disjoint constructors. It contains open terms and is not all of N.
`variable(index)`, `abstraction(body)` and `application(left,right)` return
actual terms. Index0 denotes the nearest binder; indices extending beyond the
enclosing binders denote free variables.

The representation formulas are `3*index`, `3*body+1`, and
`3*((left+right)^2+left)+2`. Their injectivity, distinct tags and strict subterm
rank inequalities are proved in source. `lambda_term_induction` gives structural
induction, and `lambda_term_root_cases` excludes junk syntax. The guarded
`variable_index`, `abstraction_body` and `application_parts` selectors are
introduced only after their unique-existence proofs. The latter has the
convenience projections `application_left` and `application_right`.

`shift(term,cutoff,amount)` raises indices at or above cutoff, increasing cutoff
under an abstraction. Amount is natural. `instantiate(term,depth,argument)`
removes the binder at depth: lower indices remain bound, the matching index
becomes `shift(argument,0,depth)`, and higher indices decrease by1. Depth
increases under an abstraction. `beta_contract(body,argument)` instantiates
depth0; its first argument is the abstraction's body.

`is_root_beta_step(source,target)` describes a root contraction.
`is_beta_step(source,target)` is its least closure under abstraction and either
side of application. It is a relation, so it retains the different possible
redex choices of untyped beta reduction.

## Proved uses

- `shift_zero(term,cutoff)` holds for every term and cutoff.
- `beta_identity(argument)` proves that the identity body returns every argument.
- `beta_avoids_capture` proves that `(lambda x. lambda y. x) y` produces the
  de Bruijn term `abstraction(variable(1))`; `capture_result_is_distinct`
  proves that this is different from the captured `abstraction(variable(0))`.
- `instantiate_variable_below/at/above`, `instantiate_abstraction` and
  `instantiate_application` expose the general substitution equations.
- `beta_under_abstraction`, `beta_in_function` and `beta_in_argument` prove
  compatible one-step closure.
- `variables_are_normal(index,target)` proves that variables have no beta
  successor. `omega_self_step` proves the actual step Omega -> Omega.

The [independent caller](validation/main.lit) uses the showcase through qualified
imports, including generic term parameters and capture-sensitive examples.
Run both saved files with:

```bash
target/release/litex -strict -lang en -f showcases/lambda_calculus/main.lit
target/release/litex -strict -lang en -f showcases/lambda_calculus/validation/main.lit
```

See [acceptance.json](validation/acceptance.json) for focused results and hashes,
and [negative_cases.json](validation/negative_cases.json) for final assertions
checked after the positive caller in a live Session. Invalid destructor calls,
negative shifts, wrong capture and spurious variable reductions are boundaries.

There are no source trust statements or user axioms. The model uses Litex's
existing classical set/function theory and natural arithmetic. Typed lambda
calculi, Church-Rosser, standardization, normalization and a general theorem
relating free-variable sets to substitution are further work. Omega's checked
self-step alone is not presented as that entire metatheory. No Lean replay is
claimed.
