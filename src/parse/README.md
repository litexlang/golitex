# Parsing Litex

`1 + 1 = 2` becomes `Stmt::Fact`, while `have a R = 1` becomes
`Stmt::Definition(DefinitionStmt::HaveObjEqualStmt(..))`.

```litex
forall x R:
    x = x
```

```text
Tokenizer.parse_blocks("1 + 1 = 2")
  -> TokenBlock([1, +, 1, =, 2])
Runtime.parse_statement(block)
  -> parse_fact(block)
  -> parse_obj(left), parse_obj(right)
  -> Stmt::Fact(EqualFact(left, right))
```

## Examples and boundaries

| Input | Parser result |
| --- | --- |
| The `forall x R:` example above | A `Stmt::Fact(Fact::ForallFact(...))`. |
| `claim:`<br>&nbsp;&nbsp;`? 1 = 1`<br>&nbsp;&nbsp;`1 = 1` | A proof-block statement with one goal and one proof step. |
| Top-level `? 1 = 1` | Rejected; `?` is only a goal inside `claim`, `example`, `thm`, `by`, or `strategy`. |
| `have` with no body | Rejected with `have: expected object definition, fn, or by preimage`. |
| A failed parse after opening a binder | Restores the saved `ParseContext`, so a broken `forall x ...` does not leak `x`. |

## Start here

| File | Example |
| --- | --- |
| [`tokenizer.rs`](tokenizer.rs) | Splits `forall x R:` and its indented body into one `TokenBlock`. |
| [`statement_parsing.rs`](statement_parsing.rs) | Parses one complete statement and dispatches its first token, such as `forall`, `have`, `claim`, or a bare fact. |
| [`fact/expression.rs`](fact/expression.rs) | Builds equality, conjunction, chain, existential, and universal facts. |
| [`fact/parameter_definition.rs`](fact/parameter_definition.rs) | Parses typed and carrier-bound parameters shared by facts and definitions. |
| [`object/expression.rs`](object/expression.rs) | Owns object-expression precedence, numeric literals, call/field postfixes, and function-set syntax, such as `x + 1` and `f(x)`. |
| [`object/primary.rs`](object/primary.rs) | Dispatches primary keyword and atom forms, including scalar, set, sequence/matrix, Cartesian, and iterated operators such as `sin(x)` and `sum(1, n, f)`. |
| [`object/collections.rs`](object/collections.rs) | Parses argument groups, `unfold`, intervals, replacements, set builders, and set literals such as `{1, 2}`. |
| [`object/reference.rs`](object/reference.rs) | Resolves bare and module-qualified names, struct views, field carriers, and template-backed reference types. |
| [`statements/definition.rs`](statements/definition.rs) | Parses definition settings, templates, structs, propositions, trust definitions, and shared definition-header rules. |
| [`statements/have_object.rs`](statements/have_object.rs) | Parses object, tuple, Cartesian, sequence, finite-sequence, and matrix `have` definitions. |
| [`statements/have_function.rs`](statements/have_function.rs) | Parses equality, case-based, induction, and unique-existence function definitions. |
| [`statements/obtain_and_algorithm.rs`](statements/obtain_and_algorithm.rs) | Parses `obtain`, preimage definitions, and algorithm branches. |
