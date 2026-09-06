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
| An identifier token starting with `__` | Preserved by the tokenizer, then rejected by `is_valid_litex_name` when used as a user-defined name; the prefix remains reserved for generated symbols, including names in Lean output. `_x` remains a valid user name. |
| A failed parse after opening a binder | Restores the saved `ParseContext`, so a broken `forall x ...` does not leak `x`. |

Object expressions bind, from tighter to looser, as postfix calls/indexing,
right-associative power, prefix `-`, multiplicative operators, and additive
operators. Thus `-t^2` parses as `-(t^2)`, while `(-t)^2` keeps the negative
value as the power base. Public authoring still uses the explicit forms.

## Start here

| File | Example |
| --- | --- |
| [`tokenizer.rs`](tokenizer.rs) | Splits `forall x R:` and its indented body into one `TokenBlock`. |
| [`statement_parsing.rs`](statement_parsing.rs) | Parses one complete statement and dispatches its first token, such as `forall`, `have`, `claim`, or a bare fact. |
| [`fact/expression.rs`](fact/expression.rs) | Builds equality, conjunction, chain, existential, and universal facts. |
| [`fact/parameter_definition.rs`](fact/parameter_definition.rs) | Parses typed and carrier-bound parameters shared by facts and definitions. |
| [`object/expression.rs`](object/expression.rs) | Owns object-expression precedence, numeric literals, call/field postfixes, and function-set syntax, such as `x + 1` and `f(x)`. |
| [`object/primary.rs`](object/primary.rs) | Dispatches primary keyword and atom forms, including scalar, set, sequence/matrix, Cartesian, and iterated operators such as `sin(x)` and `sum(1, n, f)`. |
| [`object/collections.rs`](object/collections.rs) | Parses argument groups, intervals, replacements, set builders, and set literals such as `{1, 2}`. |
| [`object/reference.rs`](object/reference.rs) | Parses bare and module-qualified names plus struct-carrier syntax. Field postfixes retain only their receiver and field name; runtime definition state resolves the carrier later. |
| [`statements/definition.rs`](statements/definition.rs) | Parses definition settings, templates, structs, propositions, trust definitions, and shared definition-header rules. |
| [`statements/have_object.rs`](statements/have_object.rs) | Parses object, tuple, Cartesian, sequence, finite-sequence, and matrix `have` definitions. |
| [`statements/have_function.rs`](statements/have_function.rs) | Parses equality, case-based, induction, and unique-existence function definitions. |
| [`statements/obtain_and_algorithm.rs`](statements/obtain_and_algorithm.rs) | Parses `obtain`, preimage definitions, and algorithm branches. |
