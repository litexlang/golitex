# Parsing Litex

`1 + 1 = 2` becomes `Stmt::Fact`, while `have a R = 1` becomes `Stmt::DefObjStmt`.

```litex
forall x R:
    x = x
```

```text
Tokenizer.parse_blocks("1 + 1 = 2")
  -> TokenBlock([1, +, 1, =, 2])
Runtime.parse_stmt(block)
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
| [`parse_stmt.rs`](parse_stmt.rs) | Dispatches the first token `forall`, `have`, `claim`, or a bare fact. |
| [`parse_fact.rs`](parse_fact.rs) | Builds equality, conjunction, chain, existential, and universal facts. |
| [`parse_def_stmt.rs`](parse_def_stmt.rs) | Parses definition settings, templates, structs, propositions, trust definitions, and shared definition-header rules. |
| [`parse_have_object_stmt.rs`](parse_have_object_stmt.rs) | Parses object, tuple, Cartesian, sequence, finite-sequence, and matrix `have` definitions. |
| [`parse_have_function_stmt.rs`](parse_have_function_stmt.rs) | Parses equality, case-based, induction, and unique-existence function definitions. |
| [`parse_obtain_and_algorithm_stmt.rs`](parse_obtain_and_algorithm_stmt.rs) | Parses `obtain`, preimage definitions, and algorithm branches. |
| [`parse_obj.rs`](parse_obj.rs) | Owns object-expression precedence, numeric literals, call/field postfixes, and function-set syntax, such as `x + 1` and `f(x)`. |
| [`parse_primary_obj.rs`](parse_primary_obj.rs) | Dispatches primary keyword and atom forms, including scalar, set, sequence/matrix, Cartesian, and iterated operators such as `sin(x)` and `sum(1, n, f)`. |
| [`parse_obj_collections.rs`](parse_obj_collections.rs) | Parses argument groups, `unfold`, intervals, replacements, set builders, and set literals such as `{1, 2}`. |
| [`parse_reference_obj.rs`](parse_reference_obj.rs) | Resolves bare and module-qualified names, struct views, field carriers, and template-backed reference types. |
