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
| [`parse_obj.rs`](parse_obj.rs) | Builds objects such as `x + 1`, `sin(x)`, or `{1, 2}`. |
