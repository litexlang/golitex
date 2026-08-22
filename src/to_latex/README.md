# LaTeX rendering

`litex -latex -e '1 = 1'` produces the display fragment `\[ 1 = 1 \]`.

```text
parse each top-level Litex statement
  -> call Stmt::to_latex_string
  -> wrap each nonempty result in \[ ... \]
  -> preserve project [export] order for -f and -r targets
```

## Examples and boundaries

| Input | Output example |
| --- | --- |
| `1 = 1` | `\[ 1 = 1 \]`. |
| `forall x R:`<br>&nbsp;&nbsp;`x = x` | `\forall (x \in \mathbb{R}), x = x`. |
| A project with `main.lit` then `theorem.lit` | Concatenates fragments in `[export]` order. |
| A syntactically invalid `have` | Returns a parse error instead of partial LaTeX. |
| A false but parseable fact such as `1 = 2` | Still renders, because LaTeX conversion is a parse-only path. |

Start with [`to_latex_pipeline.rs`](to_latex_pipeline.rs) for project order and [`to_latex_string.rs`](to_latex_string.rs) for examples such as sums, sets, functions, and quantified facts.
