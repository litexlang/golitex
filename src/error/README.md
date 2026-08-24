# Structured runtime errors

This input produces `WellDefinedError: divisor x must be non-zero`:

```litex
forall x R:
    x ^ 2 / x = x
```

```text
RuntimeError::WellDefinedError {
  line: 2,
  message: "divisor `x` must be non-zero",
  execution_phase: verify_well_definedness,
  verify_process: not_run,
  affect_environment: not_run
}
```

## Examples and boundaries

| Input | Error kind |
| --- | --- |
| `have` | `ParseError` with the expected `have` forms. |
| `1 / 0 = 0` | `WellDefinedError` before equality verification. |
| `1 = 2` | `VerifyError`/unknown proof information after successful well-definedness. |
| Reusing an already defined name incorrectly | `NameAlreadyUsedError`. |
| A nested failed proof step | Retains the outer statement, failed goal/step index, and previous cause. |

Start with [`runtime_error.rs`](runtime_error.rs); for example,
`RuntimeErrorStruct.previous_error` keeps the cause chain for a failed nested
theorem step.
