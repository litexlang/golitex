# New Pipeline Plan

## Well-definedness records and result environments

The new pipeline keeps three kinds of state distinct:

```text
VerifyState
  temporary memo and recursion guard for the current proof scope

ExecEnv
  object -> WD id records visible in that environment

Result
  verification output plus the child environments needed to inspect and
  render the result after verification
```

For an object `obj`, an `ExecEnv` records only that its well-definedness has
already been established in that environment:

```rust
HashMap<ObjKey, WellDefinednessId>
```

The lookup is environment-scoped. A child environment may see records from its
parent, but a parent does not see records created only in the child. A child WD
record is not automatically merged into the parent.

When a child environment is retained by the verification `Result`, the result
can carry that child environment (or an equivalent environment snapshot). The
renderer and later result inspection can therefore find the child object's WD
record and print it correctly, even though the parent environment never owned
that record.

The intended lookup order is:

```text
1. Check the current proof-scope VerifyState memo.
2. Check the current ExecEnv and its visible parent environments.
3. If found, return WD success / reuse the recorded WD id.
4. Otherwise perform recursive WD verification.
5. Store the successful record in the environment that owns the proof.
6. Preserve that child environment in the Result when the result must expose it.
```

The ownership boundary is:

```text
VerifyState: temporary proof-search reuse
ExecEnv:     WD records belonging to one environment
Result:      this verification's output and retained child-environment state
```

The full WD proof tree remains result data. `ExecEnv` stores the reusable
fact that an object is WD and its `WellDefinednessId`; it does not become a
global proof-result store.

```text
parent ExecEnv
  └── child ExecEnv: object -> WD id
                      └── retained by Result for final rendering/inspection
```

