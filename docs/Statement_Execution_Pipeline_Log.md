# Statement Execution Pipeline Log

This log records executor cleanup that separates statement execution into
well-definedness checks, verification/process checks, and environment effects.

## 2026-07-05

Goal: migrate the `have` object-introduction family to the explicit three-stage
executor shape already used by simple control and predicate-definition
statements.

Updated statements:

- `have a T`
- `have a T = x`
- `have ... by exist`
- `have ... by preimage`
- `have fn ... = ...`
- `have fn ... case_by_case`
- `have fn ... by induc`
- `have fn ... by forall exist unique`
- `have tuple`
- `have cart`
- `have seq`
- `have finite_seq`
- `have matrix`

Implementation notes:

- Kept public parser, statement, result, and output types unchanged.
- Kept each existing `exec_have_...` entrypoint and split its body into
  `verify_well_definedness`, `verify_process`, and `affect_environment`
  helpers.
- Moved permanent name binding and fact storage into the affect stage.
- Kept recursive-function registration for `have fn by induc` inside a local
  verification environment until final facts are stored.
- Added regression coverage for failed `have` process checks not binding the
  attempted name in the real environment.

