# Object regression corpus

This directory tests object syntax, domains, values and rejected uses. The
[coverage manifest](coverage.json) maps object families to positive files,
negative controls and known gaps. The corresponding declarations are in
`src/ast/obj.rs`.

Positive files contain labelled cases. Negative fixtures must be rejected;
known gaps record a difference between observed and intended behavior. A
recorded gap is not evidence that a mathematical statement is false.

## Run

From the repository root:

```sh
python3 examples/test_objs/run.py --audit-only
python3 examples/test_objs/run.py --object div
python3 examples/test_objs/run.py
```

The audit checks the AST and file inventory. Execution commands build the
release binary, then check exit status and the current CLI JSON envelope.
The default mode checks intended behavior and fails if a positive case is
rejected, a forbidden input is accepted, or an execution/format error occurs.

`--baseline` instead compares observations to the manifest's recorded baseline.
A matching baseline does not mean that known defects have been fixed. The
runner reports source and binary identities; results apply to those inputs.

## Files and boundaries

- `*.lit`: labelled positive cases.
- `negative/`: individual rejection controls.
- `gaps/`: intended-positive cases with recorded unresolved behavior.
- `fixtures/` and `identifier_with_*/`: project context for imported names.
- `coverage.json`: maintained inventory, expected outcomes and baseline data.
- `run.py`: inventory and execution checks.

Some positive files reuse earlier statements in that file. Do not run all
`.lit` files as expected successes: negative and gap files have different
acceptance criteria. This finite corpus does not establish the absence of
all object-verification defects.
