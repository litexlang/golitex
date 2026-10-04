# Statement audit: DefTemplateStmt

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `trust` (authoring / automation boundary). Explicit countdown chains pass in persistent sessions; strengthened owning files were probed separately and their exact results are retained in `release_basics/proof_journals/authoring-files.json`. This is not evidence of incorrect mathematics. Repair ownership: category 1, preserve the goal and use checked explicit steps; only diagnose local Rust behavior if the explicit route itself fails. Shared search changes require discussion.

## DefTemplateStmt/whole-file

```litex
# Stmt: DefTemplateStmt
# AST: Stmt::Definition::DefTemplateStmt
# Run all scenarios and boundaries: python3 examples/test_statements/run.py --leaf DefTemplateStmt

# case: set-and-function-template
template<S set>:
    have template_copy set = S
\template_copy<R> = R
template<T set>:
    have fn template_id(x T) T = x
\template_id<R>(4) = 4

# case: parametric-nonempty-binding
template<S nonempty_set>:
    have template_member S
let template_selected = \template_member<R>
\template_member<R> $in R
forall T nonempty_set:
    \template_member<T> $in T

# case: case-and-recursive-functions
template<S set>:
    have fn template_flag(x R) N by cases:
        case x = 0: 0
        case x != 0: 1
\template_flag<R>(0) = 0
template<T set>:
    have fn template_count(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: template_count(n - 1)
\template_count<R>(1) = 0

# case: existence-body-template
witness exist x R st {x = 2} from 2
template<S set>:
    have template_existing R:
        template_existing = 2

# case: obtain-exist-template
witness exist x R st {x = 3} from 3
template<S set>:
    obtain template_obtained from exist x R st {x = 3}

# case: obtain-atomic-template
prop template_has_copy(a R):
    exist x R st {x = a}
witness $template_has_copy(4) from 4
template<S set>:
    obtain template_atomic from $template_has_copy(4)

# case: replacement-template
prop template_image_rel(x, y set):
    x = y
forall x {1}, y, z set:
    $template_image_rel(x, y)
    $template_image_rel(x, z)
    =>:
        y = z
template<S set>:
    have by replacement_axiom: template_image from prop template_image_rel, set {1}

# case: unique-function-template
prop template_unique_source_rel(x, y R):
    y = x + 1
claim:
    ? forall x R:
        exist! y R st {$template_unique_source_rel(x, y)}
    witness exist! y R st {$template_unique_source_rel(x, y)} from x + 1:
        by def $template_unique_source_rel(x, x + 1)
have fn template_unique_source by exist!:
    ? forall x R:
        exist! y R st {$template_unique_source_rel(x, y)}
forall x R:
    $template_unique_source_rel(x, template_unique_source(x))

template<S set>:
    have fn template_unique by exist!:
        ? forall x R:
            exist! y R st {$template_unique_source_rel(x, y)}

# case: trust-have-template
template<S set>:
    trust have template_trusted R:
        template_trusted = 5
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements"]

```json
{
  "kind": "run",
  "success": false,
  "target": "file",
  "path": "/Users/shenjiachen/\u4e3b\u8981\u6587\u4ef6\u5939/GeekGems/litex/golitex/tmp/2026-10-03/src-basic-release-audit/snapshot/examples/test_statements/def_template_stmt.lit",
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "template<S set>:\n    have template_copy set = S",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define template",
        "message": "Define a reusable template"
      },
      "stores": [
        "forall S set:\n    $is_set(\\template_copy<S>)",
        "forall S set:\n    \\template_copy<S> = S"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "\\template_copy<R> = R",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "\\template_copy<R> = R"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "template<T set>:\n    have fn template_id(x T) = x",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define template",
        "message": "Define a reusable template"
      },
      "stores": [
        "forall T set:\n    \\template_id<T> $in fn (x T) T",
        "forall T set:\n    \\template_id<T> = fn (x T) T{x}"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "\\template_id<R>(4) = 4",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "\\template_id<R>(4) = 4"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "template<S nonempty_set>:\n    have template_member S",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define template",
        "message": "Define a reusable template"
      },
      "stores": [
        "forall S nonempty_set:\n    \\template_member<S> $in S"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "let template_selected = \\template_member<R>",
      "proof_method": {
        "type": "define_obj",
        "rule_name": "Let binding",
        "message": "Bind a name to a well-defined value"
      },
      "stores": [
        "template_selected = \\template_member<R>"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement
```

## DefTemplateStmt/case-and-recursive-functions

```litex
template<S set>:
    have fn template_flag(x R) N by cases:
        case x = 0: 0
        case x != 0: 1
\template_flag<R>(0) = 0
template<T set>:
    have fn template_count(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: template_count(n - 1)
\template_count<R>(1) = 0
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements"]

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "template<S set>:\n    have fn template_flag(x R) N by cases :\n        case x = 0: 0\n        case x != 0: 1",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define template",
        "message": "Define a reusable template"
      },
      "stores": [
        "forall S set:\n    \\template_flag<S> $in fn (x R) N",
        "forall S set, x R:\n    x = 0\n    =>:\n        \\template_flag<S>(x) = 0",
        "forall S set, x R:\n    x != 0\n    =>:\n        \\template_flag<S>(x) = 1"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "\\template_flag<R>(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "\\template_flag<R>(0) = 0"
      ],
      "infers": []
    },
    {
      "success": true,
      "statement": "template<T set>:\n    have fn template_count(n N) N by induc n from 0:\n        case n = 0: 0\n        case n >= 1: template_count(n - 1)",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define template",
        "message": "Define a reusable template"
      },
      "stores": [
        "forall T set:\n    \\template_count<T> $in fn (n N) N",
        "forall T set, n N:\n    n = 0\n    =>:\n        \\template_count<T>(n) = 0",
        "forall T set, n N:\n    n >= 1\n    =>:\n        \\template_count<T>(n) = \\template_count<T>(n - 1)"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "\\template_count<R>(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "\\template_count<R>(1) = 0"
      },
      "stores": [],
      "infers": []
    }
  ],
  "session_error": null
}
```

Acceptance: unchanged semantic goal with a checked explicit proof, plus wrong-result/domain/rollback controls. A verified explicit proof closes authoring debt without requiring stronger automatic recursion.
