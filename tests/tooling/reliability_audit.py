#!/usr/bin/env python3
"""Adversarial strict-CLI audit; Fraction is the independent arithmetic oracle.

Run with --binary PATH --output PATH. A false mathematical statement being
accepted is a soundness finding; a true statement being rejected is reported
separately as a capability observation. No generated source uses trust/axioms
except cases that deliberately test strict rejection.
"""

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess
import time


def cases():
    def case(name, domain, source, expected=None, reject=False, error_contains=None):
        return dict(name=name, domain=domain, source=source,
                    expected=expected, reject=reject, error_contains=error_contains)

    yield case("zero-factor-tracer", "cancellation",
               "0 * 1 = 0 * 2\n1 = 2\n1 = 2\n1 = 1", [True, False, False, True])
    for name, source in [
        ("let", "let x = 1\nlet x = 2"),
        ("identical-let", "let x = 1\nlet x = 1"),
        ("let-have", "let x = 1\nhave x R = 2"),
        ("have-let", "have x R = 1\nlet x = 2"),
        ("function", "have fn f(t R) R = 1\nhave fn f(u R) R = 2"),
        ("function-let", "have fn f(t R) R = 1\nlet f = 2"),
        ("predicate", "prop mark(t R):\n    t = 0\nprop mark(t R):\n    t = 1"),
        ("let-predicate", "let mark = 1\nprop mark(t R):\n    t = 0"),
        ("predicate-let", "prop mark(t R):\n    t = 0\nlet mark = 1"),
        ("abstract-concrete", "abstract_prop mark(t)\nprop mark(t R):\n    t = 0"),
        ("theorem", "thm mark:\n    ? 1 = 1\nthm mark:\n    ? 0 = 1"),
        ("let-theorem", "let mark = 1\nthm mark:\n    ? 1 = 1"),
        ("struct", "struct Mark:\n    value R\n    other R\nstruct Mark:\n    value N\n    other R"),
        ("binder", "forall x, x R:\n    x = x"),
        ("nested-binder", "let x = 1\nforall x R:\n    x = x"),
        ("local-shadow", "let x = 1\nsketch:\n    let x = 2"),
        ("function-shadow", "let x = 1\nhave fn f(x R) R = x"),
        ("builder-shadow", "let x = 1\nlet S = {x R: x = x}"),
    ]:
        yield case(f"repeated-name-{name}", "duplicate-names", source,
                   reject=True, error_contains="already bound")
    yield case("repeated-name-closed-scope", "duplicate-names",
               "sketch:\n    let x = 1\n    x = 1\nsketch:\n    let x = 2\n    x = 2\nlet x = 3\nx = 3\nx = 1\nx = 2",
               [True, True, True, True, False, False])
    yield case("repeated-name-independent-binders", "duplicate-names",
               "forall x R:\n    x = x\nforall x R:\n    x = x\n0 = 1", [True, True, False])
    for name in ("R", "pi", "sin"):
        yield case(f"repeated-name-builtin-{name}", "duplicate-names",
                   f"let {name} = 0", reject=True, error_contains="reserved builtin name")
    for p, q in product((False, True), repeat=2):
        left, right = ("0 = 0" if p else "0 = 1"), ("1 = 1" if q else "1 = 0")
        yield case(f"boolean-{int(p)}-{int(q)}", "logic",
                   f"{left} and {right}\n{left} or {right}\n0 = 1\n1 = 1",
                   [p and q, p or q, False, True])
    # Every closed comparison is decidable independently with exact fractions.
    values = [Fraction(n, d) for n in range(-3, 4) for d in (1, 2, 3)]
    values = sorted(set(values))
    relations = [("=", lambda a, b: a == b), ("!=", lambda a, b: a != b),
                 ("<", lambda a, b: a < b), ("<=", lambda a, b: a <= b),
                 (">", lambda a, b: a > b), (">=", lambda a, b: a >= b)]
    for i, a in enumerate(values):
        for j, b in enumerate(values):
            lines = [f"{literal(a)} {op} {literal(b)}" for op, _ in relations]
            expected = [compare(a, b) for _, compare in relations]
            lines.append("0 = 1")
            expected.append(False)
            yield case(f"rational-order-{i}-{j}", "exact-comparison",
                       "\n".join(lines), expected)

    for a in range(-4, 5):
        for b in range(-4, 5):
            exprs = [(f"({a}) + ({b})", Fraction(a + b)),
                     (f"({a}) - ({b})", Fraction(a - b)),
                     (f"({a}) * ({b})", Fraction(a * b))]
            if b:
                exprs.append((f"({a}) / ({b})", Fraction(a, b)))
            for op, (expr, value) in enumerate(exprs):
                source = (f"{expr} = {literal(value)}\n"
                          f"{expr} = {literal(value + 1)}\n"
                          f"{expr} = {literal(value)}\n0 = 1")
                yield case(f"integer-arithmetic-{a}-{b}-{op}", "exact-arithmetic",
                           source, [True, False, True, False])

    for name, expr, value in [
        ("decimal-product", "0.1 * 0.2", Fraction(1, 50)),
        ("decimal-sum", "0.1 + 0.2", Fraction(3, 10)),
        ("beyond-float-integer", "9007199254740993 - 9007199254740992", Fraction(1)),
        ("long-decimal-difference", "1.000000000000000000000000000001 - 1", Fraction(1, 10**30)),
        ("large-integer-product", "12345678901234567890 * 12345678901234567890", Fraction(12345678901234567890**2)),
        ("odd-negative-power", "(-3)^5", Fraction(-243)),
        ("even-negative-power", "(-3)^4", Fraction(81)),
        ("negative-exponent", "2^(-3)", Fraction(1, 8)),
    ]:
        yield case(name, "numeric-boundary",
                   f"{expr} = {literal(value)}\n{expr} = {literal(value + 1)}\n0 = 1",
                   [True, False, False])

    for i, expr in enumerate(["1 / 0", "0 / 0", "0 * (1 / 0)",
                              "(1 / 0) - (1 / 0)", "1 / (2 - 2)"]):
        yield case(f"undefined-reflexivity-{i}", "well-definedness",
                   f"{expr} = {expr}\n{expr} = 0\n1 = 1\n0 = 1",
                   [False, False, True, False])

    structural = [
        ("invalid-binding-retry", "binding", "have k N = -1\nhave k N = 1\nk = 1\nk = -1", [False, True, True, False]),
        ("claim-rollback", "rollback", "have a, b R\nclaim:\n    ? 0 = 1\n    a = a\na = b\n1 = 1", [True, False, False, True]),
        ("partial-chain-rollback", "rollback", "have a R\na = a = 0\na = 0\na = a", [True, False, False, True]),
        ("partial-conjunction-rollback", "rollback", "have a R\na = a and a = 0\na = 0\na = a", [True, False, False, True]),
        ("conditional-premise-no-escape", "scope", "have a, b R\nforall t R:\n    a = b\n    =>:\n        a = b\na = b\n0 = 1", [True, True, False, False]),
        ("failed-forall-no-escape", "scope", "have a, b R\nforall t R:\n    a = b\n    =>:\n        0 = 1\na = b\n0 = 1", [True, False, False, False]),
        ("failed-theorem-no-publication", "theorem", "thm broken:\n    ? 0 = 1\n0 = 1\n1 = 1", [False, False, True]),
        ("theorem-carrier", "theorem", "thm natural:\n    ? forall n N:\n        n >= 0\nby thm natural(-1) => -1 >= 0\n-1 >= 0\nby thm natural(0) => 0 >= 0", [True, False, False, True]),
        ("theorem-premise", "theorem", "thm guarded:\n    ? forall x R:\n        x > 0\n        =>:\n            x != 0\nrelease thm guarded(0)\n0 != 0\nrelease thm guarded(1)", [True, False, False, True]),
        ("theorem-wrong-conclusion", "theorem", "thm identity:\n    ? forall n N:\n        n = n\nby thm identity(1) => 1 = 2\n1 = 2\nby thm identity(1) => 1 = 1", [True, False, False, True]),
        ("witness-carrier", "witness", "witness exist x {1} st {x = 0} from 0\nexist x {1} st {x = 0}\nwitness exist x {1} st {x = 1} from 1", [False, False, True]),
        ("witness-wrong-property", "witness", "witness exist x {0, 1} st {x = 2} from 1\nexist x {0, 1} st {x = 2}\n0 = 1", [False, False, False]),
        ("witness-dependent-carrier", "witness", "witness exist x {1}, y {x} st {y = 0} from 1, 0\n0 = 1", [False, False]),
        ("obtain-empty", "witness", "obtain x from exist y {} st {y = y}\n0 = 1\n1 = 1", [False, False, True]),
        ("bodyless-false-theorem", "theorem", "thm false_natural:\n    ? forall n N:\n        n < 0\n0 = 1", [False, False]),
        ("noninjective-function", "functions", "have fn f(x R) R = 0\nforall a, b R:\n    f(a) = f(b)\n    =>:\n        a = b\n0 = 1", [True, False, False]),
        ("unequal-finite-sets", "sets", "{0, 1} = {0, 2}\n{0, 1} = {1, 0}\n0 = 1", [False, True, False]),
        ("duplicate-list-set-wd", "well-definedness", "{0, 0} = {0}\n0 = 1", [False, False]),
        ("tuple-order", "sets", "(0, 1) = (1, 0)\n(0, 1) = (0, 1)\n0 = 1", [False, True, False]),
        ("false-quantifier", "quantifiers", "forall x R:\n    x = 0\nforall x R:\n    x = x\n0 = 1", [False, True, False]),
        ("quantifier-capture", "quantifiers", "forall x, y R:\n    x = y\n0 = 1", [False, False]),
        ("empty-carrier-no-witness", "quantifiers", "forall x {}:\n    0 = 1\n0 = 1\nexist x {} st {x = x}", [True, False, False]),
        ("false-iff-direction", "quantifiers", "forall x R:\n    =>:\n        x = 0\n    <=>:\n        x = 1\n0 = 1", [False, False]),
        ("fake-contradiction", "proof-blocks", "by contra:\n    ? 0 = 1\n    impossible 1 = 2\n0 = 1\n1 = 1", [False, False, True]),
        ("partial-contradiction", "proof-blocks", "by contra:\n    ? 0 = 1\n    impossible 1 = 1 and 0 = 0\n0 = 1", [False, False]),
        ("missing-case", "proof-blocks", "claim:\n    ? forall x R:\n        x = 0 or x = 1\n        =>:\n            x >= 0\n    by cases:\n        ? x >= 0\n        case x = 0\n0 = 1", [False, False]),
        ("false-branch", "proof-blocks", "by cases:\n    ? 0 = 1\n    case 0 = 0\n0 = 1", [False, False]),
        ("false-induction-base", "induction", "prop bad(n Z):\n    0 = 1\nby induc n from 0:\n    ? $bad(n)\n$bad(0)\n0 = 1", [True, False, False, False]),
        ("false-strong-induction-base", "induction", "prop bad(n Z):\n    0 = 1\nby strong_induc n from 0:\n    ? $bad(n)\n$bad(0)\n0 = 1", [True, False, False, False]),
        ("overlapping-function-cases", "functions", "have fn f(x R) R by cases:\n    case x >= 0: 0\n    case x <= 0: 1\n0 = 1", [False, False]),
        ("missing-function-case", "functions", "have fn f(x R) R by cases:\n    case x = 0: 0\n0 = 1", [False, False]),
        ("wrong-function-codomain", "functions", "have fn f(x R) N by cases:\n    case x = 0: -1\n    case x != 0: 1\n0 = 1", [False, False]),
        ("zero-product-cancellation", "cancellation", "forall a, b R:\n    0*a = 0*b\n    =>:\n        a = b\n0 = 1", [False, False]),
        ("zero-numerator-cancellation", "cancellation", "forall a, b R*:\n    0/a = 0/b\n    =>:\n        a = b\n0 = 1", [False, False]),
        ("square-root-injectivity", "cancellation", "forall a, b R:\n    a^2 = b^2\n    =>:\n        a = b\n0 = 1", [False, False]),
        ("sign-reversal", "order", "forall a, b R:\n    a < b\n    =>:\n        -a < -b\n0 = 1", [False, False]),
        ("zero-strict-scaling", "order", "forall a, b R:\n    a < b\n    =>:\n        0*a < 0*b\n0 = 1", [False, False]),
        ("complex-order", "well-definedness", "i < 0\n0 < i\ni = i\n0 = 1", [False, False, True, False]),
        ("false-predicate-fold", "definitions", "prop bad(x R):\n    x = 0\nby def $bad(1)\n$bad(1)\nby def $bad(0)", [True, False, False, True]),
        ("explicit-set-extension", "sets", "by extension {0, 1} = {1, 0}\nby extension {0, 1} = {0, 2}\n0 = 1", [True, False, False]),
        ("set-builder-alpha", "binding", "{x R: x > 0} = {y R: y > 0}\n{x R: x > 0} = {y R: y < 0}\n0 = 1", [True, False, False]),
        ("anonymous-alpha", "binding", "fn(x R) R {x} = fn(y R) R {y}\nfn(x R) R {x} = fn(y R) R {-y}\n0 = 1", [True, False, False]),
        ("anonymous-free-variable", "binding", "have a, b R\nfn(x R) R {a} = fn(y R) R {b}\na = b\n0 = 1", [True, False, False, False]),
        ("anonymous-permuted-parameters", "binding", "fn(x, y R) R {x-y} = fn(a, b R) R {b-a}\nfn(x, y R) R {x-y} = fn(a, b R) R {a-b}\n0 = 1", [False, True, False]),
        ("function-space-different-carrier", "binding", "fn(x R) R = fn(y N) R\nfn(x R) R = fn(y R) N\nfn(x R) R = fn(y R) R\n0 = 1", [False, False, True, False]),
        ("function-extension-different-bodies", "functions", "have fn f(x R) R = x\nhave fn g(x R) R = -x\nby fn_extension f = g\nf = g\n0 = 1", [True, True, False, False, False]),
        ("function-domain", "functions", "have fn f(x N) N = x\nf(-1) = -1\nf(0) = 0\n0 = 1", [True, False, True, False]),
        ("function-undefined-body", "functions", "have fn f(x R) R = 1 / x\n0 = 1", [False, False]),
        ("failed-function-retry", "binding", "have fn f(x R) N = -1\nhave fn f(x R) N = 1\nf(0) = 1\nf(0) = -1", [False, True, True, False]),
        ("circular-predicate-fold", "definitions", "prop circle(x R):\n    $circle(x)\nby def $circle(0)\n0 = 1", [False, False, False]),
        ("empty-domain-theorem-call", "theorem", "thm vacuous:\n    ? forall x {}:\n        0 = 1\nrelease thm vacuous(0)\n0 = 1", [True, False, False]),
        ("explicit-empty-domain-theorem", "theorem", "thm vacuous_explicit:\n    ? forall x {}:\n        0 = 1\n    by contra:\n        ? 0 = 1\n        impossible x $in {}\nrelease thm vacuous_explicit(0)\n0 = 1\n1 = 1", [True, False, False, True]),
        ("unique-existence-false", "witness", "exist! x {0, 1} st {x = x}\n0 = 1", [False, False]),
        ("integer-division-carrier", "well-definedness", "have k Z = 1 / 2\nhave k Z = 2 / 2\nk = 1\n0 = 1", [False, True, True, False]),
        ("strict-order-self", "order", "have a R\na < a\na <= a\na > a\na >= a\n0 = 1", [True, False, True, False, True, False]),
        ("pure-set-numeric-extension", "foundations", "by extension 0 = 1\nby extension i = 0\n0 = 1\n1 = 1", [False, False, False, True]),
        ("empty-separation-no-witness", "foundations", "let S = {x {0}: x != x}\nhave y S\n0 = 1\n1 = 1", [True, False, False, True]),
    ]
    for name, domain, source, expected in structural:
        record = case(name, domain, source, expected)
        # These are intentionally honest capability probes, not required
        # positive controls. Rejection is incomplete proof support, not falsity.
        record["capability_probe"] = name in {"unequal-finite-sets", "empty-domain-theorem-call"}
        yield record

    # Each schema below has an explicit finite countermodel. This is sufficient
    # to establish falsity, without claiming finite samples prove valid laws.
    terms = [
        ("a", lambda a, b, k: a), ("b", lambda a, b, k: b),
        ("k", lambda a, b, k: k),
        ("a+k", lambda a, b, k: a+k), ("b+k", lambda a, b, k: b+k),
        ("k-a", lambda a, b, k: k-a), ("k-b", lambda a, b, k: k-b),
        ("a*k", lambda a, b, k: a*k), ("b*k", lambda a, b, k: b*k),
        ("a/k", lambda a, b, k: a/k), ("b/k", lambda a, b, k: b/k),
        ("k/a", lambda a, b, k: k/a), ("k/b", lambda a, b, k: k/b),
    ]
    assignments = list(product(map(Fraction, [-2, -1, 1, 2]), repeat=3))
    for i, (left, left_value) in enumerate(terms):
        for j, (right, right_value) in enumerate(terms[i+1:], i+1):
            countermodel = next((v for v in assignments if v[0] != v[1]
                                 and left_value(*v) == right_value(*v)), None)
            if countermodel is None:
                continue
            record = case(f"cancellation-countermodel-{i}-{j}", "schema-countermodels",
                          f"forall a, b, k R*:\n    {left} = {right}\n    =>:\n        a = b\n0 = 1",
                          [False, False])
            record["countermodel"] = dict(zip(("a", "b", "k"), map(str, countermodel)))
            yield record

    for i, (left, left_value) in enumerate(terms[:9]):
        for j, (right, right_value) in enumerate(terms[:9]):
            countermodel = next((v for v in assignments if v[0] < v[1]
                                 and not left_value(*v) < right_value(*v)), None)
            if countermodel is None:
                continue
            record = case(f"order-countermodel-{i}-{j}", "schema-countermodels",
                          f"forall a, b, k R:\n    a < b\n    =>:\n        {left} < {right}\n0 = 1",
                          [False, False])
            record["countermodel"] = dict(zip(("a", "b", "k"), map(str, countermodel)))
            yield record

    for name, source, error_contains in [
        ("strict-trust", "trust 0 = 1", "forbidden"),
        ("strict-nested-trust", "claim:\n    ? 0 = 1\n    trust 0 = 1", "forbidden"),
        ("strict-trust-have", "trust have x {}", "forbidden"),
        ("strict-axiom", "axiom false_axiom:\n    ? forall x R:\n        0 = 1", "forbidden"),
        ("strict-template-trust", "template<S set>:\n    trust have chosen R:\n        chosen = 0", "forbidden"),
        ("binder-no-escape", "forall x R:\n    x = x\nx = 0", "undefined name `x`"),
        ("sketch-name-no-escape", "sketch:\n    let local = 0\nlocal = 0", "undefined name `local`"),
        ("unrestricted-comprehension-rejected", "let russell = {x set: not x $in x}", "undefined name `set`"),
    ]:
        yield case(name, "strict-or-scope", source, reject=True, error_contains=error_contains)


def literal(value):
    value = Fraction(value)
    return (f"({value.numerator})" if value.denominator == 1 else
            f"(({value.numerator}) / {value.denominator})")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--only", help="case-name substring")
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    binary = args.binary.resolve()
    results = []
    start = time.monotonic()
    for case in cases():
        if args.only and args.only not in case["name"]:
            continue
        record = dict(case)
        try:
            # The binary's directory has no litex.config; -e runs in isolation.
            proc = subprocess.run([str(binary), "-strict", "-lang", "en", "-e", case["source"]],
                                  cwd=binary.parent, capture_output=True, text=True,
                                  timeout=args.timeout)
            record["exit_code"] = proc.returncode
            data = json.loads(proc.stdout)
            actual = [item["success"] for item in data["statement_results"]]
            record["actual"] = actual
            record["session_error"] = data["session_error"]
            envelope_success = all(actual) and data["session_error"] is None
            consistent = (data["success"] == (proc.returncode == 0)
                          and data["success"] == envelope_success)
            if data["kind"] != "run" or not consistent:
                record["status"] = "output_contract_failure"
            elif case["reject"]:
                if data["success"]:
                    record["status"] = "false_acceptance"
                elif case["error_contains"] not in str(data["session_error"]):
                    record["status"] = "wrong_rejection_reason"
                else:
                    record["status"] = "pass"
            elif data["session_error"] is not None or len(actual) != len(case["expected"]):
                record["status"] = "expression_or_session_observation"
            elif actual == case["expected"]:
                record["status"] = "pass"
            elif any(ok and not expected for ok, expected in zip(actual, case["expected"])):
                record["status"] = "false_acceptance"
            elif case.get("capability_probe"):
                record["status"] = "true_statement_rejected"
            else:
                record["status"] = "positive_control_failure"
            if record["status"] != "pass":
                record["output"] = data
                record["stderr"] = proc.stderr
        except subprocess.TimeoutExpired:
            record["status"] = "timeout"
        except (ValueError, KeyError, TypeError) as error:
            record.update(status="invalid_output", error=str(error),
                          stdout=proc.stdout, stderr=proc.stderr)
        results.append(record)
        if len(results) % 100 == 0:
            print(f"Checked {len(results)} cases", flush=True)

    if not results:
        parser.error("No audit cases matched --only; no checks were executed.")
    summary = dict(Counter(record["status"] for record in results))
    report = dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  strict=True, case_count=len(results),
                  statement_count=sum(len(r["expected"] or []) for r in results),
                  elapsed_seconds=round(time.monotonic() - start, 3),
                  summary=summary, results=results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    for record in results:
        if record["status"] != "pass":
            print(record["status"], record["name"], record.get("actual"))
    return int(any(r["status"] in {"false_acceptance", "output_contract_failure",
                                  "expression_or_session_observation", "wrong_rejection_reason",
                                  "positive_control_failure", "timeout", "invalid_output"} for r in results))


if __name__ == "__main__":
    raise SystemExit(main())
