"""Check the imported real-series example and its nearest rejection boundaries."""

import json
import os
from pathlib import Path
import subprocess
from concurrent.futures import ThreadPoolExecutor


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / "target/release/litex"
ENV = {**os.environ, "LITEX_STD_PATH": str(ROOT / "std")}
NEGATIVES = {
    "missing_convergence": "well_defined",
    "lim_missing_convergence": "well_defined",
    "eliminated_selector": "well_defined",
    "wrong_candidate": "search_proof",
    "zero_prefix": "well_defined",
    "incomplete_sequence": "well_defined",
    "wrong_finite_correction": "search_proof",
    "incorrect_zero_converse": "conclusion",
    "geometric_boundary": "premise",
    "ratio_boundary": "premise",
    "root_boundary": "premise",
    "ratio_negative_q": "premise",
    "missing_ratio_nonzero": "premise",
    "comparison_missing_sign": "premise",
    "wrong_geometric_value": "search_proof",
    "root_missing_bound": "premise",
    "root_zero_index": "argument_type",
}


def run(path):
    result = subprocess.run(
        [str(BINARY), "-lang", "en", "-strict", "-f", str(path)],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=180,
    )
    output = json.loads(result.stdout)
    assert output["kind"] == "run", output
    assert output["session_terminated"] is False, output
    assert output["termination"] is None, output
    assert output["statement_results"], output
    return result, output


def main():
    with ThreadPoolExecutor(max_workers=3) as pool:
        positives = list(pool.map(run, [HERE / "main.lit",
                                       HERE / "convergence" / "main.lit"]))
        for label, (result, output) in zip(("basic", "convergence"), positives):
            assert result.returncode == 0, output
            assert output["run_result"] == "success", output
            assert not output["errors"], output
            assert all(s["statement_result"] == "accepted"
                       for s in output["statement_results"]), output
            print(f"{label} example: {len(output['statement_results'])} accepted statements",
                  flush=True)
        results = list(pool.map(run, [HERE / "negative" / f"{name}.lit"
                                      for name in NEGATIVES]))
    for (name, phase), (result, output) in zip(NEGATIVES.items(), results):
        assert result.returncode == 1, output
        assert output["run_result"] == "failure", output
        statements = output["statement_results"]
        assert all(s["statement_result"] == "accepted"
                   for s in statements[:-1]), output
        assert statements[-1]["statement_result"] == "rejected", output
        assert len(output["errors"]) == 1, output
        error = output["errors"][0]
        assert error["statement_index"] == len(statements) - 1, output
        assert error["phase"] == phase, output
        print(f"{name}: final statement rejected at {phase}")
    print(f"{2 + len(NEGATIVES)} focused real-series CLI checks passed")


if __name__ == "__main__":
    main()
