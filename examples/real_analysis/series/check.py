"""Check the imported real-series example and its nearest rejection boundaries."""

import json
import os
from pathlib import Path
import subprocess


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
}


def run(path):
    result = subprocess.run(
        [str(BINARY), "-lang", "en", "-strict", "-f", str(path)],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=60,
    )
    output = json.loads(result.stdout)
    assert output["kind"] == "run", output
    assert output["session_terminated"] is False, output
    assert output["termination"] is None, output
    assert output["statement_results"], output
    return result, output


def main():
    result, output = run(HERE / "main.lit")
    assert result.returncode == 0, output
    assert output["run_result"] == "success", output
    assert not output["errors"], output
    assert all(s["statement_result"] == "accepted"
               for s in output["statement_results"]), output
    print(f"public example: {len(output['statement_results'])} accepted statements")
    for name, phase in NEGATIVES.items():
        result, output = run(HERE / "negative" / f"{name}.lit")
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
    print("9 focused real-series CLI checks passed")


if __name__ == "__main__":
    main()
