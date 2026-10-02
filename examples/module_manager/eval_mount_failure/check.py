"""Check real CLI envelopes for failed and successful configured eval mounts."""
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / "target/release/litex"
for cwd, source, expected in [
    (HERE, "1 = 1", False),
    (HERE, "0 = 1", False),
    (ROOT / "examples/module_manager/cwd_eval", "1 = 1", True),
]:
    result = subprocess.run(
        [str(BINARY), "-strict", "-e", source],
        cwd=cwd, text=True, capture_output=True, timeout=20,
    )
    output = json.loads(result.stdout)
    assert result.returncode == (0 if expected else 1), result
    assert output["success"] == expected, output
    if expected:
        assert output["session_error"] is None, output
        assert output["statement_results"], output
    else:
        assert output["session_error"] == "FailToImport", output
        assert output["statement_results"] == [], output
print("3 configured eval envelope checks passed")
