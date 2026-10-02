"""Run current qualified-template forms and reject nearby malformed/missing names."""
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / "target/release/litex"
cases = [
    (["-f", str(HERE / "main.lit")], True),
    (["-f", str(ROOT / "examples/module_manager/trusted_template_prefix/main.lit")], True),
    (["-e", r"\local::missing<R> = R"], False),
    (["-e", r"\Unknown::defs::copied<R> = R"], False),
    (["-e", r"\local::copied = R"], False),
    (["-e", r"\Library::defs::copied::extra<R> = R"], False),
]
for args, expected in cases:
    result = subprocess.run([str(BINARY), "-strict", *args], cwd=HERE,
                            text=True, capture_output=True, timeout=20)
    output = json.loads(result.stdout)
    assert result.returncode == (0 if expected else 1), result
    assert output["success"] == expected, output
    if expected:
        assert output["session_error"] is None, output
print("6 qualified-template CLI checks passed")
