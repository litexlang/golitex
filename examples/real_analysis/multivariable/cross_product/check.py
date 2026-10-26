"""Check imported real cross products and rejection boundaries in one Session."""

import json
import os
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BINARY = ROOT / "target/release/litex"
ENV = {**os.environ, "LITEX_STD_PATH": str(ROOT / "std")}


def read_json(stream):
    text = ""
    while True:
        line = stream.readline()
        if not line:
            raise AssertionError(f"Session ended before a JSON result: {text}")
        text += line
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            continue


def check_envelope(output):
    assert output["kind"] == "run", output
    assert output["session_terminated"] is False, output
    assert output["termination"] is None, output


def main():
    result = subprocess.run(
        [str(BINARY), "-strict", "-lang", "en", "-f", str(HERE / "main.lit")],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=180,
    )
    output = json.loads(result.stdout)
    check_envelope(output)
    assert result.returncode == 0 and output["run_result"] == "success", output
    assert not output["errors"], output
    assert all(s["statement_result"] == "accepted" for s in output["statement_results"]), output
    print(f"Imported example: {len(output['statement_results'])} accepted statements", flush=True)

    cases = json.loads((HERE / "negative_cases.json").read_text())
    with subprocess.Popen(
        [str(BINARY), "-strict", "-lang", "en", "-f", str(HERE / "main.lit"), "-session"],
        cwd=ROOT, env=ENV, text=True, stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
    ) as session:
        def submit(source):
            session.stdin.write(source.rstrip() + "\n\n")
            session.stdin.flush()
            turn = read_json(session.stdout)
            check_envelope(turn)
            assert turn["target"] == "repl", turn
            assert len(turn["statement_results"]) == 1, turn
            return turn

        try:
            # -session prints the initial file snapshot only on exit.
            assert submit("0=0")["run_result"] == "success"
            # Export-file facts are scoped. Introduce the rejection fixture in
            # the live REPL rather than relying on mounted-file ambient facts.
            setup = ["release obj def vectors::cross_product::real_cross_product"]
            for name, values in (("boundary_e1", (1, 0, 0)),
                                 ("boundary_e2", (0, 1, 0)),
                                 ("boundary_e3", (0, 0, 1))):
                literal = "(" + ",".join(map(str, values)) + ")"
                setup.append(f"have {name} cart_n(R,3)={literal}")
                setup.extend(f"{name}({k})={value}"
                             for k, value in enumerate(values, 1))
            setup.append("release thm vectors::cross_product::real_cross_product_value(boundary_e1,boundary_e2,0,0,1)")
            for source in setup:
                assert submit(source)["run_result"] == "success", source
            for case in cases:
                turn = submit(case["source"])
                assert turn["run_result"] == "failure", (case, turn)
                assert turn["statement_results"][0]["statement_result"] == "rejected", turn
                assert len(turn["errors"]) == 1, turn
                assert turn["errors"][0]["phase"] == case["phase"], (case, turn)
                print(f"{case['name']}: rejected at {case['phase']}", flush=True)
            # Ordinary rejection must retain the earlier accepted example.
            assert submit("vectors::cross_product::real_cross_product(boundary_e1,boundary_e2)=(0,0,1)")["run_result"] == "success"
            session.stdin.write("exit\n")
            session.stdin.flush()
            final = read_json(session.stdout)
            check_envelope(final)
            assert len(final["errors"]) == len(cases), final
            assert final["run_result"] == "failure", final
            session.wait(timeout=30)
        finally:
            if session.poll() is None:
                session.terminate()
                session.wait(timeout=10)
    print(f"All {len(cases)} rejection controls and post-failure liveness passed")


if __name__ == "__main__":
    main()
