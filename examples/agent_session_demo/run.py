"""Drive a real Litex Session and compare it with repeated prefix replay."""

import json
import os
from pathlib import Path
import queue
import subprocess
import sys
import tempfile
import threading
import time


ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT / "target/release/litex"
PREFIX = "have a R = 2"
STEPS = (
    "have b R = a + 1",
    "have c R = b + 1",
    "have d R = c + 1",
    "have f R = d + 1",
)
REJECTED = "b = 99"
PROMPT = b"litex> "
TIMEOUT = 10


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def batch(cwd, *args):
    result = subprocess.run(
        [str(BINARY), "-lang", "en", "-strict", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        timeout=TIMEOUT,
        check=False,
    )
    require(not result.stderr, f"unexpected stderr: {result.stderr}")
    return result, json.loads(result.stdout)


def require_success(result, output, target, statement_count):
    require(result.returncode == 0, f"{target} exit: {result.returncode}")
    require(output.get("kind") == "run", f"{target}: not a run envelope")
    require(output.get("run_result") == "success", f"{target}: failed run")
    require(output.get("session_terminated") is False, f"{target}: terminated")
    require(output.get("termination") is None, f"{target}: termination detail")
    statements = output.get("statement_results")
    require(isinstance(statements, list), f"{target}: missing statements")
    require(len(statements) == statement_count, f"{target}: wrong statement count")
    require(
        all(item.get("statement_result") == "accepted" for item in statements),
        f"{target}: rejected statement",
    )


class Session:
    """Read Litex's text REPL responses up to each flushed prompt."""

    def __init__(self, cwd):
        self.process = subprocess.Popen(
            [str(BINARY), "-lang", "en", "-strict", "-session", "-e", PREFIX],
            cwd=cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        self.chunks = queue.Queue()
        self.buffer = bytearray()
        self.reader = threading.Thread(target=self._pump, daemon=True)
        self.reader.start()
        try:
            greeting = self._through(PROMPT)
            require(b"Litex REPL" in greeting, "initial Session did not start")
        except (OSError, RuntimeError):
            self.close()
            raise

    def _pump(self):
        try:
            while True:
                chunk = os.read(self.process.stdout.fileno(), 4096)
                if not chunk:
                    break
                self.chunks.put(chunk)
        finally:
            self.chunks.put(None)

    def _through(self, marker):
        deadline = time.monotonic() + TIMEOUT
        while marker not in self.buffer:
            remaining = deadline - time.monotonic()
            require(remaining > 0, "timed out waiting for Litex prompt")
            try:
                chunk = self.chunks.get(timeout=remaining)
            except queue.Empty as error:
                raise RuntimeError("timed out waiting for Litex prompt") from error
            require(chunk is not None, f"Litex stopped before prompt: {self.buffer!r}")
            self.buffer.extend(chunk)
        end = self.buffer.index(marker) + len(marker)
        response = bytes(self.buffer[:end])
        del self.buffer[:end]
        return response

    def submit(self, statement):
        self.process.stdin.write((statement + "\n").encode())
        self.process.stdin.flush()
        response = self._through(PROMPT)
        return response[: -len(PROMPT)].decode().strip()

    def finish(self):
        self.process.stdin.write(b"exit\n")
        self.process.stdin.flush()
        self.process.stdin.close()
        deadline = time.monotonic() + TIMEOUT
        while True:
            remaining = deadline - time.monotonic()
            require(remaining > 0, "timed out waiting for Session exit")
            try:
                chunk = self.chunks.get(timeout=remaining)
            except queue.Empty as error:
                raise RuntimeError("timed out waiting for Session exit") from error
            if chunk is None:
                break
            self.buffer.extend(chunk)
        code = self.process.wait(timeout=TIMEOUT)
        stderr = self.process.stderr.read().decode()
        require(not stderr, f"unexpected Session stderr: {stderr}")
        return code, json.loads(self.buffer.decode())

    def close(self):
        if self.process.poll() is None:
            self.process.kill()
            self.process.wait(timeout=TIMEOUT)


def main():
    require(BINARY.is_file(), f"build the release binary first: {BINARY}")
    with tempfile.TemporaryDirectory(prefix="litex-agent-session-") as scratch:
        scratch = Path(scratch)  # Empty directory: no incidental litex.config.
        accepted = [PREFIX]
        session = Session(scratch)
        saved = scratch / "accepted.lit"
        saved.write_text(PREFIX + "\n", encoding="utf-8")

        def record(step):
            accepted.append(step)
            with saved.open("a", encoding="utf-8") as source:
                source.write(step + "\n")

        try:
            require(session.submit(STEPS[0]) == "success", "first dependent step failed")
            record(STEPS[0])

            failure = json.loads(session.submit(REJECTED))
            require(failure.get("kind") == "run", "failure was not JSON run feedback")
            require(failure.get("run_result") == "failure", "bad candidate was accepted")
            require(failure.get("session_terminated") is False, "soft failure killed Session")
            require(failure.get("termination") is None, "soft failure has termination")
            results = failure.get("statement_results")
            require(isinstance(results, list) and len(results) == 1, "wrong failure frame")
            require(results[0].get("statement_result") == "rejected", "wrong verdict")
            require(results[0].get("statement") == REJECTED, "wrong rejected source")
            require(results[0].get("why_failed", {}).get("phase") == "search_proof", "wrong phase")
            require(results[0].get("why_failed", {}).get("goal") == REJECTED, "wrong goal")

            for step in STEPS[1:]:
                require(session.submit(step) == "success", f"dependent step failed: {step}")
                record(step)
            exit_code, final_output = session.finish()
            require(exit_code == 1, "Session with a rejected attempt should exit 1")
            require(final_output.get("run_result") == "failure", "missing final failure")
            require(final_output.get("session_terminated") is False, "Session hard-stopped")
            require(final_output.get("termination") is None, "unexpected final termination")
        finally:
            session.close()

        # A fresh process cannot see b unless the accepted prefix is replayed.
        missing, missing_output = batch(scratch, "-e", STEPS[1])
        require(missing.returncode == 1, "fresh process unexpectedly saw b")
        require(missing_output.get("session_terminated") is True, "missing b was not caught")
        require(missing_output.get("termination", {}).get("phase") == "parse", "wrong boundary")

        # This deliberately repeats the accepted prefix once per new step.
        replayed_step_checks = 0
        for count in range(1, len(STEPS) + 1):
            code = "\n".join([PREFIX, *STEPS[:count]])
            result, output = batch(scratch, "-e", code)
            require_success(result, output, "restart", count + 1)
            replayed_step_checks += count

        # The one source journal contains only accepted statements.
        require(saved.read_text(encoding="utf-8") == "\n".join(accepted) + "\n", "journal drift")
        result, output = batch(scratch, "-f", str(saved))
        require_success(result, output, "final file", len(accepted))

    n = len(STEPS)
    require(replayed_step_checks == n * (n + 1) // 2, "prefix-sum mismatch")
    print(f"Soft rejection: {REJECTED!r}; next dependent step accepted in the same Session")
    print("Fresh process without the prefix: missing name rejected")
    print(f"Dependent-step checks: Session {n}, restart each step {replayed_step_checks}")
    print(f"Ratio: {replayed_step_checks / n:g} = (N + 1) / 2 for N = {n}")
    print(f"Initial prefix loads: Session 1, restart each step {n}")
    print("Excluded from ratio: rejected trial, initial loads, final clean file gate")
    print("Final accepted source: strict clean file check passed")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"Session demo failed: {error}", file=sys.stderr)
        sys.exit(1)
