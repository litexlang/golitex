#!/usr/bin/env python3
"""Replay the showcase frames through one persistent Litex session."""

from __future__ import annotations

import argparse
import json
import select
import subprocess
import sys
import time
from pathlib import Path


FRAME_NAMES = (
    "frame_01_failed.lit.txt",
    "frame_02_accepted.lit.txt",
    "frame_03_reuse.lit.txt",
    "frame_04_endpoint.lit.txt",
)


def find_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / "Cargo.toml").is_file() and (candidate / "target").is_dir():
            return candidate
    raise RuntimeError(f"cannot locate the golitex repository above {start}")


def read_event(process: subprocess.Popen[bytes], events_file, phase: str) -> dict:
    while True:
        readable, _, _ = select.select([process.stdout], [], [], 30.0)
        if not readable:
            if process.poll() is not None:
                raise RuntimeError(f"Litex exited during {phase} with code {process.returncode}")
            print(json.dumps({"progress": "waiting", "phase": phase}), file=sys.stderr, flush=True)
            continue
        line = process.stdout.readline()
        if not line:
            raise RuntimeError(f"Litex closed stdout during {phase}")
        events_file.write(line)
        events_file.flush()
        return json.loads(line)


def send_run(process: subprocess.Popen[bytes], frame_id: str, payload: bytes) -> None:
    header = f"run {frame_id} {len(payload)}\n".encode("utf-8")
    process.stdin.write(header + payload)
    process.stdin.flush()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    showcase_dir = Path(__file__).resolve().parent
    repo_root = find_repo_root(showcase_dir)
    target = showcase_dir / "main.lit"
    command = [
        str(repo_root / "target/release/litex"),
        "-compact",
    ]
    if args.strict:
        command.append("-strict")
    command.extend(["-session", "-before", str(target)])

    started = time.monotonic()
    with args.output.open("wb") as events_file:
        process = subprocess.Popen(
            command,
            cwd=repo_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            ready = read_event(process, events_file, "registered prefix load")
            if ready.get("event") != "ready":
                print(
                    json.dumps(
                        {
                            "event": ready.get("event"),
                            "strict": args.strict,
                            "entered_session": False,
                        }
                    ),
                    flush=True,
                )
                return 2
            print(json.dumps({"event": "ready", "elapsed_seconds": round(time.monotonic() - started, 3)}), flush=True)

            for index, name in enumerate(FRAME_NAMES, start=1):
                frame_id = f"B{index:03d}"
                send_run(process, frame_id, (showcase_dir / name).read_bytes())
                event = read_event(process, events_file, frame_id)
                print(
                    json.dumps(
                        {
                            "event": event.get("event"),
                            "id": event.get("id"),
                            "ok": event.get("ok"),
                        }
                    ),
                    flush=True,
                )

            process.stdin.write(b"close\n")
            process.stdin.flush()
            return_code = process.wait(timeout=30)
            if return_code != 0:
                raise RuntimeError(f"Litex session exited with code {return_code}")
            return 0
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)


if __name__ == "__main__":
    raise SystemExit(main())
