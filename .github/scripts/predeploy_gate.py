#!/usr/bin/env python3
"""Run release-mode docs, examples, and textbook file gates."""

from __future__ import annotations

import argparse
import ast
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


RUNNER_VERSION = "0.1"
DEFAULT_GLOBAL_TIMEOUT_SECONDS = 240.0
DEFAULT_FILE_TIMEOUT_SECONDS = 600.0
DEFAULT_TEXTBOOK_JOBS = min(4, os.cpu_count() or 1)
PROFILE_LINE = re.compile(r"^repository statement (.+):(\d+): [0-9.]+ ms$")


@dataclass(frozen=True)
class Textbook:
    name: str
    module_path: Path


# This is the deployment textbook allowlist. Paths are repository-relative.
TEXTBOOKS = [
    Textbook("Analysis", Path("scripts/Analysis/textbook")),
    Textbook("MIL", Path("scripts/mathematics_in_litex/textbook")),
    Textbook(
        "Mechanics", Path("scripts/The-Mechanics-of-Litex-Proof/textbook")
    ),
    Textbook("LADR", Path("scripts/linear_algebra_done_right/textbook")),
    Textbook("NTFB", Path("scripts/number_theory_for_beginners/textbook")),
]

GATES = (
    ("docs", "run_docs_markdown_files"),
    ("examples", "run_examples_only"),
)


@dataclass(frozen=True)
class TextbookFile:
    textbook: Textbook
    path: Path
    book_index: int
    book_total: int


@dataclass(frozen=True)
class GateResult:
    label: str
    command: tuple[str, ...]
    status: str
    returncode: int | None
    output: str
    wall_seconds: float


@dataclass(frozen=True)
class FileResult:
    textbook_file: TextbookFile
    status: str
    returncode: int | None
    wall_seconds: float
    line: int | None = None
    statement: str | None = None
    source_path: str | None = None
    message: str | None = None
    output: str = ""


@dataclass(frozen=True)
class ProcessOutcome:
    status: str
    returncode: int | None
    stdout: str
    stderr: str
    wall_seconds: float


class ProcessController:
    def __init__(self, timeout_seconds: float) -> None:
        self.deadline = time.perf_counter() + timeout_seconds
        self.timeout_seconds = timeout_seconds
        self.cancelled = threading.Event()
        self._lock = threading.Lock()
        self._processes: set[subprocess.Popen[str]] = set()
        self._cancelled_pids: set[int] = set()

    def run(
        self,
        command: list[str],
        *,
        cwd: Path,
        env: dict[str, str] | None = None,
        merge_stderr: bool = False,
        timeout_seconds: float | None = None,
    ) -> ProcessOutcome:
        start = time.perf_counter()
        remaining = self.deadline - start
        if self.cancelled.is_set() or remaining <= 0:
            self.cancel_all()
            return ProcessOutcome("not_started", None, "", "", 0.0)

        try:
            process = subprocess.Popen(
                command,
                cwd=cwd,
                env=env,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT if merge_stderr else subprocess.PIPE,
                start_new_session=os.name != "nt",
            )
        except OSError as error:
            return ProcessOutcome(
                "launch_error",
                None,
                "",
                f"{type(error).__name__}: {error}",
                time.perf_counter() - start,
            )

        with self._lock:
            self._processes.add(process)
        if self.cancelled.is_set():
            self.cancel_all()

        remaining = max(0.0, self.deadline - time.perf_counter())
        wait_seconds = remaining
        if timeout_seconds is not None:
            wait_seconds = min(wait_seconds, timeout_seconds)
        try:
            stdout, stderr = process.communicate(timeout=wait_seconds)
            status = "completed"
        except subprocess.TimeoutExpired:
            if time.perf_counter() >= self.deadline:
                self.cancel_all()
                status = "cancelled"
            else:
                stop_process_group(process)
                status = "timeout"
            stdout, stderr = process.communicate()
        finally:
            with self._lock:
                self._processes.discard(process)

        with self._lock:
            was_cancelled = process.pid in self._cancelled_pids
        if was_cancelled:
            status = "cancelled"
        return ProcessOutcome(
            status,
            process.returncode,
            stdout or "",
            stderr or "",
            time.perf_counter() - start,
        )

    def cancel_all(self) -> None:
        self.cancelled.set()
        with self._lock:
            processes = list(self._processes)
            self._cancelled_pids.update(process.pid for process in processes)
        for process in processes:
            signal_process_group(process, signal.SIGTERM)
        grace_deadline = time.perf_counter() + 0.5
        while time.perf_counter() < grace_deadline:
            if all(process.poll() is not None for process in processes):
                break
            time.sleep(0.01)
        for process in processes:
            if process.poll() is None:
                signal_process_group(process, signal.SIGKILL)


def main() -> int:
    args = parse_args()
    repository_root = Path(__file__).resolve().parents[2]

    try:
        textbook_files = collect_textbook_files(repository_root, TEXTBOOKS)
    except (OSError, ValueError) as error:
        print(f"textbook configuration error: {error}", file=sys.stderr)
        return 2

    total_start = time.perf_counter()
    controller = ProcessController(args.timeout)

    print("PREPARE  cargo test --release --no-run", flush=True)
    build = controller.run(
        ["cargo", "test", "--release", "--no-run"],
        cwd=repository_root,
        merge_stderr=True,
    )
    if build.status in {"cancelled", "not_started"}:
        print(f"PREPARE CANCELLED {build.wall_seconds:.2f}s")
        print(
            f"GLOBAL TIMEOUT {args.timeout:g}s | prepare unfinished | "
            f"docs + examples + {len(textbook_files)} textbook files not started",
            file=sys.stderr,
        )
        return 1
    if build.status != "completed" or build.returncode != 0:
        print(f"PREPARE FAILED  {build.wall_seconds:.2f}s")
        print(build.stdout or "")
        return 1
    print(f"PREPARE SUCCESS {build.wall_seconds:.2f}s", flush=True)

    binary = repository_root / "target" / "release" / "litex"
    if not binary.is_file():
        print(f"release binary missing after build: {binary}", file=sys.stderr)
        return 2

    print(
        f"START    {len(TEXTBOOKS)} books / {len(textbook_files)} files / "
        f"{args.jobs} textbook workers / global timeout {args.timeout:g}s / "
        f"file timeout {args.file_timeout:g}s",
        flush=True,
    )
    cargo_results, file_results = run_all_gates(
        repository_root,
        binary,
        textbook_files,
        args.jobs,
        args.file_timeout,
        args.verbose,
        total_start,
        controller,
    )
    total_wall_seconds = time.perf_counter() - total_start

    failed_cargo = [
        result.label
        for result in cargo_results
        if result.status != "success"
    ]
    failed_files = [result for result in file_results if result.status != "success"]
    if failed_cargo or failed_files:
        if controller.cancelled.is_set():
            unfinished_cargo = sum(
                result.status in {"cancelled", "not_started"}
                for result in cargo_results
            )
            unfinished_files = sum(
                result.status in {"cancelled", "not_started"}
                for result in file_results
            )
            print(
                f"GLOBAL TIMEOUT {args.timeout:g}s | stopped/not started: "
                f"cargo {unfinished_cargo}/{len(cargo_results)}, "
                f"textbook files {unfinished_files}/{len(file_results)}",
                file=sys.stderr,
            )
        print(
            f"DEPLOY FAILED  {total_wall_seconds:.2f}s | "
            f"cargo failures={len(failed_cargo)} | "
            f"textbook failures={len(failed_files)}",
            file=sys.stderr,
        )
        return 1

    print(
        f"DEPLOY SUCCESS {total_wall_seconds:.2f}s | "
        f"docs + examples + {len(TEXTBOOKS)} books / {len(file_results)} files",
        flush=True,
    )
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run docs, examples, and registered textbook files in parallel."
    )
    parser.add_argument(
        "--jobs",
        type=positive_int,
        default=DEFAULT_TEXTBOOK_JOBS,
        help=f"parallel textbook file processes (default: {DEFAULT_TEXTBOOK_JOBS})",
    )
    parser.add_argument(
        "--timeout",
        type=positive_float,
        default=DEFAULT_GLOBAL_TIMEOUT_SECONDS,
        help=(
            "seconds before every unfinished process is stopped "
            f"(default: {DEFAULT_GLOBAL_TIMEOUT_SECONDS:g})"
        ),
    )
    parser.add_argument(
        "--file-timeout",
        type=positive_float,
        default=DEFAULT_FILE_TIMEOUT_SECONDS,
        help=(
            "seconds before a textbook file is reported as stuck "
            f"(default: {DEFAULT_FILE_TIMEOUT_SECONDS:g})"
        ),
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="print successful Cargo test output; failures are always printed",
    )
    return parser.parse_args()


def run_all_gates(
    repository_root: Path,
    binary: Path,
    textbook_files: list[TextbookFile],
    textbook_jobs: int,
    file_timeout: float,
    verbose: bool,
    run_start: float,
    controller: ProcessController,
) -> tuple[list[GateResult], list[FileResult]]:
    cargo_results: list[GateResult] = []
    file_results: list[FileResult] = []
    book_completed = {textbook.name: 0 for textbook in TEXTBOOKS}
    book_failed = {textbook.name: 0 for textbook in TEXTBOOKS}
    completion_index = 0

    max_workers = textbook_jobs + len(GATES)
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures: dict[Future[object], tuple[str, str]] = {}
        for label, test_name in GATES:
            future = executor.submit(
                run_cargo_test,
                repository_root,
                label,
                test_name,
                subprocess.run,
                controller,
            )
            futures[future] = ("cargo", label)
        for textbook_file in textbook_files:
            future = executor.submit(
                run_textbook_file,
                repository_root,
                binary,
                textbook_file,
                file_timeout,
                subprocess.run,
                controller,
            )
            futures[future] = ("textbook", textbook_file.textbook.name)

        for future in as_completed(futures):
            kind, label = futures[future]
            if kind == "cargo":
                result = future.result()
                assert isinstance(result, GateResult)
                cargo_results.append(result)
                print_cargo_result(result, verbose)
                continue

            result = future.result()
            assert isinstance(result, FileResult)
            file_results.append(result)
            completion_index += 1
            print_file_result(completion_index, len(textbook_files), result)

            book_completed[label] += 1
            if result.status != "success":
                book_failed[label] += 1
            if book_completed[label] == result.textbook_file.book_total:
                status = "SUCCESS" if book_failed[label] == 0 else "FAILED"
                print(
                    f"BOOK {status:<7} [{label}] "
                    f"{book_completed[label] - book_failed[label]}/"
                    f"{book_completed[label]} files | "
                    f"gate wall {time.perf_counter() - run_start:.2f}s",
                    flush=True,
                )

    cargo_order = {label: index for index, (label, _) in enumerate(GATES)}
    cargo_results.sort(key=lambda result: cargo_order[result.label])
    return cargo_results, file_results


def collect_textbook_files(
    repository_root: Path, textbooks: list[Textbook]
) -> list[TextbookFile]:
    collected: list[TextbookFile] = []
    for textbook in textbooks:
        module = repository_root / textbook.module_path
        config_path = module / "litex.config"
        exports = read_export_paths(config_path)

        paths: list[Path] = []
        module_resolved = module.resolve()
        for export_name, relative_value in exports:
            path = (module / relative_value).resolve()
            try:
                path.relative_to(module_resolved)
            except ValueError as error:
                raise ValueError(
                    f"export escapes textbook module: {config_path}: {relative_value}"
                ) from error
            if path.suffix != ".lit":
                continue
            if not path.is_file():
                raise ValueError(f"registered textbook file is missing: {path}")
            paths.append(path)

        if not paths:
            raise ValueError(f"no registered .lit exports: {config_path}")
        for index, path in enumerate(paths, start=1):
            collected.append(TextbookFile(textbook, path, index, len(paths)))
    return collected


def read_export_paths(config_path: Path) -> list[tuple[str, str]]:
    exports: list[tuple[str, str]] = []
    in_export = False
    for line_number, raw_line in enumerate(
        config_path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            in_export = line == "[export]"
            continue
        if not in_export:
            continue
        if "=" not in line:
            raise ValueError(
                f"{config_path}:{line_number}: expected name = path in [export]"
            )
        export_name, raw_value = line.split("=", 1)
        export_name = export_name.strip()
        try:
            relative_value = ast.literal_eval(raw_value.strip())
        except (SyntaxError, ValueError) as error:
            raise ValueError(
                f"{config_path}:{line_number}: invalid export path"
            ) from error
        if not export_name or not isinstance(relative_value, str):
            raise ValueError(
                f"{config_path}:{line_number}: export needs a name and string path"
            )
        exports.append((export_name, relative_value))
    if not exports:
        raise ValueError(f"missing or empty [export] section: {config_path}")
    return exports


def run_textbook_file(
    repository_root: Path,
    binary: Path,
    textbook_file: TextbookFile,
    timeout_seconds: float,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    controller: ProcessController | None = None,
) -> FileResult:
    command = textbook_file_command(binary, textbook_file.path)
    environment = os.environ.copy()
    environment["LITEX_PROFILE_REPOSITORY"] = "1"
    start = time.perf_counter()
    if controller is not None:
        outcome = controller.run(
            command,
            cwd=repository_root,
            env=environment,
            timeout_seconds=timeout_seconds,
        )
        if outcome.status in {"cancelled", "not_started"}:
            source_path: str | None = None
            line: int | None = None
            statement: str | None = None
            if outcome.status == "cancelled":
                source_path, line, statement = timeout_location(
                    repository_root, outcome.stderr, textbook_file.path
                )
            return FileResult(
                textbook_file=textbook_file,
                status=outcome.status,
                returncode=outcome.returncode,
                wall_seconds=outcome.wall_seconds,
                source_path=source_path,
                line=line,
                statement=statement,
                message=(
                    "stopped because the "
                    f"{controller.timeout_seconds:g}s global deadline expired"
                    if outcome.status == "cancelled"
                    else "not started before the "
                    f"{controller.timeout_seconds:g}s global deadline expired"
                ),
                output=diagnostic_tail(outcome.stdout, outcome.stderr),
            )
        if outcome.status == "timeout":
            source_path, line, statement = timeout_location(
                repository_root, outcome.stderr, textbook_file.path
            )
            return FileResult(
                textbook_file=textbook_file,
                status="timeout",
                returncode=outcome.returncode,
                wall_seconds=outcome.wall_seconds,
                source_path=source_path,
                line=line,
                statement=statement,
                message=(
                    f"no completion after {timeout_seconds:g}s; "
                    "stuck location is inferred from the last completed statement"
                ),
                output=diagnostic_tail(outcome.stdout, outcome.stderr),
            )
        if outcome.status == "launch_error":
            return FileResult(
                textbook_file=textbook_file,
                status="launch_error",
                returncode=None,
                wall_seconds=outcome.wall_seconds,
                message=f"failed to launch Litex: {outcome.stderr}",
            )
        return file_result_from_completed(
            repository_root,
            textbook_file,
            subprocess.CompletedProcess(
                command,
                outcome.returncode,
                stdout=outcome.stdout,
                stderr=outcome.stderr,
            ),
            outcome.wall_seconds,
        )

    try:
        completed = runner(
            command,
            cwd=repository_root,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as error:
        wall_seconds = time.perf_counter() - start
        stdout = output_text(error.stdout)
        stderr = output_text(error.stderr)
        source_path, line, statement = timeout_location(
            repository_root, stderr, textbook_file.path
        )
        return FileResult(
            textbook_file=textbook_file,
            status="timeout",
            returncode=None,
            wall_seconds=wall_seconds,
            source_path=source_path,
            line=line,
            statement=statement,
            message=(
                f"no completion after {timeout_seconds:g}s; "
                "stuck location is inferred from the last completed statement"
            ),
            output=diagnostic_tail(stdout, stderr),
        )
    except OSError as error:
        return FileResult(
            textbook_file=textbook_file,
            status="launch_error",
            returncode=None,
            wall_seconds=time.perf_counter() - start,
            message=f"failed to launch Litex: {type(error).__name__}: {error}",
        )

    return file_result_from_completed(
        repository_root,
        textbook_file,
        completed,
        time.perf_counter() - start,
    )


def file_result_from_completed(
    repository_root: Path,
    textbook_file: TextbookFile,
    completed: subprocess.CompletedProcess[str],
    wall_seconds: float,
) -> FileResult:
    stdout = completed.stdout or ""
    stderr = completed.stderr or ""
    try:
        envelope = json.loads(stdout)
    except json.JSONDecodeError as error:
        exit_description = process_exit_description(completed.returncode)
        source_path, line, statement = timeout_location(
            repository_root, stderr, textbook_file.path
        )
        return FileResult(
            textbook_file=textbook_file,
            status="contract_error",
            returncode=completed.returncode,
            wall_seconds=wall_seconds,
            source_path=source_path,
            line=line,
            statement=statement,
            message=f"invalid runner JSON ({exit_description}): {error}",
            output=diagnostic_tail(stdout, stderr),
        )

    contract_error = runner_contract_error(envelope, completed.returncode)
    if contract_error:
        return FileResult(
            textbook_file=textbook_file,
            status="contract_error",
            returncode=completed.returncode,
            wall_seconds=wall_seconds,
            message=contract_error,
            output=diagnostic_tail(stdout, stderr),
        )
    if envelope["ok"] is True:
        return FileResult(
            textbook_file=textbook_file,
            status="success",
            returncode=completed.returncode,
            wall_seconds=wall_seconds,
        )

    source_path, line, statement, message = trace_diagnostic(
        envelope.get("trace", "")
    )
    return FileResult(
        textbook_file=textbook_file,
        status="failed",
        returncode=completed.returncode,
        wall_seconds=wall_seconds,
        source_path=(
            relative_display(repository_root, Path(source_path))
            if source_path
            else None
        ),
        line=line,
        statement=statement,
        message=message or "Litex verification failed",
        output=diagnostic_tail(envelope.get("trace", ""), stderr),
    )


def runner_contract_error(envelope: object, returncode: int) -> str | None:
    if not isinstance(envelope, dict):
        return "runner output is not an object"
    if envelope.get("runner") != "litex-runner":
        return "runner is not litex-runner"
    if envelope.get("runner_version") != RUNNER_VERSION:
        return f"unexpected runner_version={envelope.get('runner_version')!r}"
    ok = envelope.get("ok")
    if not isinstance(ok, bool):
        return "runner ok is not boolean"
    expected_result = "success" if ok else "error"
    expected_returncode = 0 if ok else 1
    if envelope.get("result") != expected_result:
        return f"runner result disagrees with ok={ok!r}"
    if returncode != expected_returncode:
        return f"exit={returncode} disagrees with ok={ok!r}"
    target = envelope.get("target")
    if not isinstance(target, dict) or target.get("kind") != "file":
        return "runner target kind is not file"
    if not isinstance(envelope.get("trace"), str):
        return "runner trace is not a string"
    return None


def trace_diagnostic(
    trace: str,
) -> tuple[str | None, int | None, str | None, str | None]:
    payloads = decode_concatenated_json(trace)
    dictionaries = [payload for payload in payloads if isinstance(payload, dict)]
    if not dictionaries:
        return None, None, None, first_nonempty_line(trace)
    payload = next(
        (item for item in reversed(dictionaries) if item.get("result") == "error"),
        dictionaries[-1],
    )

    nested = nested_dicts(payload)
    source_path = next(
        (item.get("path") for item in nested if isinstance(item.get("path"), str)),
        None,
    )
    line = next(
        (item.get("line") for item in nested if isinstance(item.get("line"), int)),
        None,
    )
    statement = next(
        (
            item.get("statement")
            for item in nested
            if isinstance(item.get("statement"), str)
        ),
        None,
    )
    failed_goal = next(
        (
            item.get("failed_goal")
            for item in nested
            if isinstance(item.get("failed_goal"), str)
        ),
        None,
    )
    message = payload.get("message")
    if not isinstance(message, str):
        message = failed_goal
    elif failed_goal and failed_goal != statement:
        message = f"{message}; failed goal: {failed_goal}"
    return source_path, line, statement, message


def decode_concatenated_json(value: str) -> list[object]:
    decoder = json.JSONDecoder()
    decoded: list[object] = []
    index = 0
    while index < len(value):
        while index < len(value) and value[index].isspace():
            index += 1
        if index >= len(value):
            break
        try:
            item, end = decoder.raw_decode(value, index)
        except json.JSONDecodeError:
            return []
        decoded.append(item)
        index = end
    return decoded


def timeout_location(
    repository_root: Path, stderr: str, target_path: Path
) -> tuple[str | None, int | None, str | None]:
    matches = [PROFILE_LINE.match(line) for line in stderr.splitlines()]
    completed = [match for match in matches if match]
    if not completed:
        first_line, statement = first_top_level_statement(target_path)
        return relative_display(repository_root, target_path), first_line, statement

    last = completed[-1]
    assert last is not None
    last_path = Path(last.group(1))
    if not last_path.is_absolute():
        last_path = repository_root / last_path
    last_line = int(last.group(2))
    next_line, statement = next_top_level_statement(last_path, last_line)
    if next_line is not None:
        return relative_display(repository_root, last_path), next_line, statement
    return relative_display(repository_root, last_path), last_line, "last completed statement"


def print_cargo_result(result: GateResult, verbose: bool) -> None:
    status = result.status.upper()
    print(f"CARGO {status:<7} [{result.label}] {result.wall_seconds:.2f}s", flush=True)
    if verbose or result.status != "success":
        print(result.output, end="" if result.output.endswith("\n") else "\n")


def print_file_result(completed: int, total: int, result: FileResult) -> None:
    textbook_file = result.textbook_file
    relative_file = (
        textbook_file.textbook.module_path / textbook_file.path.name
    ).as_posix()
    status = result.status.upper()
    duration = (
        f">{result.wall_seconds:.2f}s"
        if result.status == "timeout"
        else f"{result.wall_seconds:.2f}s"
    )
    book_label = f"[{textbook_file.textbook.name}]"
    print(
        f"[{completed:>3}/{total}] {book_label:<11} "
        f"[{textbook_file.book_index:>2}/{textbook_file.book_total:<2}] "
        f"{relative_file:<76} {status:<14} {duration:>10}",
        flush=True,
    )
    if result.source_path or result.line is not None:
        location = result.source_path or relative_file
        if result.line is not None:
            location = f"{location}:{result.line}"
        location_label = "stuck near" if result.status in {
            "timeout",
            "contract_error",
            "cancelled",
        } else "location"
        print(f"           {location_label:<9}| {location}", flush=True)
    if result.statement:
        print(f"           statement| {single_line(result.statement)}", flush=True)
    if result.message:
        print(f"           error    | {single_line(result.message)}", flush=True)
    if (
        result.output
        and (
            result.status not in {"success", "failed", "timeout"}
            or (result.status == "failed" and result.statement is None)
        )
    ):
        print(f"           output   | {single_line(result.output)}", flush=True)


def run_gates(
    repository_root: Path,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> list[GateResult]:
    with ThreadPoolExecutor(max_workers=len(GATES)) as executor:
        futures = [
            executor.submit(run_cargo_test, repository_root, label, test_name, runner)
            for label, test_name in GATES
        ]
        return [future.result() for future in futures]


def run_cargo_test(
    repository_root: Path,
    label: str,
    test_name: str,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
    controller: ProcessController | None = None,
) -> GateResult:
    command = cargo_test_command(test_name)
    start = time.perf_counter()
    if controller is not None:
        outcome = controller.run(command, cwd=repository_root, merge_stderr=True)
        status = {
            "completed": "success" if outcome.returncode == 0 else "failed",
            "cancelled": "cancelled",
            "not_started": "not_started",
            "launch_error": "launch_error",
        }.get(outcome.status, outcome.status)
        output = outcome.stdout
        if outcome.stderr:
            output = diagnostic_tail(output, outcome.stderr)
        if status == "cancelled":
            output = diagnostic_tail(
                output,
                "stopped because the "
                f"{controller.timeout_seconds:g}s global deadline expired",
            )
        elif status == "not_started":
            output = (
                "not started before the "
                f"{controller.timeout_seconds:g}s global deadline expired\n"
            )
        return GateResult(
            label=label,
            command=tuple(command),
            status=status,
            returncode=outcome.returncode,
            output=output,
            wall_seconds=outcome.wall_seconds,
        )
    try:
        completed = runner(
            command,
            cwd=repository_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except OSError as error:
        return GateResult(
            label=label,
            command=tuple(command),
            status="launch_error",
            returncode=2,
            output=f"failed to launch cargo: {type(error).__name__}: {error}\n",
            wall_seconds=time.perf_counter() - start,
        )

    return GateResult(
        label=label,
        command=tuple(command),
        status="success" if completed.returncode == 0 else "failed",
        returncode=completed.returncode,
        output=completed.stdout or "",
        wall_seconds=time.perf_counter() - start,
    )


def cargo_test_command(test_name: str) -> list[str]:
    return ["cargo", "test", "--release", test_name, "--", "--nocapture"]


def textbook_file_command(binary: Path, file_path: Path) -> list[str]:
    return [str(binary), "-compact", "-runner", "-f", str(file_path)]


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def output_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def process_exit_description(returncode: int) -> str:
    if returncode < 0:
        return f"terminated by signal {-returncode}"
    return f"exit {returncode}"


def signal_process_group(
    process: subprocess.Popen[str], process_signal: signal.Signals
) -> None:
    if process.poll() is not None:
        return
    try:
        if os.name == "nt":
            if process_signal == signal.SIGTERM:
                process.terminate()
            else:
                process.kill()
        else:
            os.killpg(process.pid, process_signal)
    except ProcessLookupError:
        pass
    except PermissionError:
        signal_process_tree(process, process_signal)


def signal_process_tree(
    process: subprocess.Popen[str], process_signal: signal.Signals
) -> None:
    process_ids = [process.pid]
    try:
        listing = subprocess.run(
            ["ps", "-Ao", "pid=,ppid="],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            timeout=0.5,
        )
        pairs = [
            tuple(int(part) for part in line.split())
            for line in listing.stdout.splitlines()
            if len(line.split()) == 2
        ]
        index = 0
        while index < len(process_ids):
            parent = process_ids[index]
            process_ids.extend(
                child
                for child, parent_id in pairs
                if parent_id == parent and child not in process_ids
            )
            index += 1
    except (OSError, subprocess.SubprocessError, ValueError):
        pass

    for process_id in reversed(process_ids):
        try:
            os.kill(process_id, process_signal)
        except (PermissionError, ProcessLookupError):
            pass


def stop_process_group(process: subprocess.Popen[str]) -> None:
    signal_process_group(process, signal.SIGTERM)
    try:
        process.wait(timeout=0.5)
    except subprocess.TimeoutExpired:
        signal_process_group(process, signal.SIGKILL)


def diagnostic_tail(*values: object, lines: int = 12) -> str:
    text = "\n".join(str(value).strip() for value in values if value)
    return "\n".join(text.splitlines()[-lines:])


def nested_dicts(value: object) -> list[dict[str, object]]:
    found: list[dict[str, object]] = []
    if isinstance(value, dict):
        found.append(value)
        for child in value.values():
            found.extend(nested_dicts(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(nested_dicts(child))
    return found


def first_nonempty_line(value: str) -> str | None:
    return next((line.strip() for line in value.splitlines() if line.strip()), None)


def first_top_level_statement(path: Path) -> tuple[int | None, str | None]:
    return next_top_level_statement(path, 0)


def next_top_level_statement(
    path: Path, after_line: int
) -> tuple[int | None, str | None]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return None, None
    triple_quote: str | None = None
    for line_number, line in enumerate(lines, start=1):
        stripped = line.strip()
        if triple_quote:
            if stripped.count(triple_quote) % 2 == 1:
                triple_quote = None
            continue
        if stripped.startswith(('"""', "'''")):
            delimiter = stripped[:3]
            if stripped.count(delimiter) % 2 == 1:
                triple_quote = delimiter
            continue
        if (
            line_number > after_line
            and stripped
            and not line[0].isspace()
            and not stripped.startswith("#")
        ):
            return line_number, stripped
    return None, None


def relative_display(repository_root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repository_root.resolve()).as_posix()
    except ValueError:
        return str(path)


def single_line(value: str, limit: int = 180) -> str:
    collapsed = " ".join(value.split())
    return collapsed if len(collapsed) <= limit else collapsed[: limit - 3] + "..."


if __name__ == "__main__":
    raise SystemExit(main())
