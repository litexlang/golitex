#!/usr/bin/env python3
"""Guard Litex's Tier 1 frozen framework backbone and Tier 2 append-only dispatchers.

Tier model:
- Tier 1 (Frozen Backbone): Pure orchestration, transaction/scope management,
  top-level parser entry, knowledge-base backbone, verification pipeline skeleton,
  and fact storage/inference pipeline. Locked by exact SHA-256 in
  `.github/framework_lock.json`.
- Tier 2 (Enum & Append-Only Dispatch Registries): AST/proof-result enums and
  pure routing `match` / strategy tables. Must never mutate environment stacks
  or transaction state. Changes to existing registry entries are advisory.
- Tier 3 (Feature & Domain Leaves): All concrete statement handlers, calculus
  rules/strategies, domain verifiers, and backend compilers (`compile_to_*`).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

LOCK_REL_PATH = ".github/framework_lock.json"

TIER1_FROZEN_BACKBONE: Tuple[str, ...] = (
    # Top-level parser entry
    "src/parse/parse.rs",
    # Core runtime & transactional environment state
    "src/runtime/runtime.rs",
    "src/exec_env/exec_env.rs",
    "src/exec_env/merge_exec_env.rs",
    # Top-level code & module execution backbone
    "src/run/run_litex_code.rs",
    "src/run_module/import_kb.rs",
    # Knowledge-base persistence & mount backbone
    "src/knowledge_base/mod.rs",
    "src/knowledge_base/paths.rs",
    "src/knowledge_base/fingerprint.rs",
    "src/knowledge_base/manifest.rs",
    "src/knowledge_base/mount.rs",
    "src/knowledge_base/import_cache.rs",
    "src/knowledge_base/definitions_memory_codec.rs",
    # Statement & fact verification pipeline skeleton
    "src/execute/exec_stmt.rs",
    "src/execute/execute_fact_stmt/exec_fact_stmt.rs",
    "src/execute/execute_fact_stmt/verify.rs",
    "src/execute/execute_fact_stmt/verify_state.rs",
    "src/execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_fact.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_well_defined.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equal_fact.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_proof.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/verify_atomic_except_equality.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof.rs",
    # Fact storage & forward inference pipeline skeleton
    "src/store_fact_and_infer/store_fact_and_infer.rs",
    "src/store_fact_and_infer/store_fact.rs",
    "src/store_fact_and_infer/infer_fact/infer_fact.rs",
)

TIER2_ENUM_REGISTRIES: Tuple[str, ...] = (
    "src/ast/obj.rs",
    "src/ast/fact/fact.rs",
    "src/ast/fact/atomic.rs",
    "src/ast/stmt.rs",
    "src/execute/exec_stmt_result.rs",
    "src/execute/execute_fact_stmt/verify_fact_result.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/result.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_builtin_strategy_result.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/result.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_strategy/result.rs",
)

TIER2_DISPATCH_REGISTRIES: Tuple[str, ...] = (
    "src/parse/builtin_aliases.rs",
    "src/execute/dispatch_stmt.rs",
    "src/execute/execute_fact_stmt/well_defined_results/verify_obj/dispatch_obj_well_definedness.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/dispatch_predicate_domain_wd.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_by_builtin_strategy.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/search_equal_fact_builtin_rule.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_strategy/search_atomic_except_equality_fact_proof_by_builtin_strategy.rs",
    "src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof_by_builtin_rules/search_atomic_except_equality_fact_proof_by_builtin_rule.rs",
    "src/execute/execute_by_stmt/builtin_thm/builtin_thm.rs",
    "src/knowledge_base/def_prop_codec.rs",
    "src/knowledge_base/remap.rs",
)

FORBIDDEN_TIER2_TOKENS: Tuple[str, ...] = (
    "merge_from(",
    "execution_environments_stack",
    "run_in_local_env_and_take_env",
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run_git(repo_root: Path, args: Sequence[str]) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-C", str(repo_root), *args],
        capture_output=True,
        check=False,
    )


def resolve_repo_root(explicit_root: Optional[str]) -> Path:
    if explicit_root:
        return Path(explicit_root).resolve()
    proc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode == 0 and proc.stdout.strip():
        return Path(proc.stdout.strip()).resolve()
    return Path(__file__).resolve().parents[2]


def read_index_or_disk_bytes(repo_root: Path, rel_path: str, use_index: bool) -> Optional[bytes]:
    if use_index:
        proc = run_git(repo_root, ["show", f":{rel_path}"])
        if proc.returncode == 0:
            return proc.stdout
        # Check if deleted in index
        ls_proc = run_git(repo_root, ["ls-files", "--cached", "--", rel_path])
        if ls_proc.returncode == 0 and not ls_proc.stdout.strip():
            # If tracked in HEAD, it was staged for deletion
            head_proc = run_git(repo_root, ["cat-file", "-e", f"HEAD:{rel_path}"])
            if head_proc.returncode == 0:
                return None
    disk_path = repo_root / rel_path
    if not disk_path.is_file():
        return None
    return disk_path.read_bytes()


def read_git_object_bytes(repo_root: Path, spec: str) -> Optional[bytes]:
    proc = run_git(repo_root, ["show", spec])
    if proc.returncode != 0:
        return None
    return proc.stdout


def build_lock_payload(repo_root: Path) -> dict:
    tier1_hashes: Dict[str, str] = {}
    missing: List[str] = []
    for rel_path in TIER1_FROZEN_BACKBONE:
        full_path = repo_root / rel_path
        if not full_path.is_file():
            missing.append(rel_path)
            continue
        tier1_hashes[rel_path] = sha256_bytes(full_path.read_bytes())
    if missing:
        raise FileNotFoundError(
            f"Missing Tier 1 backbone file(s): {', '.join(missing)}"
        )
    return {
        "schema_version": 1,
        "description": (
            "Litex kernel architectural lock. Tier 1 files are frozen framework "
            "backbone files locked by SHA-256. Tier 2 files are enum and append-only "
            "dispatch registries."
        ),
        "tier1_frozen_backbone": tier1_hashes,
        "tier2_enum_registries": list(TIER2_ENUM_REGISTRIES),
        "tier2_dispatch_registries": list(TIER2_DISPATCH_REGISTRIES),
        "forbidden_tier2_tokens": list(FORBIDDEN_TIER2_TOKENS),
    }


def write_lock_file(repo_root: Path) -> Path:
    payload = build_lock_payload(repo_root)
    lock_path = repo_root / LOCK_REL_PATH
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    lock_path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    return lock_path


def load_lock_payload(repo_root: Path, use_index: bool) -> Tuple[Optional[dict], Optional[str]]:
    raw = read_index_or_disk_bytes(repo_root, LOCK_REL_PATH, use_index=use_index)
    if raw is None:
        return None, f"Missing lock file `{LOCK_REL_PATH}`. Run `python3 .github/scripts/framework_guard.py --update-lock`."
    try:
        data = json.loads(raw.decode("utf-8"))
    except Exception as exc:  # noqa: BLE001
        return None, f"Invalid JSON in `{LOCK_REL_PATH}`: {exc}"
    if not isinstance(data, dict) or not isinstance(data.get("tier1_frozen_backbone"), dict):
        return None, f"Malformed `{LOCK_REL_PATH}`: missing `tier1_frozen_backbone` mapping."
    return data, None


def is_benign_removed_line(line: str) -> bool:
    """Allow pure whitespace or `use ...` import grouping lines reshaped by rustfmt."""
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith("//"):
        return True
    if stripped.startswith("use ") or stripped.startswith("pub use ") or stripped.startswith("pub(crate) use "):
        return True
    return False


def analyze_diff_lines(diff_text: str) -> Tuple[int, int]:
    """Return added and non-benign removed line counts."""
    added = 0
    removed = 0
    for raw_line in diff_text.splitlines():
        if raw_line.startswith("+++") or raw_line.startswith("---"):
            continue
        if raw_line.startswith("+"):
            added += 1
        elif raw_line.startswith("-"):
            content = raw_line[1:]
            if not is_benign_removed_line(content):
                removed += 1
    return added, removed


def check_tier2_forbidden_tokens(
    repo_root: Path,
    tier2_paths: Iterable[str],
    use_index: bool,
) -> List[str]:
    errors: List[str] = []
    for rel_path in tier2_paths:
        raw = read_index_or_disk_bytes(repo_root, rel_path, use_index=use_index)
        if raw is None:
            errors.append(f"Missing Tier 2 registry file `{rel_path}`.")
            continue
        text = raw.decode("utf-8", errors="replace")
        for token in FORBIDDEN_TIER2_TOKENS:
            if token in text:
                errors.append(
                    f"Tier 2 registry `{rel_path}` contains forbidden framework-state token `{token}`."
                )
    return errors


def detect_ci_base_commit(repo_root: Path) -> Optional[str]:
    base_ref = os.environ.get("GITHUB_BASE_REF", "").strip()
    if base_ref:
        candidate = f"origin/{base_ref}"
        if run_git(repo_root, ["rev-parse", "--verify", candidate]).returncode == 0:
            mb = run_git(repo_root, ["merge-base", candidate, "HEAD"])
            if mb.returncode == 0:
                return mb.stdout.decode("utf-8").strip()
    if run_git(repo_root, ["rev-parse", "--verify", "HEAD~1"]).returncode == 0:
        return "HEAD~1"
    return None


def check_guard(repo_root: Path, mode: str) -> int:
    """mode is one of 'staged', 'worktree', 'ci'."""
    use_index = mode == "staged"
    allow_tier1_unlock = os.environ.get("ALLOW_FRAMEWORK_UNLOCK", "") == "1"

    lock_data, lock_err = load_lock_payload(repo_root, use_index=use_index)
    if lock_err is not None or lock_data is None:
        print(f"[FRAMEWORK LOCK ERROR] {lock_err}", file=sys.stderr)
        return 2

    locked_tier1: Dict[str, str] = lock_data["tier1_frozen_backbone"]
    expected_tier1_set = set(TIER1_FROZEN_BACKBONE)
    locked_tier1_set = set(locked_tier1.keys())

    if expected_tier1_set != locked_tier1_set:
        missing_in_lock = sorted(expected_tier1_set - locked_tier1_set)
        extra_in_lock = sorted(locked_tier1_set - expected_tier1_set)
        print(
            "[FRAMEWORK LOCK ERROR] `.github/framework_lock.json` Tier 1 list is out of sync with `framework_guard.py`.",
            file=sys.stderr,
        )
        if missing_in_lock:
            print(f"  Missing in lock: {', '.join(missing_in_lock)}", file=sys.stderr)
        if extra_in_lock:
            print(f"  Extra in lock: {', '.join(extra_in_lock)}", file=sys.stderr)
        print(
            "  Run `python3 .github/scripts/framework_guard.py --update-lock` to synchronize.",
            file=sys.stderr,
        )
        return 2

    # 1. Verify every Tier 1 file matches the SHA-256 lock.
    mismatched_tier1: List[str] = []
    missing_tier1: List[str] = []
    for rel_path in TIER1_FROZEN_BACKBONE:
        raw = read_index_or_disk_bytes(repo_root, rel_path, use_index=use_index)
        if raw is None:
            missing_tier1.append(rel_path)
            continue
        actual_hash = sha256_bytes(raw)
        if actual_hash != locked_tier1[rel_path]:
            mismatched_tier1.append(rel_path)

    if missing_tier1 or mismatched_tier1:
        print(
            "\n[FRAMEWORK LOCK ERROR] Tier 1 Frozen Backbone modification detected!",
            file=sys.stderr,
        )
        for rel_path in missing_tier1:
            print(f"  - MISSING/DELETED: {rel_path}", file=sys.stderr)
        for rel_path in mismatched_tier1:
            print(f"  - MODIFIED:        {rel_path}", file=sys.stderr)
        print(
            "\nTier 1 files hold pure framework orchestration and core structs and must not change",
            file=sys.stderr,
        )
        print(
            "during normal feature, calculus-strategy, or backend-compiler work.",
            file=sys.stderr,
        )
        print(
            "  * New syntax/rules/strategies belong in Tier 2 registries (append-only) + Tier 3 leaf modules.",
            file=sys.stderr,
        )
        print(
            "  * If an intentional framework change was explicitly approved by the maintainer:",
            file=sys.stderr,
        )
        print(
            "      1. python3 .github/scripts/framework_guard.py --update-lock",
            file=sys.stderr,
        )
        print(
            "      2. Stage `.github/framework_lock.json` and commit with ALLOW_FRAMEWORK_UNLOCK=1",
            file=sys.stderr,
        )
        return 2

    # 2. Check if `.github/framework_lock.json` itself changed relative to HEAD / CI base.
    base_spec: Optional[str] = None
    if mode in ("staged", "worktree"):
        if run_git(repo_root, ["rev-parse", "--verify", "HEAD"]).returncode == 0:
            base_spec = "HEAD"
    elif mode == "ci":
        base_spec = detect_ci_base_commit(repo_root)

    if base_spec is not None:
        old_lock_bytes = read_git_object_bytes(repo_root, f"{base_spec}:{LOCK_REL_PATH}")
        if old_lock_bytes is not None:
            try:
                old_lock_data = json.loads(old_lock_bytes.decode("utf-8"))
                old_hashes = old_lock_data.get("tier1_frozen_backbone", {})
            except Exception:  # noqa: BLE001
                old_hashes = {}
            unlocked_paths = [
                p for p in TIER1_FROZEN_BACKBONE if old_hashes.get(p) != locked_tier1.get(p)
            ]
            if unlocked_paths:
                if mode == "ci":
                    joined = ", ".join(unlocked_paths)
                    print(
                        f"::warning title=Tier 1 Framework Lock Updated::Tier 1 backbone lock hashes changed for: {joined}"
                    )
                elif not allow_tier1_unlock:
                    print(
                        "\n[FRAMEWORK LOCK WARNING] `.github/framework_lock.json` updates Tier 1 backbone hashes:",
                        file=sys.stderr,
                    )
                    for rel_path in unlocked_paths:
                        print(f"  - {rel_path}", file=sys.stderr)
                    print(
                        "\nRe-run with `ALLOW_FRAMEWORK_UNLOCK=1` (or confirm interactively in `tools/commit_with_impact.sh`) to authorize.",
                        file=sys.stderr,
                    )
                    return 3
                else:
                    print(
                        f"[Framework Notice] Authorized Tier 1 lock update for: {', '.join(unlocked_paths)}"
                    )
        elif mode in ("staged", "worktree"):
            print(f"[Framework Notice] Initializing `{LOCK_REL_PATH}` ({len(TIER1_FROZEN_BACKBONE)} Tier 1 files locked).")

    # 3. Verify Tier 2 registries never contain forbidden state/transaction tokens.
    all_tier2 = (*TIER2_ENUM_REGISTRIES, *TIER2_DISPATCH_REGISTRIES)
    token_errors = check_tier2_forbidden_tokens(repo_root, all_tier2, use_index=use_index)
    if token_errors:
        print("\n[FRAMEWORK INVARIANT ERROR] Tier 2 purity violation:", file=sys.stderr)
        for err in token_errors:
            print(f"  - {err}", file=sys.stderr)
        return 2

    # 4. Inspect Tier 2 diffs for append-only vs. non-append-only modifications.
    if base_spec is not None:
        append_only_files: List[Tuple[str, int]] = []
        non_append_files: List[str] = []

        for rel_path in all_tier2:
            if mode == "worktree":
                tracked = run_git(repo_root, ["ls-files", "--error-unmatch", "--", rel_path]).returncode == 0
                if not tracked and (repo_root / rel_path).is_file():
                    line_count = len((repo_root / rel_path).read_text(encoding="utf-8", errors="replace").splitlines())
                    append_only_files.append((rel_path, line_count))
                    continue
            if mode == "staged":
                diff_args = ["diff", "--cached", "-U0", base_spec, "--", rel_path]
            elif mode == "worktree":
                diff_args = ["diff", "-U0", base_spec, "--", rel_path]
            else:
                diff_args = ["diff", "-U0", base_spec, "HEAD", "--", rel_path]

            diff_proc = run_git(repo_root, diff_args)
            diff_text = diff_proc.stdout.decode("utf-8", errors="replace")
            if not diff_text.strip():
                continue
            added, removed = analyze_diff_lines(diff_text)
            if removed > 0:
                non_append_files.append(rel_path)
            elif added > 0:
                append_only_files.append((rel_path, added))

        for rel_path, added in append_only_files:
            print(f"[Framework Notice] Tier 2 append-only branch addition: {rel_path} (+{added} lines)")

        if non_append_files:
            print(f"[Framework Notice] Updated Tier 2 registry entries: {', '.join(non_append_files)}")

    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check or update Litex's Tier 1/Tier 2 architectural framework lock."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--staged",
        action="store_true",
        help="Validate staged Git index changes (for pre-commit hook and commit helpers).",
    )
    group.add_argument(
        "--worktree",
        action="store_true",
        help="Validate working tree files against `.github/framework_lock.json` and HEAD.",
    )
    group.add_argument(
        "--ci",
        action="store_true",
        help="Validate repository state in CI and emit GitHub Actions warnings for lock/Tier-2 changes.",
    )
    group.add_argument(
        "--update-lock",
        action="store_true",
        help="Recompute SHA-256 hashes of all Tier 1 frozen backbone files and write `.github/framework_lock.json`.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Override repository root directory (used by unit tests).",
    )
    args = parser.parse_args(argv)
    repo_root = resolve_repo_root(args.repo_root)

    if args.update_lock:
        try:
            lock_path = write_lock_file(repo_root)
        except FileNotFoundError as exc:
            print(f"[FRAMEWORK LOCK ERROR] {exc}", file=sys.stderr)
            return 2
        print(
            f"Updated `{lock_path.relative_to(repo_root)}` ({len(TIER1_FROZEN_BACKBONE)} Tier 1 files hashed)."
        )
        return 0

    if args.ci:
        return check_guard(repo_root, mode="ci")
    if args.worktree:
        return check_guard(repo_root, mode="worktree")
    return check_guard(repo_root, mode="staged")


if __name__ == "__main__":
    sys.exit(main())
