#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
GOLITEX_ROOT="$(CDPATH= cd "$SCRIPT_DIR/.." && pwd -P)"
LITEX_ROOT="$(CDPATH= cd "$GOLITEX_ROOT/.." && pwd -P)"

DRY_RUN=0
LIST_ONLY=0
ALLOW_INTERACTIVE=0
CONTINUE_ON_ERROR=0
ONLY_LABEL=""

usage() {
  cat <<'EOF'
Usage: scripts/update_external_repos.sh [options]

Update external repositories from the ignored working copies under golitex.

Options:
  --list                 Show the configured mappings and exit.
  --dry-run              Show what would be updated without changing files.
  --allow-interactive    Also run update scripts that may prompt, commit, or push.
  --continue-on-error    Continue with later repos after one update fails.
  --only NAME            Run only one mapping by label.
  -h, --help             Show this help.

Default behavior updates confirmed mappings, then prints git status for every
target repo it touched.

Set UPDATE_COMMIT_MSG="..." to override the default commit message used by
target update scripts that commit changes.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --list)
      LIST_ONLY=1
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    --allow-interactive)
      ALLOW_INTERACTIVE=1
      shift
      ;;
    --continue-on-error)
      CONTINUE_ON_ERROR=1
      shift
      ;;
    --only)
      if [[ $# -lt 2 ]]; then
        echo "--only requires a mapping label" >&2
        exit 2
      fi
      ONLY_LABEL="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

ENTRIES=$(cat <<'EOF'
MATH-500-litex|scripts/MATH-500-litex|MATH-500-litex|script|confirmed exact repo; target update.sh is non-interactive
gsm8k-litex|scripts/gsm8k-litex|gsm8k-litex|rsync|confirmed exact repo; no target update.sh found
math23k-litex|scripts/math23k-litex|math23k-litex|rsync|confirmed exact repo; no target update.sh found
The-Mechanics-of-Litex-Proof|scripts/The-Mechanics-of-Litex-Proof|The-Mechanics-of-Litex-Proof|script|confirmed exact repo; target update.sh uses a default commit message
litex-minif2f|scripts/litex-minif2f|litex-minif2f|rsync|confirmed target; use rsync because target update.sh points at golitex/litex-minif2f instead of golitex/scripts/litex-minif2f
mathematics_in_litex|scripts/mathematics_in_litex|mathematcis_in_litex|rsync|confirmed target; external directory is currently named ../mathematcis_in_litex
MetaMathQA-litex|scripts/MetaMathQA-litex|litex-metamathqa|rsync|confirmed target
analysis-one|scripts/analysis-one|litex-analysis-textbook|rsync|confirmed target; target update.sh syncs in the opposite direction, so use rsync here
high_school_book|scripts/high_school_book|litex-high-school-math|rsync|confirmed target
skills|CODEX_HOME/skills/litex*|skills|target-script|confirmed target; update.sh discovers all Codex skills whose directory name starts with litex
EOF
)

print_mapping() {
  local label="$1"
  local source_rel="$2"
  local target_rel="$3"
  local mode="$4"
  local note="$5"
  printf '%-32s %-12s %s -> ../%s\n' "$label" "$mode" "$source_rel" "$target_rel"
  printf '  %s\n' "$note"
}

run_cmd() {
  if [[ "$DRY_RUN" -eq 1 ]]; then
    printf '  dry-run:'
    printf ' %q' "$@"
    printf '\n'
  else
    "$@"
  fi
}

mirror_with_rsync() {
  local source_abs="$1"
  local target_abs="$2"

  if ! command -v rsync >/dev/null 2>&1; then
    echo "rsync is required but was not found" >&2
    return 1
  fi

  run_cmd rsync -a --delete \
    --exclude '.git/' \
    --exclude 'update.sh' \
    "$source_abs"/ "$target_abs"/
}

run_update_script() {
  local target_abs="$1"
  local update_script="$target_abs/update.sh"

  if [[ ! -f "$update_script" ]]; then
    echo "update.sh not found: $update_script" >&2
    return 1
  fi

  if [[ "$DRY_RUN" -eq 1 ]]; then
    printf '  dry-run: cd %q && ./update.sh\n' "$target_abs"
    return 0
  fi

  (cd "$target_abs" && ./update.sh)
}

show_git_status() {
  local label="$1"
  local target_abs="$2"

  if [[ ! -d "$target_abs/.git" ]]; then
    return 0
  fi

  echo
  echo "== git status: $label =="
  if ! git -C "$target_abs" \
    -c filter.lfs.required=false \
    -c filter.lfs.process= \
    -c filter.lfs.clean= \
    -c filter.lfs.smudge= \
    status --short
  then
    echo "warning: git status failed for $label" >&2
  fi
}

run_entry() {
  local label="$1"
  local source_rel="$2"
  local target_rel="$3"
  local mode="$4"
  local note="$5"
  local source_abs="$GOLITEX_ROOT/$source_rel"
  local target_abs="$LITEX_ROOT/$target_rel"

  if [[ -n "$ONLY_LABEL" && "$ONLY_LABEL" != "$label" ]]; then
    return 0
  fi

  if [[ "$LIST_ONLY" -eq 1 ]]; then
    print_mapping "$label" "$source_rel" "$target_rel" "$mode" "$note"
    return 0
  fi

  if [[ "$mode" == "skip" ]]; then
    echo "skip $label: $note"
    return 0
  fi

  if [[ "$mode" == "interactive" && "$ALLOW_INTERACTIVE" -ne 1 ]]; then
    echo "skip $label: interactive update; rerun with --allow-interactive to include it"
    return 0
  fi

  if [[ "$mode" == "target-script" ]]; then
    if [[ ! -d "$target_abs" ]]; then
      echo "target directory not found for $label: $target_abs" >&2
      return 1
    fi

    echo
    echo "== update: $label =="
    echo "$source_rel -> $target_abs"
    run_update_script "$target_abs"
    show_git_status "$label" "$target_abs"
    return 0
  fi

  if [[ ! -d "$source_abs" ]]; then
    echo "source directory not found for $label: $source_abs" >&2
    return 1
  fi

  if [[ ! -d "$target_abs" ]]; then
    echo "target directory not found for $label: $target_abs" >&2
    return 1
  fi

  if [[ "$source_abs" == "$target_abs" ]]; then
    echo "source and target are the same for $label: $source_abs" >&2
    return 1
  fi

  echo
  echo "== update: $label =="
  echo "$source_abs -> $target_abs"

  case "$mode" in
    script|interactive|target-script)
      run_update_script "$target_abs"
      ;;
    rsync)
      mirror_with_rsync "$source_abs" "$target_abs"
      ;;
    *)
      echo "unknown mode for $label: $mode" >&2
      return 1
      ;;
  esac

  show_git_status "$label" "$target_abs"
}

FAILED=()
MATCHED_ONLY=0

while IFS='|' read -r label source_rel target_rel mode note; do
  [[ -z "$label" ]] && continue

  if [[ -n "$ONLY_LABEL" && "$ONLY_LABEL" == "$label" ]]; then
    MATCHED_ONLY=1
  fi

  if ! run_entry "$label" "$source_rel" "$target_rel" "$mode" "$note"; then
    FAILED+=("$label")
    if [[ "$CONTINUE_ON_ERROR" -ne 1 ]]; then
      break
    fi
  fi
done <<< "$ENTRIES"

if [[ -n "$ONLY_LABEL" && "$MATCHED_ONLY" -ne 1 ]]; then
  echo "no mapping named: $ONLY_LABEL" >&2
  exit 2
fi

if [[ ${#FAILED[@]} -gt 0 ]]; then
  echo
  echo "failed mappings:"
  printf '  %s\n' "${FAILED[@]}"
  exit 1
fi

if [[ "$LIST_ONLY" -ne 1 ]]; then
  echo
  echo "done"
fi
