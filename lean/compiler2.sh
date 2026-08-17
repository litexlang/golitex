#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPOSITORY_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
exec cargo run --quiet --manifest-path "$REPOSITORY_ROOT/Cargo.toml" --bin litex_to_lean_compiler2 -- "$@"
