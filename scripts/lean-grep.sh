#!/usr/bin/env bash
# Smart grep restricted to Lean source files in the project.
# Excludes .lake/, .git/, and only matches .lean files.
#
# Usage:
#   scripts/lean-grep.sh [GREP_FLAGS...] PATTERN [PATH...]
#
# Examples:
#   scripts/lean-grep.sh -n 'TangentSpace I'         # show line numbers
#   scripts/lean-grep.sh -l 'open scoped Riemannian' # list files only
#   scripts/lean-grep.sh -E 'covDeriv|mlieBracket'   # extended regex
#
# Equivalent to:
#   grep -r --include='*.lean' --exclude-dir=.lake --exclude-dir=.git "$@"
# but always with the right exclusions so you never accidentally match
# Mathlib source under .lake/ or stale build artifacts.

set -euo pipefail

if [[ $# -eq 0 ]]; then
  echo "Usage: $0 [GREP_FLAGS...] PATTERN [PATH...]" >&2
  echo "If no PATH given, searches from cwd." >&2
  exit 1
fi

# Default search root if no path given: current directory.
HAS_PATH=0
for arg in "$@"; do
  case "$arg" in
    -*) ;;
    *) HAS_PATH=1; break ;;
  esac
done

if [[ $HAS_PATH -eq 0 ]]; then
  exec grep -r --include='*.lean' --exclude-dir=.lake --exclude-dir=.git "$@" .
else
  exec grep -r --include='*.lean' --exclude-dir=.lake --exclude-dir=.git "$@"
fi
