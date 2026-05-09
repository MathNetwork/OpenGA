#!/usr/bin/env bash
# Rewrite Lean import path prefixes across the project.
#
# Usage:
#   scripts/rewrite-import.sh OLD_PATH NEW_PATH
#
# Example:
#   scripts/rewrite-import.sh OpenGALib.Riemannian.Util OpenGALib.Util
#
# This rewrites every `import OLD_PATH...` line to `import NEW_PATH...`
# across all .lean files (excluding .lake/, .git/). Prefix-only match,
# so `import OLD_PATH.X.Y` becomes `import NEW_PATH.X.Y` automatically.
#
# Refuses to run on a dirty working tree — commit or stash first so the
# bulk edit is one revertible step.

set -euo pipefail

if [[ $# -ne 2 ]]; then
  cat >&2 <<EOF
Usage: $0 OLD_PATH NEW_PATH

Example:
  $0 OpenGALib.Riemannian.Util OpenGALib.Util
EOF
  exit 1
fi

OLD="$1"
NEW="$2"

# Refuse to run on dirty working tree.
if [[ -n "$(git status --porcelain --untracked-files=no)" ]]; then
  echo "error: working tree not clean (modified files exist)." >&2
  echo "Commit or stash first; bulk edits should be a single revertible step." >&2
  git status --short >&2
  exit 1
fi

# Escape regex metacharacters in OLD path.
OLD_ESCAPED=$(printf '%s' "$OLD" | sed 's/[][\\.*^$/]/\\&/g')

# Find files containing the import.
FILES=$(grep -rlE "^import ${OLD_ESCAPED}" \
          --include="*.lean" \
          --exclude-dir=.lake --exclude-dir=.git \
          . || true)

if [[ -z "$FILES" ]]; then
  echo "No files import '$OLD'. Nothing to do." >&2
  exit 0
fi

# Show what will change.
COUNT=$(echo "$FILES" | wc -l | tr -d ' ')
echo "Rewriting 'import $OLD...' → 'import $NEW...' in $COUNT file(s):"
echo "$FILES" | sed 's/^/  /'
echo

# Apply.
echo "$FILES" | xargs perl -i -pe "s|^import ${OLD_ESCAPED}|import ${NEW}|"

echo "Done. Verify with:"
echo "  lake build"
echo "If green, commit. If broken, 'git reset --hard' to revert."
