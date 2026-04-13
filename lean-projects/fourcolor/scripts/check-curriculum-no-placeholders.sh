#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

TARGET_DIRS=(
  "FourColor/Curriculum/Actual"
  "FourColor/Curriculum/Checks"
)

EXISTING_TARGETS=()
for dir in "${TARGET_DIRS[@]}"; do
  if [ -d "${dir}" ]; then
    EXISTING_TARGETS+=("${dir}")
  fi
done

if [ "${#EXISTING_TARGETS[@]}" -eq 0 ]; then
  echo "No curriculum production paths found to check."
  exit 0
fi

PATTERN='\b(axiom|admit|sorry)\b'

if command -v rg >/dev/null 2>&1; then
  SEARCH_CMD=(rg -n --glob '*.lean' "${PATTERN}" "${EXISTING_TARGETS[@]}")
elif command -v grep >/dev/null 2>&1; then
  # Portable fallback when ripgrep is unavailable for the runtime user.
  SEARCH_CMD=(
    grep -RInE --include='*.lean'
    '(^|[^[:alnum:]_])(axiom|admit|sorry)([^[:alnum:]_]|$)'
    "${EXISTING_TARGETS[@]}"
  )
else
  echo "❌ Curriculum placeholder guard failed: neither rg nor grep is available."
  exit 2
fi

if "${SEARCH_CMD[@]}"; then
  echo
  echo "❌ Curriculum placeholder guard failed."
  echo "   Found forbidden tokens in: ${EXISTING_TARGETS[*]}"
  exit 1
fi

echo "✅ Curriculum placeholder guard passed (${EXISTING_TARGETS[*]})."
