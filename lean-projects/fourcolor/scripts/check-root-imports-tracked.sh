#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

ROOT_FILE="FourColor.lean"
PREFIX="FourColor."

if [ ! -f "${ROOT_FILE}" ]; then
  echo "❌ Missing ${ROOT_FILE}"
  exit 2
fi

missing=0
untracked=0
checked=0

while IFS= read -r mod; do
  [ -z "${mod}" ] && continue
  case "${mod}" in
    ${PREFIX}*) ;;
    *) continue ;;
  esac

  rel="${mod//./\/}.lean"
  checked=$((checked + 1))

  if [ ! -f "${rel}" ]; then
    echo "MISSING: ${rel} (import ${mod})"
    missing=$((missing + 1))
    continue
  fi

  if ! git ls-files --error-unmatch "${rel}" >/dev/null 2>&1; then
    echo "UNTRACKED: ${rel} (import ${mod})"
    untracked=$((untracked + 1))
  fi
done < <(awk '/^import[[:space:]]+/ { print $2 }' "${ROOT_FILE}")

if [ "${missing}" -gt 0 ] || [ "${untracked}" -gt 0 ]; then
  echo
  echo "❌ Root import trackedness check failed for ${ROOT_FILE}."
  echo "   checked=${checked} missing=${missing} untracked=${untracked}"
  exit 1
fi

echo "✅ Root import trackedness check passed for ${ROOT_FILE} (checked=${checked})."
