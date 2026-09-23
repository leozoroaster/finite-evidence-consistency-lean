#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

# Use portable grep so no extra search tool is needed on a fresh machine.
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|sorryAx|native_decide|axiom|unsafe|partial|extern)([^[:alnum:]_]|$)|@\[implemented_by' \
  FiniteEvidenceConsistency.lean FiniteEvidence/*.lean Audit.lean; then
  echo 'Unexpected proof placeholder, added axiom, or unsafe evaluation.' >&2
  exit 1
else
  scan_status=$?
  [[ "$scan_status" -eq 1 ]] || exit "$scan_status"
fi

lake env lean --version
lake build
lake env lean --trust=0 Audit.lean
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" \
  lake env leanchecker -v FiniteEvidence FiniteEvidenceConsistency
echo 'Verified: build, twelve guarded axiom checks, source scan, and kernel replay passed.'
