#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build
audit_output="$(mktemp)"
trap 'rm -f -- "$audit_output"' EXIT
lake env lean Audit.lean | tee "$audit_output"
if grep -q 'sorryAx' "$audit_output"; then
  echo 'FAILED: an audited theorem depends on an admitted proof.' >&2
  exit 1
fi
echo 'Build and axiom audit passed.'
