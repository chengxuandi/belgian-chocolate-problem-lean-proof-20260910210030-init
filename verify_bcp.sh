#!/usr/bin/env bash
set -euo pipefail

# Run from any directory, including Git Bash on Windows.
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if command -v lake >/dev/null 2>&1; then
  bcp_lake="$(command -v lake)"
elif [[ -x "$HOME/.elan/bin/lake.exe" ]]; then
  bcp_lake="$HOME/.elan/bin/lake.exe"
else
  echo "ERROR: lake not found" >&2
  exit 1
fi
if command -v python3 >/dev/null 2>&1; then
  bcp_python="$(command -v python3)"
elif command -v python >/dev/null 2>&1; then
  bcp_python="$(command -v python)"
else
  echo "ERROR: Python 3 not found" >&2
  exit 1
fi

mkdir -p .lake/bcp-verification
"$bcp_lake" env lean --version | tee .lake/bcp-verification/toolchain.log
"$bcp_python" scripts/audit_bcp_source.py | tee .lake/bcp-verification/source-audit.log
"$bcp_python" scripts/build_bcp_serial.py "$bcp_lake" 2>&1 | tee .lake/bcp-verification/all-modules.log
"$bcp_lake" build BCPThreshold 2>&1 | tee .lake/bcp-verification/build.log

# The serial prebuild includes standalone audit files, not just root imports.
"$bcp_lake" env lean BCPThreshold/FinalAudit.lean 2>&1 | tee .lake/bcp-verification/final-audit.log
grep -q 'FINAL_AXIOM_AUDIT = PASS' .lake/bcp-verification/final-audit.log

printf '\n========================================\n'
printf 'BCP FORMAL VERIFICATION: PASS\n'
printf '========================================\n'
