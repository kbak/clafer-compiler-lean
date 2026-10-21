#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ $# != 0 ]]; then
  echo 'Usage: bash scripts/check.sh (all checks are mandatory)' >&2
  exit 2
fi
export PYTHONDONTWRITEBYTECODE=1
export LAKE_ARTIFACT_CACHE=false
export LAKE_RESTORE_ARTIFACTS=true
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

# [impl->req~compiler-build~1]
python3 scripts/check.py
bash -n scripts/check.sh
bash -n scripts/prepare_dependencies.sh
python3 scripts/project_modules.py
command -v lake >/dev/null

# An optional external cache supplies dependencies only. The source/manifest
# checks below still run; no project output or proof result is restored here.
if [[ -n "${CLAFER_COMPILER_PACKAGES:-}" && ! -e .lake/packages ]]; then
  cp -a --reflink=auto "$CLAFER_COMPILER_PACKAGES" .lake/packages
fi

lake env lean --version
python3 scripts/project_modules.py --dependencies
lake build
python3 scripts/project_modules.py --dependencies
mapfile -t modules < .lake/validation/modules.txt
lake build "${modules[@]/#/+}"
lake env lean -DwarningAsError=true .lake/validation/axiom_audit.lean &
audit_pid=$!

# leanchecker loads each project's .olean and replays its kernel declarations.
# The recursive roots also include helpers not imported by the library root.
# Audit, replay and isolated regressions only read these completed build outputs.
# Two bounded replay workers use LeanChecker's existing task scheduler; all
# modules are still replayed, with at most two import environments loaded at once.
LEAN_NUM_THREADS=2 lake env leanchecker --verbose ClaferCompiler Main tests &
kernel_pid=$!
test_status=0
lake env python3 scripts/run_tests.py || test_status=$?
kernel_status=0
wait "$kernel_pid" || kernel_status=$?
audit_status=0
wait "$audit_pid" || audit_status=$?
if (( audit_status != 0 )); then exit "$audit_status"; fi
if (( test_status != 0 )); then exit "$test_status"; fi
if (( kernel_status != 0 )); then exit "$kernel_status"; fi
echo 'All build, native, import, kernel, axiom and regression gates passed.'
