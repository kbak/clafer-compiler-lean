#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
regression_args=()
reference_ci=false
if [[ $# == 1 && $1 == --compiler-ci ]]; then
  regression_args=(--compiler-ci)
elif [[ $# == 1 && $1 == --reference-ci ]]; then
  reference_ci=true
elif [[ $# != 0 ]]; then
  echo 'Usage: bash scripts/check.sh [--compiler-ci | --reference-ci]' >&2
  exit 2
fi
export PYTHONDONTWRITEBYTECODE=1
export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE:-false}"
export LAKE_RESTORE_ARTIFACTS=true
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

# Reuse the pinned semantics check's timing wrapper; a cached build still runs
# every validation gate against the restored artifacts.
run_step() {
  local label=$1 started=$SECONDS status=0
  shift
  printf '\n[check] %s: starting\n' "$label"
  "$@" || status=$?
  printf '[check] %s: exit %s, %ss\n' "$label" "$status" "$((SECONDS - started))"
  return "$status"
}

# [impl->req~compiler-build~1]
run_step 'Repository checks' python3 scripts/check.py
bash -n scripts/check.sh
bash -n scripts/prepare_dependencies.sh
python3 scripts/project_modules.py
command -v lake >/dev/null

# An optional external cache supplies dependencies only. The source/manifest
# checks below still run. Lake may separately reuse traced build artifacts;
# proof and test results are always recomputed.
if [[ -n "${CLAFER_COMPILER_PACKAGES:-}" && ! -e .lake/packages ]]; then
  cp -a --reflink=auto "$CLAFER_COMPILER_PACKAGES" .lake/packages
fi

lake env lean --version
python3 scripts/project_modules.py --dependencies
if $reference_ci; then
  run_step 'Reference corpora' python3 scripts/run_tests.py --reference-ci
  echo 'Reference qualification passed; compiler proof and runtime checks are separate.'
  exit 0
fi
run_step 'Library and native build' lake build
# Lake caches the executable, but not the response file used by native probes
# and qualification. Relink from the restored objects to retain current local
# link inputs, including when an older workspace already has a response file.
rm -f .lake/build/bin/clafer-compiler
run_step 'Native link receipt' env LAKE_ARTIFACT_CACHE=false lake build clafer-compiler
test -s .lake/build/bin/clafer-compiler.rsp
python3 scripts/project_modules.py --dependencies
mapfile -t modules < .lake/validation/modules.txt
run_step 'All module build' lake build "${modules[@]/#/+}"
# Keep the heavy import environments out of the regression CPU/memory budget.
# Every gate is still awaited and its exit status is mandatory, including after
# another validation gate fails. leanchecker recursively includes hidden helpers.
audit_status=0
run_step 'Axiom audit' lake env lean -DwarningAsError=true .lake/validation/axiom_audit.lean || audit_status=$?
test_status=0
run_step 'Regression groups' lake env python3 scripts/run_tests.py "${regression_args[@]}" || test_status=$?
kernel_status=0
run_step 'Kernel replay' env LEAN_NUM_THREADS=2 lake env leanchecker --verbose ClaferCompiler Main tests || kernel_status=$?
if (( audit_status != 0 )); then exit "$audit_status"; fi
if (( test_status != 0 )); then exit "$test_status"; fi
if (( kernel_status != 0 )); then exit "$kernel_status"; fi
if [[ ${#regression_args[@]} == 0 ]]; then
  echo 'All build, native, import, kernel, axiom and regression gates passed.'
else
  echo 'Compiler CI passed; standalone reference corpora were not run in this profile.'
fi
