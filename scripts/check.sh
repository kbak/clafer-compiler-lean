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
lake env lean -DwarningAsError=true .lake/validation/axiom_audit.lean
lake env python3 scripts/run_tests.py

# leanchecker loads each project's .olean and replays its kernel declarations.
# The recursive roots also include helpers not imported by the library root.
lake env leanchecker --verbose ClaferCompiler Main tests
echo 'All build, native, import, kernel, axiom and regression gates passed.'
