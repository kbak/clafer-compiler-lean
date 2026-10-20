#!/usr/bin/env bash
# Provision the committed dependency graph before the bounded check command.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONDONTWRITEBYTECODE=1
export LAKE_ARTIFACT_CACHE=false
export LAKE_RESTORE_ARTIFACTS=true
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

# Loading the workspace fetches missing packages from lake-manifest.json.
# It must not resolve new revisions with `lake update`.
lake env lean --version
python3 scripts/project_modules.py --dependencies
mapfile -t imports < <(python3 - <<'PY'
from pathlib import Path
from scripts.project_modules import imports
root = Path('.lake/packages/clafer')
paths = [p for name in ('DPGraph', 'FormalCD', 'Clafer')
         for p in [root / (name + '.lean'), *(root / name).rglob('*.lean')]]
print('\n'.join(sorted({dep for p in paths for dep in imports(p.read_text())
                       if dep.split('.')[0] == 'Mathlib'})))
PY
)
if (( ${#imports[@]} == 0 )); then
  echo 'Missing upstream Mathlib import inventory' >&2
  exit 1
fi
if ! lake exe cache get "${imports[@]}"; then
  echo 'Mathlib cache unavailable; building the pinned dependencies from source.' >&2
fi
lake build +Clafer
python3 scripts/project_modules.py --dependencies
