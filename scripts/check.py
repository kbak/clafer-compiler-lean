#!/usr/bin/env python3
"""Validate scaffold syntax and documentation without claiming a compiler build."""
import ast
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit

root = Path(__file__).resolve().parents[1]
if (root / ".git").exists():
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root,
    ).decode().split("\0")
else:
    # IntentBond checks exported source snapshots without Git metadata.
    paths = [str(path.relative_to(root)) for path in root.rglob("*") if path.is_file()]
errors = []
for name in sorted(set(filter(None, paths))):
    path = root / name
    if not path.is_file():
        continue
    if path.suffix not in {".md", ".json", ".py", ".sh", ".yml", ".yaml", ".cff", ".txt"}:
        continue
    text = path.read_text()
    if re.search(r"^(?:<{7}|={7}|>{7})(?: |$)", text, re.M):
        errors.append(f"{name}: merge conflict marker")
    try:
        if path.suffix == ".json":
            json.loads(text)
        elif path.suffix == ".py":
            ast.parse(text, filename=name)
    except (ValueError, SyntaxError) as error:
        errors.append(f"{name}: {error}")
    if path.suffix == ".md":
        for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            if not (path.parent / unquote(url.path)).exists():
                errors.append(f"{name}: missing local link {target}")
if errors:
    raise SystemExit("\n".join(errors))
print("Scaffold syntax, local file links, and conflict-marker checks passed.")
print("No Lean build or compiler validation is configured yet.")
