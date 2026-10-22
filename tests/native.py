"""Build and run a temporary Lean entry point against explicit native modules."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run_native(test, modules, module, entry):
    """Keep fixture selection and output assertions in the calling test."""
    def run(*args):
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=45)
        test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    run("lake", "build", *(f"+{name}:c.o" for name in modules))
    with tempfile.TemporaryDirectory(prefix="clafer-native-") as tmp:
        directory = Path(tmp)
        harness = directory / "Harness.lean"
        harness.write_text(f"import {module}\ndef main : IO Unit := {entry}\n")
        c_file, binary = directory / "Harness.c", directory / "native-tests"
        run("lake", "env", "lean", f"--root={directory}", "-c", str(c_file), str(harness))
        objects = [f'.lake/build/ir/{name.replace(".", "/")}.c.o.export' for name in modules]
        run("lake", "env", "leanc", str(c_file), *objects, "-o", str(binary))
        return run(str(binary))
