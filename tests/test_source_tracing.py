"""Guard the pinned checker's import of real Lean source annotations."""

from pathlib import Path
import tempfile
import unittest

from intentbond.oft import default_jar, export_items, validate_jar
from intentbond.snapshot import Snapshot

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'ClaferCompiler/Correctness/StructuralCorrectness.lean'


class LeanSourceTracingTests(unittest.TestCase):
    def test_pinned_checker_retains_real_lean_artifacts_and_locations(self):
        # [utest->req~intentbond-workflow~1]
        source = (ROOT / SOURCE).read_bytes()
        with tempfile.TemporaryDirectory(prefix="clafer-source-trace-") as temporary:
            root = Path(temporary)
            path = root / SOURCE
            path.parent.mkdir(parents=True)
            path.write_bytes(source)
            output = root / "evidence"
            output.mkdir()
            snapshot = Snapshot(root, "source-import-regression", "worktree",
                                [{"path": SOURCE, "mode": "100644"}])
            jar = default_jar()
            validate_jar(jar)
            items, result, _ = export_items(snapshot, [SOURCE], jar, "java", output, "source")
            self.assertEqual(result["status"], "passed")
            self.assertTrue({'proof'} <= {item["type"] for item in items})
            lines = source.decode().splitlines()
            for item in items:
                self.assertEqual(item["path"], SOURCE)
                self.assertGreater(item["line"], 0)
                self.assertLessEqual(item["line"], len(lines))
                self.assertIn("[" + item["type"] + "->req~", lines[item["line"] - 1])
            self.assertEqual(path.read_bytes(), source)


if __name__ == "__main__":
    unittest.main()
