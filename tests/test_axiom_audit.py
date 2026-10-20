"""Run the actual Lean audit against isolated modules, including private names.

Run by `lake env python3 -m unittest discover -s tests`; fixtures never become
library sources. They use Lean's kernel and the production audit template.
"""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


TEMPLATE = (Path(__file__).resolve().parents[1] / "scripts/axiom_audit.lean").read_text()


# Adapted from clafer-semantics 1454e3bd (MIT, copyright 2026 Kacper Bak; see LICENSE).
# [utest->req~compiler-build~1]
class AxiomAuditTest(unittest.TestCase):
    def audit(self, body, *, root="ClaferCompiler", import_all=True, foreign=False):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            module = root + ".AuditFixture"
            source = path / root / "AuditFixture.lean"
            source.parent.mkdir()
            source.write_text("module\n" + body + "\n")
            env = dict(os.environ, LEAN_PATH=directory + os.pathsep + os.environ.get("LEAN_PATH", ""))
            if foreign:
                external = path / 'Foreign.lean'
                external.write_text('module\nnamespace Foreign\npublic axiom assumed : False\nend Foreign\n')
                result = subprocess.run(
                    ['lean', '--root=' + directory, '-o', str(external.with_suffix('.olean')), str(external)],
                    env=env, capture_output=True, text=True, check=False)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                source.write_text('module\nimport Foreign\n' + body + '\n')
            compiled = subprocess.run(
                ["lean", "-DwarningAsError=true", "--root=" + directory,
                 "-o", str(source.with_suffix(".olean")), str(source)],
                env=env, capture_output=True, text=True, check=False,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            audit = path / "Audit.lean"
            audit.write_text(TEMPLATE.replace("-- PROJECT_IMPORTS", "import " +
                                               ("all " if import_all else "") + module))
            return subprocess.run(["lean", "-DwarningAsError=true", str(audit)],
                                  env=env, capture_output=True, text=True, check=False)

    def test_private_and_generated_declarations_outside_namespace_are_counted(self):
        result = self.audit("namespace Unrelated\nprivate inductive Witness | point\nend Unrelated")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("New assumptions: none", result.stdout)
        self.assertNotIn("ClaferCompiler: 0 declarations", result.stdout)

    def test_new_axioms_in_every_root_are_rejected(self):
        for root in ["ClaferCompiler", "Main", "tests"]:
            with self.subTest(root=root):
                result = self.audit("private axiom forbidden : False", root=root)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("new project axiom", result.stdout)

    def test_unsafe_and_partial_declarations_are_rejected(self):
        for body in ["private unsafe def bad : Nat := 0",
                     "private partial def bad (n : Nat) : Nat := bad n"]:
            with self.subTest(body=body):
                result = self.audit(body)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unsafe or partial project declaration", result.stdout)

    def test_suppressed_sorry_warning_still_fails_axiom_audit(self):
        result = self.audit('set_option warningAsError false\nprivate theorem bad : False := by sorry')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('unapproved axiom sorryAx', result.stdout)

    def test_transitive_nonstandard_axiom_is_rejected(self):
        result = self.audit('private theorem bad : False := Foreign.assumed', foreign=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('unapproved axiom Foreign.assumed', result.stdout)

    def test_plain_import_cannot_hide_private_axiom(self):
        result = self.audit("private axiom forbidden : False", import_all=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit must import all", result.stdout)

    def test_empty_audit_is_rejected(self):
        result = self.audit("")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit found no project declarations", result.stdout)

    def test_upper_layer_declarations_cannot_satisfy_compiler_guard(self):
        result = self.audit("private def witness : Nat := 0", root="tests")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("audit found no ClaferCompiler declarations", result.stdout)


if __name__ == "__main__":
    unittest.main()
