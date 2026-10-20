"""Mutate isolated source trees to exercise discovery and boundary failures."""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import project_modules as project


# [utest->req~compiler-build~1]
# [utest->req~compiler-boundaries~1]
class InventoryTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in ['lakefile.toml', 'lean-toolchain', 'ClaferCompiler.lean', 'Main.lean', 'tests.lean']:
            shutil.copyfile(ROOT / name, self.root / name)
        for name in ['ClaferCompiler', 'tests', 'scripts']:
            shutil.copytree(ROOT / name, self.root / name)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_unimported_owned_module_is_discovered_and_audited(self):
        self.write('ClaferCompiler/IR/Hidden.lean', 'def buildWitness := 1')
        modules = project.validate(self.root)
        self.assertIn('ClaferCompiler.IR.Hidden', modules)
        self.assertIn('import all ClaferCompiler.IR.Hidden', project.audit_source(self.root, modules))

    def test_unowned_modules_are_rejected(self):
        for path in ['Other.lean', 'ClaferCompiler/Unowned.lean', '.hidden/Hidden.lean',
                     'ClaferCompiler/Backend/Other.lean']:
            with self.subTest(path=path):
                self.write(path, 'def witness := 1')
                with self.assertRaisesRegex(ValueError, 'unowned'):
                    project.validate(self.root)
                (self.root / path).unlink()

    def test_runtime_cannot_reach_proof_or_upstream_imports(self):
        for dependency in ['Clafer', 'FormalCD', 'DPGraph', 'Mathlib',
                           'ClaferCompiler', 'ClaferCompiler.SemanticsBridge',
                           'ClaferCompiler.Correctness']:
            with self.subTest(dependency=dependency):
                self.write('ClaferCompiler/IR/Hidden.lean', f'import {dependency}\n')
                with self.assertRaisesRegex(ValueError, 'runtime imports'):
                    project.validate(self.root)

    def test_proof_escapes_rejected_even_with_warnings_disabled(self):
        for text in ['theorem bad : False := by sorry', 'example : False := by admit',
                     'private axiom bad : False', 'unsafe def bad := 0',
                     'partial def bad (n : Nat) : Nat := bad n']:
            with self.subTest(text=text):
                self.write('ClaferCompiler/Correctness/Hidden.lean',
                           'set_option warningAsError false\n' + text)
                with self.assertRaisesRegex(ValueError, 'prohibited'):
                    project.validate(self.root)

    def test_comments_and_strings_are_not_proof_escapes(self):
        self.write('ClaferCompiler/IR/Hidden.lean',
                   '/- sorry /- admit -/ -/\n-- unsafe\ndef text := "partial -- /- axiom"')
        project.validate(self.root)

    def test_cycles_and_missing_imports_fail(self):
        self.write('ClaferCompiler/IR/A.lean', 'import ClaferCompiler.IR.B')
        with self.assertRaisesRegex(ValueError, 'missing local import'):
            project.validate(self.root)
        self.write('ClaferCompiler/IR/B.lean', 'import ClaferCompiler.IR.A')
        with self.assertRaisesRegex(ValueError, 'import cycle'):
            project.validate(self.root)

    def test_missing_required_test_and_weakened_glob_fail(self):
        (self.root / 'tests/Upstream.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'missing required module'):
            project.validate(self.root)
        shutil.copyfile(ROOT / 'tests/Upstream.lean', self.root / 'tests/Upstream.lean')
        path = self.root / 'lakefile.toml'
        path.write_text(path.read_text().replace('"ClaferCompiler.**"', '"ClaferCompiler.IR"'))
        with self.assertRaisesRegex(ValueError, 'configuration differs'):
            project.validate(self.root)

    def test_symlinked_sources_and_directories_fail(self):
        link = self.root / 'ClaferCompiler/IR/Link.lean'
        link.parent.mkdir(exist_ok=True)
        link.symlink_to(ROOT / 'Main.lean')
        with self.assertRaisesRegex(ValueError, 'source symlink'):
            project.validate(self.root)
        link.unlink()
        link.parent.joinpath('Linked').symlink_to(ROOT / 'tests', target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'directory symlink'):
            project.validate(self.root)

    def test_import_parser_rejects_ambiguous_headers(self):
        for source in ['import Clafer Main', 'def x := 0\nimport Clafer',
                       'import\nClafer', '/- unterminated']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                project.imports(source)
        self.assertEqual(project.imports('/- /- nested -/ -/\nimport all Clafer'), ['Clafer'])
