"""Live pinned tools plus rejection tests; all execution evidence is external."""
import copy
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/oracles"))
import oracle


# [utest->req~compiler-oracles~1]
class CheckerDependencyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.packages = self.root / ".lake/packages"
        self.upstream = self.packages / "clafer"
        self.mathlib = self.packages / "mathlib"
        self.mathlib.mkdir(parents=True)
        self.upstream.mkdir()
        # A real tiny Git dependency exercises identity/dirty checks without
        # cloning the actual Mathlib tree in every regression.
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.mathlib), *args], text=True).strip()
        git("init", "-q")
        git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null",
            "commit", "--allow-empty", "-qm", "Fixture dependency")
        oracle.write(self.root / "lake-manifest.json", dict(packages=[
            dict(name="clafer"), dict(name="mathlib", rev=git("rev-parse", "HEAD"))]))
        self.enterContext(patch.object(oracle, "ROOT", self.root))
        self.enterContext(patch.object(oracle, "UPSTREAM", self.upstream))
        # The existing dependency validator has its own integration coverage;
        # these tests isolate sharing only after that validator returns success.
        real_run = subprocess.run
        def run(command, *args, **kwargs):
            if str(self.root / "scripts/project_modules.py") in command:
                return subprocess.CompletedProcess(command, 0)
            return real_run(command, *args, **kwargs)
        self.validate = self.enterContext(patch.object(oracle.subprocess, "run", side_effect=run))

    def test_relative_shared_packages_survive_snapshot_copy(self):
        oracle.share_checker_dependencies()
        link = self.upstream / ".lake/packages/mathlib"
        self.assertTrue(link.is_symlink())
        self.assertFalse(Path(os.readlink(link)).is_absolute())
        self.assertEqual(self.mathlib, link.resolve())
        oracle.share_checker_dependencies()
        snapshot = self.root / "snapshot"
        shutil.copytree(self.packages, snapshot, symlinks=True)
        self.assertEqual(snapshot / "mathlib", (snapshot / "clafer/.lake/packages/mathlib").resolve())
        self.validate.assert_any_call([
            sys.executable, str(self.root / "scripts/project_modules.py"),
            "--repo", str(self.root), "--dependencies",
            "--output-dir", str(self.root / ".lake/validation")], check=True)

    def test_dirty_existing_dependency_is_rejected_and_preserved(self):
        oracle.share_checker_dependencies()
        marker = self.mathlib / "local-change"
        marker.write_text("preserve me")
        with self.assertRaisesRegex(ValueError, "Checker dependency differs"):
            oracle.share_checker_dependencies()
        self.assertEqual("preserve me", marker.read_text())

    def test_failed_validation_does_not_create_aliases(self):
        self.validate.side_effect = subprocess.CalledProcessError(1, "dependency-validation")
        with self.assertRaises(subprocess.CalledProcessError):
            oracle.share_checker_dependencies()
        self.assertFalse((self.upstream / ".lake").exists())

    def test_existing_checkout_at_wrong_revision_is_rejected(self):
        target = self.upstream / ".lake/packages/mathlib"
        target.parent.mkdir(parents=True)
        shutil.copytree(self.mathlib, target)
        subprocess.run(["git", "-C", str(target), "-c", "user.name=Fixture",
                        "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false",
                        "-c", "core.hooksPath=/dev/null", "commit", "--allow-empty", "-qm",
                        "Different revision"], check=True)
        with self.assertRaisesRegex(ValueError, "Checker dependency differs"):
            oracle.share_checker_dependencies()
        self.assertTrue(target.is_dir())
        self.assertFalse(target.is_symlink())


# [utest->req~compiler-oracles~1]
class OracleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.api = oracle.adapters()
        cls.p = cls.api["protocol"]
        # No download, implicit fallback, or missing-tool skip during the check.
        tools = os.environ.get("CLAFER_ORACLE_TOOLS")
        if not tools:
            raise RuntimeError("Prepare scripts/oracles/oracle.py tools and set CLAFER_ORACLE_TOOLS")
        cls.exporter, cls.build, cls.alloy = oracle.load_tools(tools, cls.api)
        parent = oracle.external(os.environ.get("CLAFER_ORACLE_EVIDENCE", tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix="oracles-", dir=parent))
        print(f"Oracle evidence: {cls.output}", flush=True)
        cls.source = oracle.source_identity()
        oracle.write(cls.output / "downstream-source.json", cls.source)
        cls.profile = cls.p.loads(oracle.PROFILE.read_bytes())
        corpus = cls.p.loads(oracle.CORPUS.read_bytes())
        if corpus["schema"] != "clafer-oracle-corpus/1" or corpus["semantics_commit"] != oracle.SEMANTICS:
            raise ValueError("Wrong corpus schema or semantics pin")
        cls.corpus = corpus["fixtures"]
        cls.captures = {}
        for item in cls.corpus:
            out = cls.output / item["id"]
            result = oracle.capture_case(oracle.fixture_path(item), item["bounds"], out,
                                         cls.api, cls.exporter, cls.build)
            cls.captures[item["id"]] = (out, result)

    @classmethod
    def tearDownClass(cls):
        cls.api["checker_runtime"].stop()
        oracle.write(cls.output / "evidence-index.json", {
            str(p.relative_to(cls.output)): oracle.digest(p)
            for p in sorted(cls.output.rglob("*")) if p.is_file()})
        if oracle.source_identity() != cls.source:
            raise RuntimeError("Oracle source changed during validation")

    def test_corpus_admission_and_unsupported_boundaries(self):
        for item in self.corpus:
            with self.subTest(fixture=item["id"]):
                _, result = self.captures[item["id"]]
                self.assertEqual(item["expected"], result["status"], result)
                if item["expected"] == "unsupported":
                    self.assertIsNone(result["checker"])
                    self.assertIsNone(result["solver"])
        self.assertEqual("abstract_fragment", self.captures["inherited-field"][1]["code"])
        self.assertEqual("type_metadata", self.captures["numeric"][1]["code"])
        self.assertIn("temporal modifier", self.captures["temporal"][1]["detail"])

    def test_live_exact_candidates_and_replay(self):
        # Identical, distinct bag heads reference one target. Set uniqueness
        # independently rejects this candidate; unrelated overlap also violates.
        candidate = oracle.UPSTREAM / "tests/fixtures/comparison/collapse_bag_heads.json"
        runs = [("bag", candidate, "agree_satisfies"),
                ("set", candidate, "agree_violates"),
                ("overlap", oracle.UPSTREAM / "tests/fixtures/comparison/unrelated-overlap.json",
                 "agree_violates")]
        for name, candidate_path, expected in runs:
            with self.subTest(fixture=name):
                out = self.output / (name + "-comparison")
                result = oracle.compare_case(self.captures[name][0] / "capture", candidate_path,
                                             out, self.api, self.alloy, self.profile["comparison"])
                self.assertTrue(oracle.comparison_ok(result), result)
                self.assertEqual(expected, result["category"], result)
                self.assertEqual(candidate_path.read_bytes(), (out / "candidate.json").read_bytes())
                solved = self.p.loads((out / "solver.json").read_bytes())
                self.assertEqual("sat4j", solved["options"]["solver"])
                for key, value in self.profile["options"].items():
                    self.assertEqual(value, solved["options"][key], key)
                self.assertEqual(dict(min=-1, max=-1), solved["static_trace"])
        replay = self.api["comparison"].replay(self.output / "bag-comparison",
                                               self.output / "bag-replay", runtime=self.alloy)
        self.assertTrue(oracle.comparison_ok(replay), replay)
        self.assertEqual("agree_satisfies", replay["category"])

    def test_every_capture_artifact_is_hash_bound(self):
        bundle = self.captures["bag"][0] / "capture"
        manifest = self.p.loads((bundle / "manifest.json").read_bytes())
        # Finite mutation domain: every raw artifact, including harmless whitespace.
        for name in manifest["inputs"]:
            with self.subTest(artifact=name):
                target = self.output / ("tampered-" + name)
                shutil.copytree(bundle, target)
                with (target / name).open("ab") as f:
                    f.write(b"\n")
                with self.assertRaisesRegex(self.p.Rejection, "artifact_hash"):
                    self.p.import_bundle(target)

    def test_receipt_pairing_backend_and_erased_source_checks(self):
        bundle = self.captures["bag"][0] / "capture"
        receipt = self.p.loads((bundle / "generation.json").read_bytes())
        for change, code in [(dict(backend="tmp.als"), "backend"),
                             (dict(json="{}"), "paired_output"),
                             (dict(alloy=receipt["alloy"] + "\n"), "paired_output")]:
            with self.subTest(change=list(change)):
                with self.assertRaisesRegex(self.p.Rejection, code):
                    self.p.validate_generation(dict(receipt, **change), (bundle / "input.cfr").read_bytes(),
                                               (bundle / "analyzed.json").read_bytes(),
                                               (bundle / "model.als").read_bytes())

    def test_actual_analyzer_rejects_temporal_model(self):
        out = self.output / "temporal-analyzer"
        out.mkdir()
        (out / "original.als").write_text("var sig A {}\npred show {}\nrun show for 1\n")
        (out / "comparison.als").write_text("var sig A {}\npred ib_candidate {}\nrun ib_candidate for 5\n")
        result = self.api["alloy_runtime"].solve(self.alloy, out, {})
        self.assertEqual("error", result["status"], result)
        self.assertIn("temporal", result["detail"])
        self.assertIsNone(result["outcome"])

    def test_actual_process_timeout_is_not_unsat(self):
        out = self.output / "timeout"
        out.mkdir()
        sleeper = out / "slow-java"
        sleeper.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(10)\n")
        sleeper.chmod(0o755)
        # A deliberately stalled process tests the adapter deadline, not SAT4J.
        runtime = dict(self.alloy, java=sleeper)
        result = self.api["alloy_runtime"].solve(runtime, out, {}, timeout=1)
        oracle.write(out / "observed.json", result)
        self.assertEqual("timeout", result["status"])
        self.assertIsNone(result["outcome"])
        self.assertEqual("inconclusive", self.api["comparison"].category("violates", result["outcome"], None))

    def test_missing_and_changed_tools_fail_without_fallback(self):
        tools = self.p.loads(Path(os.environ["CLAFER_ORACLE_TOOLS"]).read_bytes())
        for key in ("exporter", "build", "jar", "java_home"):
            with self.subTest(tool=key):
                bad = self.output / ("missing-" + key + ".json")
                oracle.write(bad, dict(tools, **{key: str(self.output / "nonexistent")}))
                with self.assertRaises((OSError, ValueError)):
                    oracle.load_tools(bad, self.api)
        changed = self.output / "changed-build.json"
        build = self.p.loads(self.build.read_bytes())
        oracle.write(changed, dict(build, compiler_commit="0" * 40))
        self.assertFalse(self.api["runtime"].valid_runtime(self.exporter, changed))
        # Restore the genuine explicit runtime after negative setup tests.
        oracle.load_tools(os.environ["CLAFER_ORACLE_TOOLS"], self.api)

    def test_insufficient_bitwidth_is_unsupported(self):
        result = oracle.compare_case(
            self.captures["bag"][0] / "capture",
            oracle.UPSTREAM / "tests/fixtures/comparison/collapse_bag_heads.json",
            self.output / "small-bitwidth", self.api, self.alloy,
            dict(self.profile["comparison"], bitwidth=1))
        self.assertEqual("unsupported", result["category"], result)
        self.assertIsNone(result["solver"])
        self.assertFalse(result["complete"])

    def test_disagreement_and_runtime_outcomes_are_not_success(self):
        c = self.api["comparison"]
        self.assertEqual("alloy_accepts_lean_rejects", c.category("violates", "sat", True))
        self.assertEqual("lean_accepts_alloy_rejects", c.category("satisfies", "unsat", None))
        for category in ("alloy_accepts_lean_rejects", "lean_accepts_alloy_rejects",
                         "unsupported", "inconclusive", "pin_decode_failure", "witness_unsat"):
            self.assertFalse(oracle.comparison_ok(dict(complete=True, category=category)))
        for outcome in ("timeout", "unknown", "error", "resource_limit", None):
            self.assertEqual("inconclusive", c.category("satisfies", outcome, None))

    def test_fixture_and_evidence_paths_fail_closed(self):
        for item in self.corpus:
            changed = copy.deepcopy(item)
            changed["identity"]["sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "Fixture identity"):
                oracle.fixture_path(changed)
        with self.assertRaisesRegex(ValueError, "outside"):
            oracle.external(ROOT / ".lake/oracle-output")

    def test_pins_match_provisioned_tools(self):
        profile = self.profile
        build = self.p.loads(self.build.read_bytes())
        self.assertEqual("clafer-oracle-profile/1", profile["schema"])
        self.assertEqual(oracle.SEMANTICS, profile["semantics_commit"])
        self.assertEqual(self.p.PIN, profile["haskell_commit"])
        self.assertEqual(self.api["alloy_runtime"].JAR_SHA, profile["alloy_jar_sha256"])
        for field, key in (("stack", "stack_version"), ("ghc", "ghc_version"), ("resolver", "resolver")):
            self.assertEqual(profile[field], build[key])

    def test_cli_retains_unsupported_and_missing_tool_failures(self):
        out = self.output / "cli-unsupported"
        bounds = self.captures["expression"][0] / "bounds.json"
        result = subprocess.run([
            sys.executable, str(ROOT / "scripts/oracles/oracle.py"), "capture",
            "--tools", os.environ["CLAFER_ORACLE_TOOLS"],
            str(ROOT / "tests/fixtures/oracles/expression.cfr"), "--bounds", str(bounds), str(out)],
            capture_output=True, timeout=30)
        self.assertEqual(1, result.returncode, result.stderr)
        self.assertEqual("unsupported", self.p.loads(result.stdout)["status"])
        self.assertEqual("unsupported", self.p.loads((out / "result.json").read_bytes())["status"])
        missing = subprocess.run([
            sys.executable, str(ROOT / "scripts/oracles/oracle.py"), "replay",
            "--tools", str(self.output / "absent-tools.json"), "unused", str(self.output / "unused")],
            capture_output=True, timeout=30)
        self.assertEqual(1, missing.returncode)
        self.assertEqual("error", self.p.loads(missing.stderr)["status"])
        self.assertEqual(b"", missing.stdout)


if __name__ == "__main__":
    unittest.main()
