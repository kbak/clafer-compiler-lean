"""Compare kernel-checked target observations with independent static Alloy text."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/oracles"))
import oracle


# [utest->req~compiler-alloy-core~1]
# [utest->req~compiler-bounds~1]
class AlloyCoreTests(unittest.TestCase):
    def test_independent_truth_tables_in_actual_analyzer(self):
        api = oracle.adapters()
        tools = os.environ.get("CLAFER_ORACLE_TOOLS")
        if not tools:
            self.fail("CLAFER_ORACLE_TOOLS is required; missing tools cannot skip target checks")
        _, _, runtime = oracle.load_tools(tools, api)
        parent = oracle.external(os.environ.get("CLAFER_ORACLE_EVIDENCE", tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="alloy-core-", dir=parent))
        print(f"Alloy core evidence: {output}", flush=True)
        fixture = ROOT / "tests/fixtures/alloy-core/cases.json"
        bridge = ROOT / "scripts/oracles/AlloyCoreBridge.java"
        sources = [fixture, bridge, Path(__file__), ROOT / "tests/AlloyCore.lean",
                   ROOT / "tests/AlloyOracle.lean", *sorted((ROOT / "ClaferCompiler/Backend/Alloy").glob("*.lean"))]
        identity = {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources}
        cases = json.loads(fixture.read_text())
        self.assertTrue(cases)
        names = [item["id"] for item in cases]
        self.assertEqual(len(names), len(set(names)))
        (output / "cases.json").write_bytes(fixture.read_bytes())
        (output / "AlloyCoreBridge.java").write_bytes(bridge.read_bytes())
        oracle.write(output / "source.json", identity)
        oracle.write(output / "runtime.json", runtime["identity"])
        env = api["alloy_runtime"].java_env()

        def run(name, command, timeout=30, cwd=output):
            oracle.write(output / (name + "-command.json"), command)
            with (output / (name + "-stdout.log")).open("w") as stdout, \
                    (output / (name + "-stderr.log")).open("w") as stderr:
                subprocess.run(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                               check=True, timeout=timeout)

        run("javac", [str(runtime["java"].with_name("javac")), "--release", "17",
                      "-cp", str(runtime["jar"]), "-d", str(output), str(bridge)])
        run("analyzer", [str(runtime["java"]), "-Xmx512m", "-XX:ActiveProcessorCount=1",
                         "-XX:+UseSerialGC", "-cp", os.pathsep.join([str(output), str(runtime["jar"])]),
                         "AlloyCoreBridge", str(output / "cases.json")], timeout=40)
        run("lean", ["lake", "env", "lean", "tests/AlloyOracle.lean"], cwd=ROOT)
        observations = (output / "lean-stdout.log").read_text().splitlines()
        lean = {}
        for line in observations:
            name, value = line.split()
            self.assertNotIn(name, lean)
            self.assertIn(value, ("true", "false"))
            lean[name] = value == "true"
        actual = json.loads((output / "results.json").read_text())
        self.assertEqual(names, [row["id"] for row in actual])
        self.assertEqual(set(names), set(lean))
        for row in actual:
            with self.subTest(case=row["id"]):
                self.assertIs(type(row["satisfiable"]), bool)
                self.assertEqual(lean[row["id"]], row["satisfiable"])
                self.assertEqual("sat4j", row["options"]["solver"])
                self.assertTrue(row["options"]["noOverflow"])
                self.assertIn(row["bitwidth"], (2, 4))
        self.assertEqual(identity, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / "evidence-index.json", {
            str(p.relative_to(output)): oracle.digest(p)
            for p in sorted(output.rglob("*")) if p.is_file()})
