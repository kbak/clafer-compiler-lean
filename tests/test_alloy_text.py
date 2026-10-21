"""Exercise emitted bytes, independent Alloy ASTs, exact witnesses and mutations."""
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


# [utest->req~compiler-alloy-text~1]
class AlloyTextTests(unittest.TestCase):
    def test_text_roundtrip_maps_and_actual_analyzer(self):
        api = oracle.adapters()
        config = os.environ.get("CLAFER_ORACLE_TOOLS")
        self.assertTrue(config, "CLAFER_ORACLE_TOOLS is required")
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get("CLAFER_ORACLE_EVIDENCE", tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="alloy-text-", dir=parent))
        print(f"Alloy text evidence: {output}", flush=True)
        bridge = ROOT / "scripts/oracles/AlloyTextBridge.java"
        reference_file = ROOT / "tests/fixtures/alloy-text/references.json"
        sources = [bridge, reference_file, Path(__file__), ROOT / "tests/AlloyText.lean",
                   ROOT / "tests/AlloyTextOracle.lean",
                   *sorted((ROOT / "ClaferCompiler/Backend/Alloy").glob("*.lean"))]
        identities = {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources}
        for p in sources:
            destination = output / "source" / p.relative_to(ROOT)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(p.read_bytes())
        oracle.write(output / "source.json", identities)
        oracle.write(output / "runtime.json", runtime["identity"])
        env = api["alloy_runtime"].java_env()

        def run(name, command, cwd=output, timeout=40):
            oracle.write(output / (name + "-command.json"), command)
            with (output / (name + "-stdout.log")).open("w") as stdout, \
                    (output / (name + "-stderr.log")).open("w") as stderr:
                subprocess.run(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                               check=True, timeout=timeout)

        native_modules = ["ClaferCompiler.Backend.Alloy." + name for name in
                          ("Syntax", "Bounds", "Names", "Parse", "Print", "Semantics")]
        native_modules += ["tests." + name for name in ("AlloyCore", "AlloyText", "AlloyTextOracle")]
        run("build-native", ["lake", "build", *["+" + m + ":c.o" for m in native_modules]], cwd=ROOT)
        harness = output / "Harness.lean"
        harness.write_text("import tests.AlloyTextOracle\n"
                           "def main (args : List String) : IO Unit := "
                           "ClaferCompiler.Tests.AlloyTextOracle.run args\n")
        c_file, executable = output / "Harness.c", output / "alloy-text-tests"
        run("compile-native", ["lake", "env", "lean", f"--root={output}", "-c", str(c_file), str(harness)], cwd=ROOT)
        run("link-native", ["lake", "env", "leanc", str(c_file),
                           *[str(ROOT / ".lake/build/ir" / (m.replace(".", "/") + ".c.o.export"))
                             for m in native_modules], "-o", str(executable)], cwd=ROOT)
        run("lean", [str(executable), str(output)])
        self.assertEqual((output / "lean-stdout.log").read_text().strip(),
                         "192 target modules; 4000 names; 20 parser mutations")
        references = json.loads(reference_file.read_text())
        # Independently pin the complete four-atom candidate from AlloyCore.
        # This is test-only syntax, outside the serializer's input language.
        pin = "fact { some disj x,y: cc0 | some disj u,v: cc4 | cc1 = x->u + x->v + y->u }\n"
        manifest = []
        for i in range(192):
            name = f"case_{i}"
            path = output / (name + ".als")
            source = path.read_text()
            data = path.read_bytes()
            self.assertTrue(data.isascii())
            self.assertNotIn("//", source)
            self.assertNotIn("/*", source)
            mappings = [line.split("\t") for line in (output / (name + ".map")).read_text().splitlines()]
            self.assertEqual(len({m[0] for m in mappings}), len(mappings))
            for label, start, end in mappings:
                self.assertRegex(label, r"^cc[0-9]+$")
                self.assertEqual(data[int(start):int(end)].decode(), label)
                self.assertLess(int(start), int(end))
            row = {"id": name}
            if name in references:
                row["reference"] = True
                (output / (name + "-reference.als")).write_text(references[name])
            truth = output / (name + ".truth")
            if truth.exists():
                self.assertIn(truth.read_text(), ("true", "false"))
                row["expected"] = truth.read_text() == "true"
                # Insert the exact-candidate fact before the command.
                self.assertEqual(source.count("run {"), 1)
                (output / (name + "-pinned.als")).write_text(source.replace("run {", pin + "run {"))
            manifest.append(row)
        self.assertEqual(len(references), 36)
        self.assertEqual(sum("expected" in row for row in manifest), 26)
        # Grouping and alias mutations are deliberately valid Alloy, so merely
        # parsing successfully cannot make these checks pass.
        (output / "case_24-mutated.als").write_text(references["case_24"].replace(
            "cc0 - (cc0 - cc0)", "cc0 - cc0 - cc0"))
        (output / "case_25-mutated.als").write_text(references["case_25"].replace(
            "(cc0 + cc4).~cc1", "(cc0 + cc0).~cc1"))
        oracle.write(output / "manifest.json", manifest)
        run("javac", [str(runtime["java"].with_name("javac")), "--release", "17", "-cp",
                      str(runtime["jar"]), "-d", str(output), str(bridge)])
        run("analyzer", [str(runtime["java"]), "-Xmx512m", "-XX:ActiveProcessorCount=1",
                         "-XX:+UseSerialGC", "-cp", os.pathsep.join([str(output), str(runtime["jar"])]),
                         "AlloyTextBridge", str(output)])
        results = json.loads((output / "results.json").read_text())
        self.assertEqual([row["id"] for row in results], [row["id"] for row in manifest])
        self.assertEqual(sum(row.get("referenceMatched", False) for row in results), 36)
        observations = [row["observation"] for row in results if "observation" in row]
        self.assertEqual(len(observations), 26)
        self.assertTrue(any(row["satisfiable"] for row in observations))
        self.assertTrue(any(not row["satisfiable"] for row in observations))
        for observation in observations:
            self.assertEqual(observation["options"]["solver"], "sat4j")
            self.assertTrue(observation["options"]["noOverflow"])
        self.assertEqual(identities, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / "evidence-index.json", {
            str(p.relative_to(output)): oracle.digest(p)
            for p in sorted(output.rglob("*")) if p.is_file()})
