"""Native arithmetic, independent Alloy ASTs, and non-vacuous operand mutations."""
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


# [utest->req~compiler-target-arithmetic~1]
# [utest->req~compiler-alloy-text~1]
class IntegerArithmeticTests(unittest.TestCase):
    def test_native_and_real_analyzer(self):
        api = oracle.adapters()
        config = os.environ.get("CLAFER_ORACLE_TOOLS")
        self.assertTrue(config, "CLAFER_ORACLE_TOOLS is required")
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get("CLAFER_ORACLE_EVIDENCE", tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="alloy-arithmetic-", dir=parent))
        print(f"Alloy arithmetic evidence: {output}", flush=True)
        sources = [Path(__file__), ROOT / "tests/IntegerArithmeticNative.lean",
                   ROOT / "tests/IntegerArithmetic.lean",
                   ROOT / "scripts/oracles/AlloyArithmeticBridge.java",
                   ROOT / "scripts/oracles/AlloyTextBridge.java",
                   ROOT / "ClaferCompiler/Correctness/IntegerArithmetic.lean",
                   *sorted((ROOT / "ClaferCompiler/Backend/Alloy").glob("*.lean"))]
        identities = {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources}
        for p in sources:
            dest = output / "source" / p.relative_to(ROOT)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(p.read_bytes())
        oracle.write(output / "source.json", identities)
        oracle.write(output / "runtime.json", runtime["identity"])
        env = api["alloy_runtime"].java_env()

        def run(name, command, cwd=output):
            oracle.write(output / (name + "-command.json"), command)
            result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                    capture_output=True, timeout=45)
            (output / (name + "-stdout.log")).write_text(result.stdout)
            (output / (name + "-stderr.log")).write_text(result.stderr)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result.stdout.strip()

        modules = ["ClaferCompiler.Backend.Alloy." + name for name in
                   ("Syntax", "Bounds", "Names", "Parse", "Print", "Semantics")]
        modules.append("tests.IntegerArithmeticNative")
        run("build-native", ["lake", "build", *["+" + m + ":c.o" for m in modules]], ROOT)
        harness = output / "Harness.lean"
        harness.write_text("import tests.IntegerArithmeticNative\n"
                           "def main (args : List String) : IO Unit := do\n"
                           "  let [directory] := args | throw (IO.userError \"directory required\")\n"
                           "  ClaferCompiler.Tests.IntegerArithmeticNative.run directory\n")
        c_file, binary = output / "Harness.c", output / "arithmetic-tests"
        run("compile-native", ["lake", "env", "lean", f"--root={output}", "-c", str(c_file), str(harness)], ROOT)
        run("link-native", ["lake", "env", "leanc", str(c_file),
                            *[str(ROOT / ".lake/build/ir" / (m.replace(".", "/") + ".c.o.export"))
                              for m in modules], "-o", str(binary)], ROOT)
        self.assertEqual(run("native", [str(binary), str(output)]),
                         "2372 arithmetic boundaries; 20 serialized cases")

        # Independently authored formulas preserve the full AST; do not derive
        # expected syntax or truth from the printer under test.
        expressions = [
            "plus[2,3] = 5", "minus[2,5] = -3", "minus[5,2] = -3",
            "minus[2,5] < 0", "0 < minus[2,5]", "plus[minus[2,5],4] = 1",
            "minus[0,7] = -7", "plus[-8,0] = -8", "minus[7,0] = 7",
            "plus[-1,0] = -1", "(some none) implies minus[2,5] = 0",
            "not (minus[2,5] = 0)", "minus[5,minus[2,1]] = 4",
            "minus[minus[5,2],1] = 4", "minus[-32767,1] = -32768",
            "plus[32766,1] = 32767", "plus[#cc0,2] = 5",
            "minus[2,#cc0] = -1", "all x: cc0 | plus[#x,2] = 3",
            "minus[#cc1,#cc0] = 2",
        ]
        expected = [True, True, False, True, False, True, True, True, True, True,
                    True, True, True, False, True, True, True, True, True, True]
        mutations = {1: "minus[5,2] = -3", 3: "0 < minus[2,5]",
                     12: "minus[minus[5,2],1] = 4", 17: "minus[#cc0,2] = -1",
                     18: "all x: cc0 | plus[#cc0,2] = 3"}
        manifest = []
        for index, expr in enumerate(expressions):
            name = f"case_{index}"
            width = 1 if index == 9 else 16 if index in (14, 15) else 4
            declarations, scopes = "", ""
            if 16 <= index <= 18:
                count = 2 if index == 18 else 3
                declarations, scopes = "sig cc0 {}\n", f", exactly {count} cc0"
            if index == 19:
                declarations = "sig cc0 {cc1: set cc4}\nsig cc4 {}\nfact { cc1 = cc0 -> cc4 }\n"
                scopes = ", exactly 2 cc0, exactly 2 cc4"
            reference = f"{declarations}run {{ {expr} }} for {width} Int{scopes}\n"
            (output / (name + "-reference.als")).write_text(reference)
            self.assertEqual((output / (name + ".truth")).read_text(), str(expected[index]).lower())
            row = {"id": name, "expected": expected[index]}
            if width == 16:
                row["expectedToolError"] = "translation-capacity"
            if index in mutations:
                (output / (name + "-mutated.als")).write_text(reference.replace(expr, mutations[index]))
                row["mutation"] = True
            manifest.append(row)
        oracle.write(output / "manifest.json", manifest)
        run("javac", [str(runtime["java"].with_name("javac")), "--release", "17", "-cp",
                      str(runtime["jar"]), "-d", str(output),
                      str(ROOT / "scripts/oracles/AlloyTextBridge.java"),
                      str(ROOT / "scripts/oracles/AlloyArithmeticBridge.java")])
        run("analyzer", [str(runtime["java"]), "-Xmx512m", "-XX:ActiveProcessorCount=1",
                         "-XX:+UseSerialGC", "-cp", os.pathsep.join([str(output), str(runtime["jar"])]),
                         "AlloyArithmeticBridge", str(output)])
        results = json.loads((output / "results.json").read_text())
        self.assertEqual([row["id"] for row in results], [row["id"] for row in manifest])
        self.assertEqual(sum("mutation" in row for row in results), len(mutations))
        self.assertEqual([r["id"] for r in results if "toolError" in r], ["case_14", "case_15"])
        for row in results:
            options = json.loads((output / (row["id"] + "-options.json")).read_text())
            self.assertTrue(options["noOverflow"])
            self.assertEqual(options["solver"], "sat4j")
            if "toolError" in row:
                self.assertNotIn("observation", row)
                self.assertIn("Translation capacity exceeded", row["toolError"])
                continue
            self.assertEqual(options, row["observation"]["options"])
            self.assertTrue(row["observation"]["options"]["noOverflow"])
            self.assertEqual(row["observation"]["options"]["solver"], "sat4j")
        self.assertEqual(identities, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / "evidence-index.json", {
            str(p.relative_to(output)): oracle.digest(p)
            for p in sorted(output.rglob("*")) if p.is_file()})
