"""Native source constraints and independent Analyzer fixtures/mutations."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts/oracles"))
import oracle
import project_modules


# [utest->req~compiler-expression-encoding~1]
# [utest->req~compiler-alloy-text~1]
class ExpressionEncodingTests(unittest.TestCase):
    def test_native_and_analyzer(self):
        api = oracle.adapters()
        config = os.environ.get("CLAFER_ORACLE_TOOLS")
        self.assertTrue(config, "CLAFER_ORACLE_TOOLS is required")
        _, _, runtime = oracle.load_tools(config, api)
        parent = oracle.external(os.environ.get("CLAFER_ORACLE_EVIDENCE", tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="expression-encoding-", dir=parent))
        print(f"Expression encoding evidence: {output}", flush=True)
        inventory = project_modules.inventory(ROOT)
        modules = set()

        def include(module):
            if module in modules or module not in inventory:
                return
            modules.add(module)
            for dependency in project_modules.imports((ROOT / inventory[module]).read_text()):
                include(dependency)

        include("tests.ExpressionEncodingNative")
        modules = sorted(modules)
        sources = [Path(__file__), ROOT / "scripts/project_modules.py",
                   ROOT / "scripts/oracles/AlloyArithmeticBridge.java",
                   ROOT / "scripts/oracles/AlloyTextBridge.java",
                   *[ROOT / inventory[m] for m in modules]]
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

        run("build-native", ["lake", "build", *["+" + m + ":c.o" for m in modules]], ROOT)
        harness = output / "Harness.lean"
        harness.write_text("import tests.ExpressionEncodingNative\n"
                           "def main (args : List String) : IO Unit := do\n"
                           "  let [directory] := args | throw (IO.userError \"directory required\")\n"
                           "  ClaferCompiler.Tests.ExpressionEncodingNative.run directory\n")
        c_file, binary = output / "Harness.c", output / "expression-tests"
        run("compile-native", ["lake", "env", "lean", f"--root={output}", "-c", str(c_file), str(harness)], ROOT)
        run("link-native", ["lake", "env", "leanc", str(c_file),
                            *[str(ROOT / ".lake/build/ir" / (m.replace(".", "/") + ".c.o.export"))
                              for m in modules], "-o", str(binary)], ROOT)
        self.assertEqual(run("native", [str(binary), str(output)]),
                         "35 source-constraint cases; 3 independent target cases; inherited attachments; overflow and scalar-payload mutations")
        expected = [True, False, True, True, True, False, True, True, True, True,
                    True, True, False, False, False, True, True, True, True, True,
                    True, True, True, True, True, False, True, True, True, True,
                    True, False, False, False, True, True, True, True]
        scalar = "((one cc0 and (one (cc0.cc3) and (-3 =< sum[cc0.cc3] and sum[cc0.cc3] =< 3))) implies sum[cc0.cc3] else -3)"
        references = {
            35: f"sig cc0 {{ cc3: one Int }}\nrun {{ {scalar} = 2 }} for 4 Int, exactly 1 cc0\n",
            36: f"sig cc0 {{ cc3: one Int }}\nrun {{ {scalar} = -3 }} for 4 Int, exactly 2 cc0\n",
            37: "sig cc0 {}\nrun { #(cc0 <: iden) = 2 } for 4 Int, exactly 2 cc0\n",
        }
        # These change independently known truth: comparison direction, lexical
        # capture, parent/dereference navigation, and masking undefined implication.
        replacements = {
            9: (" < ", " > "),
            25: ("( cc10 ) = ( cc6 )", "( cc10 ) = ( cc10 )"),
            28: ("( ~ ( cc1 ) )", "( cc5 )"),
            32: ("( one ", "( lone "),
        }
        manifest = []
        for index, truth in enumerate(expected):
            name = f"case_{index}"
            self.assertEqual((output / (name + ".truth")).read_text(), str(truth).lower())
            row = {"id": name, "expected": truth, "reference": index in references}
            if index in references:
                (output / (name + "-reference.als")).write_text(references[index])
            if index in replacements:
                original = (output / (name + ".als")).read_text()
                prefix, body = original.split("run {", 1)
                before, after = replacements[index]
                self.assertIn(before, body)
                (output / (name + "-mutated.als")).write_text(prefix + "run {" + body.replace(before, after))
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
        self.assertEqual([r["id"] for r in results], [r["id"] for r in manifest])
        self.assertEqual(sum("mutation" in r for r in results), len(replacements))
        for row in results:
            self.assertTrue(row["observation"]["options"]["noOverflow"])
            self.assertEqual(row["observation"]["options"]["solver"], "sat4j")
        self.assertEqual(identities, {str(p.relative_to(ROOT)): oracle.digest(p) for p in sources})
        oracle.write(output / "evidence-index.json", {
            str(p.relative_to(output)): oracle.digest(p)
            for p in sorted(output.rglob("*")) if p.is_file()})
