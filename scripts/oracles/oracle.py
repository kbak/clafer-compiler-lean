#!/usr/bin/env python3
"""Reproduce the pinned external Haskell/Lean/Alloy comparison oracles.

Uses the MIT-licensed adapters in the pinned Clafer Semantics Lake dependency
(Copyright 2026 Kacper Bak). See docs/oracles.md for trust and replay boundaries.
"""
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[2]
SEMANTICS = "f25c5e4c01443614d4458a51878a3705f160694a"
UPSTREAM = ROOT / ".lake/packages/clafer"
PROFILE = ROOT / "scripts/oracles/profile.json"
CORPUS = ROOT / "tests/fixtures/oracles/inventory.json"


def digest(path):
    data = Path(path).read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def write(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def external(path):
    path = Path(path).resolve()
    if path.is_relative_to(ROOT):
        raise ValueError("Tool caches and evidence must be outside the repository")
    return path


def adapters():
    # Never load executable adapters from an unverified replacement dependency.
    command = ["git", "-C", str(UPSTREAM)]
    if subprocess.check_output(command + ["rev-parse", "HEAD"], text=True).strip() != SEMANTICS:
        raise ValueError("Wrong Clafer Semantics commit")
    if subprocess.check_output(command + ["status", "--porcelain", "--untracked-files=no"], text=True):
        raise ValueError("Modified Clafer Semantics sources")
    sys.path.insert(0, str(UPSTREAM / "scripts/verification"))
    return {name: importlib.import_module(name) for name in
            ("protocol", "runtime", "capture", "comparison", "alloy_runtime", "checker_runtime")}


def source_identity():
    paths = [PROFILE, CORPUS, Path(__file__)]
    paths += sorted((ROOT / "tests/fixtures/oracles").glob("*.cfr"))
    return {str(p.relative_to(ROOT)): digest(p) for p in paths}


def fixture_path(item):
    if item["origin"] not in ("semantics", "compiler"):
        raise ValueError("Unknown fixture origin")
    base = UPSTREAM if item["origin"] == "semantics" else ROOT
    path = (base / item["path"]).resolve()
    if not path.is_relative_to(base.resolve()) or digest(path) != item["identity"]:
        raise ValueError("Fixture identity mismatch: " + item["id"])
    return path


def share_checker_dependencies():
    """Reuse the checked transitive packages in the upstream Lake workspace."""
    subprocess.run([sys.executable, str(ROOT / "scripts/project_modules.py"),
                    "--repo", str(ROOT), "--dependencies",
                    "--output-dir", str(ROOT / ".lake/validation")], check=True)
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    destination = UPSTREAM / ".lake/packages"
    destination.mkdir(parents=True, exist_ok=True)
    for package in packages:
        if package["name"] == "clafer":
            continue
        target = destination / package["name"]
        if target.exists() or target.is_symlink():
            # Preserve an existing clean checkout, but do not bless a stale or
            # locally edited nested dependency just because the outer one passed.
            command = ["git", "-C", str(target)]
            revision = subprocess.check_output(command + ["rev-parse", "HEAD"], text=True).strip()
            dirty = subprocess.check_output(command + ["status", "--porcelain"], text=True)
            if revision != package["rev"] or dirty:
                raise ValueError("Checker dependency differs from pin: " + package["name"])
        else:
            # Relative links remain inside the copied dependency package tree in
            # IntentBond snapshots. Neither upstream sources nor manifests change.
            source = ROOT / ".lake/packages" / package["name"]
            target.symlink_to(os.path.relpath(source, destination), target_is_directory=True)


# [impl->req~compiler-oracles~1]
def prepare(output):
    """Provision outside the check deadline and retain notices/dependency inputs."""
    output = external(output)
    output.mkdir(parents=True, exist_ok=False)
    api = adapters()
    share_checker_dependencies()
    runtime, p = api["runtime"], api["protocol"]
    for name in ("CLAFER_CAPTURE_CACHE", "CLAFER_ALLOY_CACHE", "CLAFER_CAPTURE",
                 "CLAFER_CAPTURE_BUILD", "CLAFER_ALLOY_JAR", "CLAFER_JAVA_HOME"):
        if name in os.environ:
            external(os.environ[name])
    exporter, build = runtime.prepare()
    external(exporter)
    alloy = api["alloy_runtime"].prepare()
    external(alloy["jar"])
    archive = output / "compiler.tar.gz"
    runtime.download(f"https://codeload.github.com/gsdlab/clafer/tar.gz/{p.PIN}", archive, p.ARCHIVE)
    # Retain source dependency declarations and notices without vendoring code.
    with tarfile.open(archive) as packed:
        for name in ("LICENSE", "stack.yaml", "clafer.cabal", "src/Language/Clafer.hs"):
            destination = output / "haskell" / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(packed.extractfile(f"clafer-{p.PIN}/{name}").read())
    notices = {}
    with zipfile.ZipFile(alloy["jar"]) as jar:
        for name in jar.namelist():
            if (name.startswith("LICENSES/") and not name.endswith("/")) or name in (
                    "META-INF/LICENSE.txt", "META-INF/NOTICE.txt", "META-INF/MANIFEST.MF"):
                destination = output / "alloy" / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(jar.read(name))
                notices[name] = digest(destination)
    (output / "semantics-LICENSE").write_bytes((UPSTREAM / "LICENSE").read_bytes())
    (output / "haskell-build.json").write_bytes(build.read_bytes())
    subprocess.run(["lake", "build", "+Clafer.Verification.ImportMain"], cwd=UPSTREAM,
                   check=True, timeout=900)
    tools = dict(schema="clafer-oracle-tools/1", semantics=SEMANTICS,
                 exporter=str(exporter), build=str(build), jar=str(alloy["jar"]),
                 java_home=str(alloy["java"].parent.parent),
                 alloy_cache=str(alloy["classes"].parents[1]),
                 exporter_identity=digest(exporter), build_identity=digest(build),
                 alloy_identity=alloy["identity"], notices=notices,
                 compiler_archive=digest(archive))
    write(output / "tools.json", tools)
    write(output / "evidence-index.json", {
        str(path.relative_to(output)): digest(path)
        for path in sorted(output.rglob("*")) if path.is_file()})
    print(output / "tools.json")


def load_tools(path, api):
    p = api["protocol"]
    path = external(path)
    tools = p.loads(path.read_bytes())
    if tools["schema"] != "clafer-oracle-tools/1" or tools["semantics"] != SEMANTICS:
        raise ValueError("Wrong oracle tools schema or semantics pin")
    exporter, build = external(tools["exporter"]), external(tools["build"])
    if (digest(exporter) != tools["exporter_identity"] or digest(build) != tools["build_identity"]
            or not api["runtime"].valid_runtime(exporter, build)):
        raise ValueError("Exporter/build identity changed")
    os.environ.update(CLAFER_ALLOY_JAR=str(external(tools["jar"])),
                      CLAFER_JAVA_HOME=str(external(tools["java_home"])),
                      CLAFER_ALLOY_CACHE=tempfile.mkdtemp(prefix="bridge-run-",
                          dir=external(tools["alloy_cache"])))
    # Compile the pinned bridge into a private build directory. Concurrent suites
    # must never overwrite a class file another JVM is loading. The immutable
    # JAR/JDK are shared; compiled bridge identity is still checked below.
    alloy = api["alloy_runtime"].prepare()
    if alloy["identity"] != tools["alloy_identity"]:
        raise ValueError("Alloy/Java runtime identity changed; provision again")
    return exporter, build, alloy


def capture_case(source, bounds, output, api, exporter, build):
    """Retain rejected inputs too; only successful admission can reach comparison."""
    output = external(output)
    output.mkdir(parents=True, exist_ok=False)
    source = Path(source)
    (output / "input.cfr").write_bytes(source.read_bytes())
    write(output / "bounds.json", bounds)
    result = dict(status="error", checker=None, solver=None,
                  source=digest(output / "input.cfr"), bounds=digest(output / "bounds.json"),
                  exporter=digest(exporter), build=digest(build), semantics=SEMANTICS)
    try:
        core, metadata = api["capture"].capture(output / "input.cfr", exporter, build,
                                                bounds, output / "capture")
        verdict, identity = api["checker_runtime"].execute(
            core, None, api["comparison"].source_snapshot())
        write(output / "checker-runtime.json", identity)
        result.update(status=verdict["status"], checker=verdict, metadata=metadata)
    except api["protocol"].Rejection as error:
        result.update(error.result())
    except (subprocess.TimeoutExpired, TimeoutError) as error:
        result.update(status="timeout", detail=str(error))
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        result.update(status="error", detail=str(error))
    write(output / "result.json", result)
    return result


def comparison_ok(result):
    # Completed discrepancies are evidence of disagreement, never passing tests.
    return result["complete"] and result["category"] in ("agree_satisfies", "agree_violates")


def compare_case(bundle, candidate, output, api, alloy, profile):
    return api["comparison"].compare(bundle, None, external(output), runtime=alloy,
                                    candidate_bytes=Path(candidate).read_bytes(), **profile)


def parser():
    cli = argparse.ArgumentParser(description=__doc__)
    sub = cli.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare", help="Provision external tools and license records")
    prep.add_argument("output", type=Path)
    for name in ("capture", "compare", "replay"):
        command = sub.add_parser(name)
        command.add_argument("--tools", required=True, type=Path)
        if name == "capture":
            command.add_argument("source", type=Path)
            command.add_argument("--bounds", required=True, type=Path)
        else:
            command.add_argument("input", type=Path)
        if name == "compare":
            command.add_argument("candidate", type=Path)
        command.add_argument("output", type=Path)
    return cli


def main():
    args = parser().parse_args()
    if args.command == "prepare":
        prepare(args.output)
        return 0
    api = adapters()
    exporter, build, alloy = load_tools(args.tools, api)
    profile = api["protocol"].loads(PROFILE.read_bytes())["comparison"]
    if args.command == "capture":
        result = capture_case(args.source, api["protocol"].loads(args.bounds.read_bytes()),
                              args.output, api, exporter, build)
        ok = result["status"] == "admitted"
    elif args.command == "compare":
        result = compare_case(args.input, args.candidate, args.output, api, alloy, profile)
        ok = comparison_ok(result)
    else:
        result = api["comparison"].replay(args.input, external(args.output), runtime=alloy)
        ok = comparison_ok(result)
    write(args.output / "downstream-source.json", source_identity())
    print(json.dumps(result, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps(dict(status="error", detail=str(error))), file=sys.stderr)
        raise SystemExit(1)
