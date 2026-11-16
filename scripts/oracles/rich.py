"""Pinned rich/core CLI qualification, separate from every historical exporter."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

import oracle
from temporal_build import run_build

HERE = Path(__file__).resolve().parent
PROFILE = HERE / 'rich-profile.json'


def profile():
    return json.loads(PROFILE.read_text())


def recipe():
    return {p.name: oracle.digest(p) for p in (Path(__file__), PROFILE, HERE/'temporal_build.py')}


def sources(work, extract=False):
    p = profile()
    archive = work / 'compiler.tar.gz'
    if oracle.digest(archive)['sha256'] != p['compiler_archive_sha256']:
        raise ValueError('wrong rich/core source archive')
    rows = {}
    with tarfile.open(archive) as packed:
        for member in packed.getmembers():
            if not member.isfile(): continue
            name = Path(member.name).relative_to('clafer-' + p['haskell_commit'])
            if name.is_absolute() or '..' in name.parts: raise ValueError('unsafe archive member')
            data = packed.extractfile(member).read()
            target = work / name
            if extract and not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                target.chmod(member.mode)
            if not target.is_file() or target.read_bytes() != data:
                raise ValueError('changed rich/core source: ' + str(name))
            rows[str(name)] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
    tree = (json.dumps(rows, sort_keys=True, separators=(',', ':')) + '\n').encode()
    if hashlib.sha256(tree).hexdigest() != p['source_tree_sha256']:
        raise ValueError('wrong rich/core source tree')
    return rows


def valid(work):
    try:
        receipt = json.loads((work/'rich-build.json').read_text())
        return (receipt['schema'] == 'clafer-rich-build/1' and receipt['profile'] == profile()
                and receipt['recipe'] == recipe() and receipt['binary'] == oracle.digest(work/'rich-clafer')
                and receipt['ghc'] == profile()['ghc'] and receipt['stack'] == profile()['stack']
                and receipt['stack_lock'] == oracle.digest(work/'stack.yaml.lock') == profile()['stack_lock'])
    except (KeyError, ValueError, OSError):
        return False


# [impl->req~compiler-rich-core-explicit~1]
def prepare(work, output):
    import fcntl
    work, output = oracle.external(work), oracle.external(output)
    work.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=False)
    runtime = oracle.adapters()['runtime']
    p = profile()
    with (work/'rich-build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        runtime.download('https://codeload.github.com/gsdlab/clafer/tar.gz/' + p['haskell_commit'],
                         work/'compiler.tar.gz', p['compiler_archive_sha256'])
        sources(work, extract=True)
        if not valid(work):
            runtime.download('https://github.com/commercialhaskell/stack/releases/download/v3.11.1/stack-3.11.1-linux-x86_64.tar.gz',
                             work/'rich-stack.tar.gz', runtime.STACK_ARCHIVE)
            stack = work/'rich-stack'
            with tarfile.open(work/'rich-stack.tar.gz') as archive:
                stack.write_bytes(archive.extractfile('stack-3.11.1-linux-x86_64/stack').read())
            stack.chmod(0o755)
            if not runtime.matches(stack, runtime.STACK_BINARY): raise ValueError('wrong Stack binary')
            env = dict(os.environ, STACK_ROOT=str(oracle.external(os.environ.get('STACK_ROOT', work/'rich-stack-root'))))
            run_build([[str(stack), 'build', 'clafer:exe:clafer']], work, env, work/'rich-build.log')
            install = Path(subprocess.check_output([str(stack), 'path', '--local-install-root'], cwd=work, env=env, text=True).strip())
            shutil.copyfile(install/'bin/clafer', work/'rich-clafer')
            (work/'rich-clafer').chmod(0o755)
            ghc = subprocess.check_output([str(stack), 'exec', '--', 'ghc', '--numeric-version'], cwd=work, env=env, text=True).strip()
            stack_version = subprocess.check_output([str(stack), '--numeric-version'], text=True).strip()
            sources(work)
            oracle.write(work/'rich-build.json', dict(schema='clafer-rich-build/1', profile=p,
                recipe=recipe(), binary=oracle.digest(work/'rich-clafer'), ghc=ghc, stack=stack_version,
                stack_lock=oracle.digest(work/'stack.yaml.lock')))
            if not valid(work): raise ValueError('rich/core build identity mismatch')
        for name in ('LICENSE', 'stack.yaml', 'stack.yaml.lock', 'clafer.cabal'):
            shutil.copyfile(work/name, output/name)
        oracle.write(output/'tools.json', dict(schema='clafer-rich-tools/1', profile=p,
            build=str(work/'rich-build.json'), identity=oracle.digest(work/'rich-build.json')))
    return output/'tools.json'


def load_tools(path):
    tools = json.loads(oracle.external(path).read_text())
    work = oracle.external(tools['build']).parent
    if (set(tools) != {'schema', 'profile', 'build', 'identity'} or
            tools['schema'] != 'clafer-rich-tools/1' or tools['profile'] != profile() or
            tools['identity'] != oracle.digest(work/'rich-build.json') or not valid(work)):
        raise ValueError('rich/core tools identity mismatch')
    sources(work)
    return work/'rich-clafer'


def capture(binary, directory, source, *, core=False, mode='clafer'):
    directory.mkdir(parents=True, exist_ok=False)
    (directory/'model.cfr').write_text(source)
    command = [str(binary), '--console-output', '--no-stats', '--keep-unused', '-m', mode,
               *(['--core'] if core else []), 'model.cfr']
    result = subprocess.run(command, cwd=directory, capture_output=True, timeout=30)
    (directory/'stdout').write_bytes(result.stdout)
    (directory/'stderr').write_bytes(result.stderr)
    oracle.write(directory/'request.json', dict(profile=profile(), command=command,
        binary=oracle.digest(binary), source=oracle.digest(directory/'model.cfr'), returncode=result.returncode))
    if result.returncode: raise ValueError('rich/core candidate rejected model: '+result.stderr.decode())
    return result.stdout.decode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-cache', required=True)
    parser.add_argument('output')
    args = parser.parse_args()
    print(prepare(args.build_cache, args.output))
