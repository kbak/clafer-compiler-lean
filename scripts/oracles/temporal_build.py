#!/usr/bin/env python3
"""Build the separate temporal exporter; caches and unsigned receipts stay external."""
import hashlib
import os
from pathlib import Path
import platform
import subprocess
import tarfile

import oracle

HERE = Path(__file__).resolve().parent


def profile():
    import json
    return json.loads((HERE / 'temporal-profile.json').read_text())


def sources(archive, source, *, extract=False):
    """Check exact archive bytes, including lockfile, before and after building."""
    p = profile()
    if oracle.digest(archive)['sha256'] != p['compiler_archive_sha256']:
        raise ValueError('Wrong temporal compiler archive')
    originals = {}
    with tarfile.open(archive) as packed:
        prefix = 'clafer-' + p['haskell_commit']
        for member in packed.getmembers():
            if not member.isfile():
                continue
            name = Path(member.name).relative_to(prefix)
            if '..' in name.parts:
                raise ValueError('Unsafe archive path')
            data = packed.extractfile(member).read()
            originals[str(name)] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
            target = source / name
            if target.exists():
                if target.read_bytes() != data:
                    raise ValueError('Modified compiler source: ' + str(name))
            else:
                if not extract:
                    raise ValueError('Missing compiler source: ' + str(name))
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                target.chmod(member.mode)
    # Match the existing upstream canonical encoding, not tar metadata.
    import json
    encoded = (json.dumps(originals, sort_keys=True, separators=(',', ':'), ensure_ascii=True) + '\n').encode()
    if hashlib.sha256(encoded).hexdigest() != p['source_tree_sha256']:
        raise ValueError('Wrong temporal source tree')
    return originals


def run_build(commands, source, env, log_path):
    with log_path.open('w') as log:
        try:
            for command in commands:
                subprocess.run(command, cwd=source, env=env, stdout=log,
                               stderr=subprocess.STDOUT, check=True, timeout=1800)
        except (OSError, subprocess.SubprocessError) as error:
            raise RuntimeError(f'Temporal exporter build failed; install GMP headers (libgmp-dev), '
                f'GHC/Stack prerequisites and inspect {log_path}; no Haskell gate skipped') from error


def valid(executable, receipt):
    import json
    try:
        b = json.loads(Path(receipt).read_text())
        return (b['schema'] == 'clafer-temporal-build/1' and b['profile'] == profile()
            and b['builder_source'] == oracle.digest(__file__)
            and b['exporter_source'] == oracle.digest(HERE / 'TemporalExport.hs')
            and b['exporter_binary'] == oracle.digest(executable)
            and b['compiler_sources_unchanged'] is True
            and b['stack_lock'] == profile()['stack_lock']
            and b['ghc'] == '9.6.7' and b['stack'] == '3.11.1'
            and os.access(executable, os.X_OK))
    except (OSError, ValueError, KeyError, TypeError):
        return False


# [impl->req~compiler-temporal-oracles~1]
def prepare(work, api):
    p = profile()
    work = oracle.external(work)
    work.mkdir(parents=True, exist_ok=True)
    executable, receipt = work / 'clafer-temporal-capture', work / 'build.json'
    import fcntl
    with (work / 'build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if valid(executable, receipt):
            sources(work / 'compiler.tar.gz', work / 'compiler')
            return executable, receipt
        if (platform.system(), platform.machine()) != ('Linux', 'x86_64'):
            raise RuntimeError('Temporal exporter build requires Linux x86_64')
        runtime = api['runtime']
        archive = work / 'compiler.tar.gz'
        runtime.download('https://codeload.github.com/gsdlab/clafer/tar.gz/' + p['haskell_commit'],
                         archive, p['compiler_archive_sha256'])
        source = work / 'compiler'
        originals = sources(archive, source, extract=True)
        oracle.write(work / 'source-files.json', originals)
        stack_archive, stack = work / 'stack.tar.gz', work / 'stack'
        runtime.download('https://github.com/commercialhaskell/stack/releases/download/v3.11.1/stack-3.11.1-linux-x86_64.tar.gz',
                         stack_archive, runtime.STACK_ARCHIVE)
        with tarfile.open(stack_archive) as packed:
            stack.write_bytes(packed.extractfile('stack-3.11.1-linux-x86_64/stack').read())
        stack.chmod(0o755)
        if not runtime.matches(stack, runtime.STACK_BINARY):
            raise ValueError('Wrong Stack binary')
        # Explicit external STACK_ROOT may reuse a matching installed compiler/package cache.
        env = dict(os.environ, STACK_ROOT=str(oracle.external(
            os.environ.get('STACK_ROOT', work / 'stack-root'))))
        obj = work / 'exporter-objects'
        obj.mkdir(exist_ok=True)
        commands = [[str(stack), 'build', 'clafer:lib'], [str(stack), 'exec', '--', 'ghc',
            '-package', 'clafer', '-package', 'aeson', '-Wall', '-fforce-recomp',
            '-outputdir', str(obj), str(HERE / 'TemporalExport.hs'), '-o', str(executable)]]
        receipt.unlink(missing_ok=True)
        run_build(commands, source, env, work / 'build.log')
        sources(archive, source)
        ghc = subprocess.check_output([str(stack), 'exec', '--', 'ghc', '--numeric-version'],
                                      cwd=source, env=env, text=True).strip()
        stack_version = subprocess.check_output([str(stack), '--numeric-version'], text=True).strip()
        b = dict(schema='clafer-temporal-build/1', profile=p, ghc=ghc, stack=stack_version,
            stack_lock=oracle.digest(source / 'stack.yaml.lock'), compiler_sources_unchanged=True,
            builder_source=oracle.digest(__file__), exporter_source=oracle.digest(HERE / 'TemporalExport.hs'),
            exporter_binary=oracle.digest(executable), stack_binary=oracle.digest(stack), commands=commands)
        oracle.write(receipt, b)
        if not valid(executable, receipt):
            raise ValueError('Temporal exporter build identity mismatch')
        return executable, receipt
