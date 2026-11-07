#!/usr/bin/env python3
"""Revision-specific build receipts; the historical temporal builder stays intact."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import tarfile

import oracle
from temporal_build import run_build

HERE = Path(__file__).resolve().parent
EXPORTER = HERE / 'PR113Export.hs'


def profile():
    return json.loads((HERE / 'pr113-profile.json').read_text())


def sources(work, *, extract=False):
    p = profile()
    archive, source = work / 'compiler.tar.gz', work / 'compiler'
    if oracle.digest(archive)['sha256'] != p['compiler_archive_sha256']:
        raise ValueError('Wrong PR113 compiler archive')
    originals = {}
    with tarfile.open(archive) as packed:
        for member in packed.getmembers():
            if not member.isfile():
                continue
            name = Path(member.name).relative_to('clafer-' + p['haskell_commit'])
            if name.is_absolute() or '..' in name.parts:
                raise ValueError('Unsafe archive member')
            data = packed.extractfile(member).read()
            originals[str(name)] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
            target = source / name
            if extract and not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
                target.chmod(member.mode)
            if not target.is_file() or target.read_bytes() != data:
                raise ValueError('Changed PR113 source: ' + str(name))
    encoded = (json.dumps(originals, sort_keys=True, separators=(',', ':')) + '\n').encode()
    if hashlib.sha256(encoded).hexdigest() != p['source_tree_sha256']:
        raise ValueError('Wrong PR113 source tree')
    if (source / 'stack.yaml.lock').exists() and oracle.digest(source / 'stack.yaml.lock') != p['stack_lock']:
        raise ValueError('Changed PR113 dependency lock')
    return originals


def recipe():
    return {p.name: oracle.digest(p) for p in
            (Path(__file__), HERE / 'temporal_build.py', EXPORTER, HERE / 'pr113-profile.json')}


def valid(work):
    try:
        b = json.loads((work / 'build.json').read_text())
        return (b['schema'] == 'clafer-pr113-build/1' and b['profile'] == profile()
            and b['recipe'] == recipe() and b['compiler_sources_unchanged'] is True
            and b['exporter_binary'] == oracle.digest(work / 'clafer-pr113-capture')
            and b['stack_lock'] == profile()['stack_lock']
            and oracle.digest(work / 'compiler/stack.yaml.lock') == b['stack_lock']
            and b['ghc'] == profile()['ghc'] and b['stack'] == profile()['stack']
            and os.access(work / 'clafer-pr113-capture', os.X_OK))
    except (OSError, ValueError, KeyError, TypeError):
        return False


# [impl->req~compiler-temporal-oracles~1]
def prepare(work, api):
    work = oracle.external(work)
    work.mkdir(parents=True, exist_ok=True)
    p = profile()
    with (work / 'build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if valid(work):
            sources(work)
            return work / 'build.json'
        if (platform.system(), platform.machine()) != ('Linux', 'x86_64'):
            raise RuntimeError('PR113 build requires Linux x86_64')
        runtime = api['runtime']
        runtime.download('https://codeload.github.com/gsdlab/clafer/tar.gz/' + p['haskell_commit'],
                         work / 'compiler.tar.gz', p['compiler_archive_sha256'])
        oracle.write(work / 'source-files.json', sources(work, extract=True))
        runtime.download('https://github.com/commercialhaskell/stack/releases/download/v3.11.1/stack-3.11.1-linux-x86_64.tar.gz',
                         work / 'stack.tar.gz', runtime.STACK_ARCHIVE)
        stack = work / 'stack'
        with tarfile.open(work / 'stack.tar.gz') as packed:
            stack.write_bytes(packed.extractfile('stack-3.11.1-linux-x86_64/stack').read())
        stack.chmod(0o755)
        if not runtime.matches(stack, runtime.STACK_BINARY):
            raise ValueError('Wrong Stack binary')
        env = dict(os.environ, STACK_ROOT=str(oracle.external(os.environ.get('STACK_ROOT', work / 'stack-root'))))
        obj = work / 'exporter-objects'
        obj.mkdir(exist_ok=True)
        commands = [[str(stack), 'build', 'clafer:lib'], [str(stack), 'exec', '--', 'ghc',
            '-package', 'clafer', '-package', 'aeson', '-Wall', '-fforce-recomp',
            '-outputdir', str(obj), str(EXPORTER), '-o', str(work / 'clafer-pr113-capture')]]
        (work / 'build.json').unlink(missing_ok=True)
        run_build(commands, work / 'compiler', env, work / 'build.log')
        sources(work)
        ghc = subprocess.check_output([str(stack), 'exec', '--', 'ghc', '--numeric-version'],
                                      cwd=work / 'compiler', env=env, text=True).strip()
        stack_version = subprocess.check_output([str(stack), '--numeric-version'], text=True).strip()
        oracle.write(work / 'build.json', dict(schema='clafer-pr113-build/1', profile=p,
            recipe=recipe(), compiler_sources_unchanged=True, ghc=ghc, stack=stack_version,
            stack_binary=oracle.digest(stack), stack_lock=oracle.digest(work / 'compiler/stack.yaml.lock'),
            exporter_binary=oracle.digest(work / 'clafer-pr113-capture'),
            commands=commands))
        if not valid(work):
            raise ValueError('PR113 build identity mismatch')
        return work / 'build.json'
