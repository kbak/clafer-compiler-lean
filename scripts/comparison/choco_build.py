"""Provision the pinned Choco and explicit-export adapters outside source."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'oracles'))
import oracle

HERE = Path(__file__).resolve().parent
PIN = '253b1de60e4d87435874db81a5151dca53ee1871'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sources():
    return {p.name: oracle.digest(p) for p in
            (Path(__file__), HERE/'ExplicitExport.hs', HERE/'ChocoInstances.java')}


def java_identity(home):
    home = oracle.external(home)
    version = subprocess.check_output([home/'bin/java', '-version'], stderr=subprocess.STDOUT,
                                      text=True, timeout=10)
    require('version "21.' in version, 'Choco requires Java 21')
    return dict(version=version, java=oracle.digest(home/'bin/java'),
                javac=oracle.digest(home/'bin/javac'), modules=oracle.digest(home/'lib/modules'))


def checked_source(source):
    command = ['git', '-C', str(source)]
    require(subprocess.check_output(command+['rev-parse', 'HEAD'], text=True).strip() == PIN,
            'Wrong Choco source revision')
    require(not subprocess.check_output(command+['status', '--porcelain', '--untracked-files=no'], text=True),
            'Modified Choco sources')
    return {n: oracle.digest(source/n) for n in subprocess.check_output(
        command+['ls-files', '-z'], text=True).split('\0') if n}


def run(command, output, name, **kwargs):
    oracle.write(output/(name+'-command.json'), list(map(str, command)))
    with (output/(name+'.log')).open('w') as log:
        subprocess.run(list(map(str, command)), stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=1800, **kwargs)


# [impl->req~compiler-choco-instances~1]
def prepare(static_tools, capture_cache, choco_source, java_home, maven, maven_cache, output):
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    api = oracle.adapters()
    cache = oracle.external(capture_cache)
    source = oracle.external(choco_source)
    java_home = oracle.external(java_home)
    static = api['protocol'].loads(Path(static_tools).read_bytes())
    require(api['runtime'].valid_runtime(Path(static['exporter']), Path(static['build'])), 'Invalid static exporter')
    # Cached binaries alone need not include the library needed by this companion.
    # Build a missing library in a separate cache: the upstream builder also
    # emits a capture executable, which must not replace the accepted receipt.
    if not (cache/'compiler/.stack-work').exists():
        original = cache
        cache = output/'capture-library'
        cache.mkdir()
        for name in ('compiler.tar.gz', 'stack.tar.gz', 'stack'):
            if (original/name).is_file(): shutil.copyfile(original/name, cache/name)
        if (original/'stack-root').is_dir():
            (cache/'stack-root').symlink_to(original/'stack-root', target_is_directory=True)
        r, p = api['runtime'], api['protocol']
        r.download(f'https://codeload.github.com/gsdlab/clafer/tar.gz/{p.PIN}',
                   cache/'compiler.tar.gz', p.ARCHIVE)
        r.download('https://github.com/commercialhaskell/stack/releases/download/v3.11.1/'
                   'stack-3.11.1-linux-x86_64.tar.gz', cache/'stack.tar.gz', r.STACK_ARCHIVE)
        if not r.matches(cache/'stack', r.STACK_BINARY):
            with tarfile.open(cache/'stack.tar.gz') as packed:
                (cache/'stack').write_bytes(packed.extractfile('stack-3.11.1-linux-x86_64/stack').read())
        (cache/'stack').chmod(0o755)
        require(r.matches(cache/'stack', r.STACK_BINARY), 'Wrong Stack binary')
        run([sys.executable, oracle.UPSTREAM/'scripts/verification/build.py',
             '--archive', cache/'compiler.tar.gz', '--stack', cache/'stack', '--work', cache],
            output, 'static-library')
    require(oracle.digest(static['exporter']) == static['exporter_identity']
            and oracle.digest(static['build']) == static['build_identity'], 'Static tools changed during setup')
    require(api['runtime'].valid_runtime(cache/'clafer-capture', cache/'build.json'), 'Invalid capture cache')
    require(oracle.digest(cache/'compiler.tar.gz')['sha256'] == api['protocol'].ARCHIVE,
            'Wrong Haskell archive')
    with tarfile.open(cache/'compiler.tar.gz') as packed:
        for member in packed.getmembers():
            if member.isfile():
                name = Path(*Path(member.name).parts[1:])
                require((cache/'compiler'/name).read_bytes() == packed.extractfile(member).read(),
                        'Modified Haskell source: '+str(name))
    before = checked_source(source)
    identity = java_identity(java_home)
    env = dict(os.environ, JAVA_HOME=str(java_home),
               PATH=str(java_home/'bin')+os.pathsep+os.environ['PATH'])
    run([maven, '-B', '-Dmaven.repo.local='+str(oracle.external(maven_cache)),
         '-DskipTests', 'clean', 'package', 'org.apache.maven.plugins:maven-dependency-plugin:3.8.1:copy-dependencies',
         '-DincludeScope=runtime', '-DoutputDirectory='+str(output/'dependencies')],
        output, 'choco-build', cwd=source, env=env)
    require(checked_source(source) == before, 'Choco sources changed during build')
    jar = output/'chocosolver.jar'
    shutil.copyfile(source/'target/chocosolver-0.5.7-jar-with-dependencies.jar', jar)
    (output/'classes').mkdir()
    run([java_home/'bin/javac', '--release', '21', '-cp', jar, '-d', output/'classes',
         HERE/'ChocoInstances.java'], output, 'bridge-build')
    # Import the unmodified upstream module by its declared name; its private
    # observer is the same checked library observation used by static capture.
    shutil.copyfile(oracle.UPSTREAM/'scripts/verification'/api['runtime'].current.EXPORTER, output/'Main.hs')
    shutil.copyfile(cache/'Observer.hs', output/'Observer.hs')
    env = dict(os.environ, STACK_ROOT=str(cache/'stack-root'))
    run([cache/'stack', 'exec', '--', 'ghc', '-package', 'clafer', '-package', 'aeson',
         '-package', 'data-stringmap', '-i'+str(output), '-outputdir', output/'objects',
         '-main-is', 'ExplicitExport', HERE/'ExplicitExport.hs', '-o', output/'explicit-export'],
        output, 'explicit-build', cwd=cache/'compiler', env=env)
    notices = output/'notices'
    notices.mkdir()
    shutil.copyfile(source/'LICENSE', notices/'choco-LICENSE')
    shutil.copyfile(source/'pom.xml', notices/'choco-pom.xml')
    shutil.copyfile(cache/'compiler/LICENSE', notices/'haskell-LICENSE')
    shutil.copyfile(oracle.UPSTREAM/'LICENSE', notices/'semantics-LICENSE')
    for dependency in (output/'dependencies').glob('*.jar'):
        with zipfile.ZipFile(dependency) as archive:
            for name in archive.namelist():
                path = Path(name)
                if name.endswith('/') or path.is_absolute() or '..' in path.parts:
                    continue
                if any(word in name.upper() for word in ('LICENSE', 'NOTICE', 'COPYING')) or name.endswith('pom.xml'):
                    target = notices/dependency.stem/path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(archive.read(name))
    artifacts = [jar, output/'explicit-export', output/'classes/ChocoInstances.class']
    tools = dict(schema='clafer-choco-tools/1', choco_commit=PIN,
        choco_version='0.5.7', solver_version='6.0.2', java_home=str(java_home), java=identity,
        static_tools=str(oracle.external(static_tools)), static_identity=oracle.digest(static_tools),
        source=sources(), choco_sources=before,
        artifacts={str(p.relative_to(output)): oracle.digest(p) for p in artifacts},
        dependencies={p.name: oracle.digest(p) for p in (output/'dependencies').glob('*.jar')},
        maven=subprocess.check_output([str(maven), '-version'], env=dict(os.environ, JAVA_HOME=str(java_home)), text=True),
        haskell_build=api['protocol'].loads((cache/'build.json').read_bytes()))
    oracle.write(output/'tools.json', tools)
    return output/'tools.json'


def load(path):
    path = oracle.external(path)
    value = json.loads(path.read_text())
    require(value['schema'] == 'clafer-choco-tools/1' and value['choco_commit'] == PIN
            and value['source'] == sources(), 'Changed Choco tools/profile; provision again')
    require(oracle.digest(value['static_tools']) == value['static_identity'], 'Changed static tools')
    require(java_identity(value['java_home']) == value['java'], 'Changed Choco JDK')
    for name, identity in value['artifacts'].items():
        require('..' not in Path(name).parts and not Path(name).is_absolute(), 'Invalid artifact path')
        require(oracle.digest(path.parent/name) == identity, 'Changed Choco artifact: '+name)
    require(set(value['artifacts']) == {'chocosolver.jar', 'explicit-export', 'classes/ChocoInstances.class'},
            'Incomplete Choco artifact inventory')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--static-tools', required=True, type=Path)
    parser.add_argument('--capture-cache', required=True, type=Path)
    parser.add_argument('--choco-source', required=True, type=Path)
    parser.add_argument('--java-home', required=True, type=Path)
    parser.add_argument('--maven', type=Path, default=Path(shutil.which('mvn') or 'mvn'))
    parser.add_argument('--maven-cache', required=True, type=Path)
    parser.add_argument('output', type=Path)
    print(prepare(**vars(parser.parse_args())))


if __name__ == '__main__':
    main()
