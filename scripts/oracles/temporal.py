#!/usr/bin/env python3
"""Explicit behavioral oracle profile; never changes the static oracle protocol."""
import argparse
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile

import oracle
import temporal_build

HERE = Path(__file__).resolve().parent
CORPUS = oracle.ROOT / 'tests/fixtures/temporal/inventory.json'


def read(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=unique)


def identity():
    paths = [Path(__file__), HERE / 'temporal_build.py', HERE / 'TemporalExport.hs',
             HERE / 'AlloyTemporalBridge.java', HERE / 'temporal-profile.json', CORPUS]
    paths += sorted(CORPUS.parent.glob('*.cfr'))
    return {str(p.relative_to(oracle.ROOT)): oracle.digest(p) for p in paths}


def compile_bridge(runtime, output, api):
    output.mkdir(parents=True, exist_ok=False)
    subprocess.run([str(runtime['java'].with_name('javac')), '--release', '17', '-cp',
        str(runtime['jar']), '-d', str(output), str(HERE / 'AlloyTemporalBridge.java')],
        check=True, capture_output=True, timeout=60, env=api['alloy_runtime'].java_env())
    return dict(runtime, classes=output, temporal_bridge=dict(
        source=oracle.digest(HERE / 'AlloyTemporalBridge.java'),
        binary=oracle.digest(output / 'AlloyTemporalBridge.class')))


# [impl->req~compiler-temporal-oracles~1]
def prepare(static_tools, build_cache, output):
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    api = oracle.adapters()
    # The static receipt is only a provisioning source; it is not rewritten.
    _, _, alloy = oracle.load_tools(static_tools, api)
    exporter, build = temporal_build.prepare(build_cache, api)
    runtime = compile_bridge(alloy, output / 'classes', api)
    source = build.parent / 'compiler'
    notices = output / 'notices'
    notices.mkdir()
    for name in ('LICENSE', 'stack.yaml', 'stack.yaml.lock', 'clafer.cabal'):
        shutil.copyfile(source / name, notices / name)
    # Existing provisioning retains all embedded Alloy notices; bind that inventory.
    tools = dict(schema='clafer-temporal-tools/1', profile=temporal_build.profile(),
        exporter=str(exporter), build=str(build), exporter_identity=oracle.digest(exporter),
        build_identity=oracle.digest(build), static_tools=str(oracle.external(static_tools)),
        static_tools_identity=oracle.digest(static_tools), temporal_bridge=runtime['temporal_bridge'])
    oracle.write(output / 'tools.json', tools)
    oracle.write(output / 'build.json', read(build))
    oracle.write(output / 'notice-index.json', {p.name:oracle.digest(p) for p in notices.iterdir()})
    return output / 'tools.json'


def load_tools(path):
    path = oracle.external(path)
    t = read(path)
    if t['schema'] != 'clafer-temporal-tools/1' or t['profile'] != temporal_build.profile():
        raise ValueError('Wrong temporal tools/profile')
    exporter, build = oracle.external(t['exporter']), oracle.external(t['build'])
    if (oracle.digest(exporter) != t['exporter_identity'] or oracle.digest(build) != t['build_identity']
            or not temporal_build.valid(exporter, build)):
        raise ValueError('Temporal exporter/build changed; rebuild exporter')
    temporal_build.sources(build.parent / 'compiler.tar.gz', build.parent / 'compiler')
    if oracle.digest(t['static_tools']) != t['static_tools_identity']:
        raise ValueError('Provisioning receipt changed')
    api = oracle.adapters()
    _, _, alloy = oracle.load_tools(t['static_tools'], api)
    scratch = Path(tempfile.mkdtemp(prefix='temporal-bridge-'))
    runtime = compile_bridge(alloy, scratch / 'classes', api)
    if runtime['temporal_bridge'] != t['temporal_bridge']:
        raise ValueError('Temporal bridge changed; provision tools again')
    return dict(exporter=exporter, build=build, runtime=runtime, api=api, tools=t)


def request_valid(r):
    if type(r) is not dict or set(r) != {'command_index','overall','bitwidth','min_steps','max_steps','identities'}:
        raise ValueError('Closed temporal request schema required')
    for k in ('command_index','overall','bitwidth','min_steps','max_steps'):
        if type(r[k]) is not int:
            raise ValueError('Integer required: ' + k)
    if not (r['command_index']>=0 and r['overall']>=1 and 1<=r['bitwidth']<=16 and
            1<=r['min_steps']<=r['max_steps']<=100):
        raise ValueError('Invalid temporal command bounds')
    if type(r['identities']) is not dict or not r['identities']:
        raise ValueError('Explicit signature identity scopes required')
    for name, b in r['identities'].items():
        if (not name.startswith('this/') or type(b) is not dict or set(b) != {'count','exact'}
                or type(b['count']) is not int or b['count']<0 or type(b['exact']) is not bool):
            raise ValueError('Invalid identity scope')


def interrupted(directory, status, detail):
    checkpoint = directory / 'execution.json'
    try:
        observed = read(checkpoint) if checkpoint.exists() else {}
    except (ValueError, OSError):
        observed = {}
    return dict(observed, status=status, detail=detail)


def solve(runtime, api, directory, request, timeout=30, heap_mb=512, *, inspection=False, integer_fields=()):
    request_valid(request)
    if type(timeout) is not int or timeout<=0 or type(heap_mb) is not int or heap_mb<64:
        raise ValueError('Invalid resource budget')
    if type(inspection) is not bool:
        raise ValueError('Boolean inspection selection required')
    integer_fields = set(integer_fields)
    if any(type(name) is not str or not name.startswith('this/') for name in integer_fields):
        raise ValueError('Explicit integer field names required')
    oracle.write(directory / 'request.json', request)
    options = [f'-Xmx{heap_mb}m','-Xss1m','-XX:ActiveProcessorCount=1','-XX:+UseSerialGC',
               '-XX:ReservedCodeCacheSize=64m','-XX:CompressedClassSpaceSize=64m']
    command = [str(runtime['java']), *options, '-cp', os.pathsep.join(
        map(str,(runtime['classes'],runtime['jar'])))]
    flag = '--solve'
    if runtime.get('pr113_candidate') in ('c7a2fb7', '0.5.8'):
        flag = '--solve-static-c7' if runtime.get('static_backend') else '--solve-c7'
    command += ['AlloyPR113Inspect', flag] if inspection else ['AlloyTemporalBridge']
    address = heap_mb+2048
    receipt = dict(identity=runtime['identity'],
        bridge=runtime['temporal_bridge'], command=command, timeout_seconds=timeout,
        heap_mb=heap_mb, address_space_mb=address, jvm_options=options)
    if inspection:
        receipt['inspector'] = runtime['inspector']
    oracle.write(directory / 'runtime.json', receipt)
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(address*1024**2,)*2)
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    with (directory/'stdout.log').open('wb') as out, (directory/'stderr.log').open('wb') as err:
        try:
            process = subprocess.run(command,cwd=directory,stdout=out,stderr=err,
                timeout=timeout,env=api['alloy_runtime'].java_env(),preexec_fn=limits)
        except subprocess.TimeoutExpired:
            return interrupted(directory,'timeout','solver wall-clock limit')
        except OSError as error:
            return interrupted(directory,'error',str(error))
    if process.returncode:
        return interrupted(directory,'error',f'JVM exit {process.returncode}')
    try:
        result=read(directory/'solver.json')
        if result['schema']!='clafer-temporal-solver/1' or result['status'] not in (
                'ok','malformed','error','resource_limit'):
            raise ValueError('Invalid temporal solver result')
        if result['status']=='ok':
            if result['outcome'] not in ('sat','bounded_unsat'):
                raise ValueError('Invalid completed solver outcome')
            expected = dict(temporal_build.profile()['options'],solver='sat4j')
            if result['options'] != expected:
                raise ValueError('Unexpected effective solver options')
            if result['outcome']=='sat':
                scalar_fields = set(integer_fields)
                if inspection and (runtime.get('pr113_candidate') == '0.5.8' or (
                        runtime.get('pr113_candidate') == 'c7a2fb7' and runtime.get('static_backend'))):
                    observed = read(directory/'inspection.json')
                    scalar_fields.update(k for k,f in observed['fields'].items() if f['targets']==['Int'])
                validate_trace(result['trace'],request,integer_fields=scalar_fields)
            if inspection:
                try:
                    observed = read(directory/'inspection.json')
                    if (type(observed) is not dict or set(observed) != {'schema','signatures','fields','commands'}
                            or observed['schema'] != 'clafer-pr113-inspection/1'
                            or type(observed['signatures']) is not dict or type(observed['fields']) is not dict
                            or type(observed['commands']) is not list):
                        raise ValueError('Invalid inspection schema')
                except (OSError,ValueError,KeyError,TypeError) as error:
                    return dict(result,status='error',outcome=None,detail='Invalid inspection: '+str(error))
        return result
    except (OSError,ValueError,KeyError,TypeError) as error:
        return interrupted(directory,'error','Invalid solver output: '+str(error))


def validate_trace(trace, request, *, integer_fields=()):
    n,loop,frames=trace['length'],trace['loop'],trace['frames']
    if type(n) is not int or type(loop) is not int or not 0<=loop<n or len(frames)!=n:
        raise ValueError('Malformed lasso')
    if not request['min_steps']<=n<=request['max_steps']:
        raise ValueError('Trace outside step bounds')
    union=set()
    for name,bound in request['identities'].items():
        atoms=set()
        for frame in frames:
            if set(frame['signatures'])!=set(request['identities']):
                raise ValueError('Trace signature inventory changed')
            rows=frame['signatures'][name]
            if any(type(row) is not list or len(row)!=1 or type(row[0]) is not str for row in rows):
                raise ValueError('Malformed signature tuples')
            atoms.update(row[0] for row in rows)
        if len(atoms)>bound['count']:
            raise ValueError('Trace exceeds identity budget')
        if bound['exact'] and len(atoms)!=bound['count']:
            raise ValueError('Trace differs from exact identity budget')
        if not trace['signatures'][name]['mutable'] and any(
                f['signatures'][name]!=frames[0]['signatures'][name] for f in frames):
            raise ValueError('Immutable signature changed')
        union.update(atoms)
    if sorted(union)!=trace['inventory']:
        raise ValueError('Trace-wide inventory mismatch')
    for frame in frames:
        if set(frame['fields'])!=set(trace['fields']):
            raise ValueError('Trace field inventory changed')
        for name,spec in trace['fields'].items():
            rows=frame['fields'][name]
            def admitted(i, atom):
                if atom in union: return True
                if name not in integer_fields or i!=1: return False
                try: value = int(atom)
                except (TypeError,ValueError): return False
                return str(value)==atom and -(2**(request['bitwidth']-1)) <= value < 2**(request['bitwidth']-1)
            if any(len(row)!=spec['arity'] or any(not admitted(i,atom) for i,atom in enumerate(row)) for row in rows):
                raise ValueError('Malformed or foreign field tuple')
            if not spec['mutable'] and rows!=frames[0]['fields'][name]:
                raise ValueError('Immutable field changed')


def fixture(case, tools):
    if case['origin']=='haskell':
        base=tools['build'].parent/'compiler'
    elif case['origin']=='compiler':
        base=CORPUS.parent
    else:
        raise ValueError('Unknown fixture origin')
    path=(base/case['path']).resolve()
    if not path.is_relative_to(base.resolve()) or oracle.digest(path)!=case['identity']:
        raise ValueError('Fixture bytes differ from inventory')
    return path


# [impl->req~compiler-temporal-oracles~1]
def run_case(tools, case, output):
    output=oracle.external(output)
    output.mkdir(parents=True,exist_ok=False)
    result=dict(status='error',outcome=None)
    oracle.write(output/'case.json',case)
    oracle.write(output/'source-identity.json',identity())
    try:
        source=fixture(case,tools)
        shutil.copyfile(source,output/'input.cfr')
        command=[str(tools['exporter']),str(output/'input.cfr')]
        oracle.write(output/'capture-command.json',command)
        with (output/'generation.json').open('wb') as out, (output/'capture.stderr').open('wb') as err:
            process=subprocess.run(command,stdout=out,stderr=err,timeout=30)
        if process.returncode:
            raise RuntimeError('Haskell exporter failed; inspect capture.stderr')
        generation=read(output/'generation.json')
        if generation['status']!='captured':
            result=dict(status=generation['status'],outcome=None,detail=generation.get('detail'))
        else:
            if generation['schema']!='clafer-temporal-generation/1' or generation['backend']!='tmp.als':
                raise ValueError('Wrong temporal generation backend/schema')
            (output/'model.als').write_text(generation['alloy'])
            (output/'model.json').write_text(generation['json'])
            oracle.write(output/'build.json',read(tools['build']))
            oracle.write(output/'capture.json',dict(schema='clafer-temporal-capture/1',
                profile=temporal_build.profile(),effective_options=generation['effective_options'],
                artifacts={name:oracle.digest(output/name) for name in
                    ('input.cfr','model.als','model.json','generation.json','build.json')},
                exporter=oracle.digest(tools['exporter'])))
            result=solve(tools['runtime'],tools['api'],output,case['request'],
                         **temporal_build.profile()['resources'])
    except subprocess.TimeoutExpired:
        result=dict(status='timeout',outcome=None,detail='Haskell capture wall-clock limit')
    except (OSError,ValueError,KeyError,TypeError,RuntimeError) as error:
        result=dict(status='error',outcome=None,detail=str(error))
    oracle.write(output/'result.json',result)
    oracle.write(output/'evidence-index.json',{p.name:oracle.digest(p)
        for p in sorted(output.iterdir()) if p.is_file()})
    return result


def replay(tools,bundle,output):
    bundle=oracle.external(bundle)
    for name,digest in read(bundle/'evidence-index.json').items():
        if Path(name).name!=name or oracle.digest(bundle/name)!=digest:
            raise ValueError('Replay artifact changed: '+name)
    if read(bundle/'source-identity.json')!=identity():
        raise ValueError('Replay adapter source changed')
    case=read(bundle/'case.json')
    result=run_case(tools,case,output)
    if (Path(output)/'capture.json').exists():
        for name in ('input.cfr','model.als','model.json','generation.json','build.json'):
            if oracle.digest(bundle/name)!=oracle.digest(Path(output)/name):
                raise ValueError('Fresh compiler replay differs: '+name)
    # Re-run the recorded bounded query; this is not C9 exact-candidate replay.
    return result


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    sub=cli.add_subparsers(dest='command',required=True)
    p=sub.add_parser('prepare')
    p.add_argument('--static-tools',required=True,type=Path)
    p.add_argument('--build-cache',required=True,type=Path)
    p.add_argument('output',type=Path)
    for name in ('run','replay','suite'):
        p=sub.add_parser(name)
        p.add_argument('--tools',required=True,type=Path)
        if name=='run': p.add_argument('case')
        if name=='replay': p.add_argument('bundle',type=Path)
        p.add_argument('output',type=Path)
    args=cli.parse_args()
    if args.command=='prepare':
        print(prepare(args.static_tools,args.build_cache,args.output)); return 0
    tools=load_tools(args.tools)
    if args.command=='replay':
        results=[replay(tools,args.bundle,args.output)]
        ok=results[0]['status']=='ok' and results[0]['outcome']==read(args.bundle/'result.json')['outcome']
    else:
        cases=read(CORPUS)['cases']
        if args.command=='run':
            cases=[c for c in cases if c['id']==args.case]
            if not cases: raise ValueError('Unknown temporal fixture')
        else: oracle.external(args.output).mkdir(parents=True,exist_ok=False)
        results=[run_case(tools,c,args.output/c['id'] if args.command=='suite' else args.output) for c in cases]
        ok=all(r['status']=='ok' and r['outcome']==c['expected'] for c,r in zip(cases,results))
    print(json.dumps([dict(status=r['status'],outcome=r.get('outcome'),detail=r.get('detail')) for r in results]))
    return 0 if ok else 1


if __name__=='__main__':
    try: sys.exit(main())
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError) as error:
        print(json.dumps(dict(status='error',outcome=None,detail=str(error))),file=sys.stderr)
        sys.exit(1)
