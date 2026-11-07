#!/usr/bin/env python3
"""Explicitly selected PR113 delta qualification and revision-bound bounded replay."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import oracle
import temporal
import pr113_build as build
import pr113_protocol as protocol

HERE = Path(__file__).resolve().parent
CORPUS = oracle.ROOT / 'tests/fixtures/pr113/inventory.json'
read = temporal.read


def candidate(tools):
    return tools.get('candidate', '9a0f16e')


def corpus(tools):
    return CORPUS if candidate(tools) == '9a0f16e' else CORPUS.parent/'c7-inventory.json'


def identity():
    paths = [Path(__file__), HERE/'pr113_build.py', HERE/'pr113_protocol.py',
             HERE/'pr113-profile.json', HERE/'PR113Export.hs', HERE/'AlloyPR113Inspect.java', CORPUS,
             CORPUS.parent/'delta.json', CORPUS.parent/'c7-inventory.json',
             CORPUS.parent/'c7-delta.json', HERE/'pr113-c7-profile.json']
    paths += list(CORPUS.parent.glob('*.cfr'))
    return dict(temporal.identity(), **{str(p.relative_to(oracle.ROOT)):oracle.digest(p) for p in paths})


def inspector(runtime, api):
    command = [str(runtime['java'].with_name('javac')), '--release', '17', '-cp',
        os.pathsep.join(map(str,(runtime['classes'],runtime['jar']))), '-d', str(runtime['classes']),
        str(HERE/'AlloyPR113Inspect.java')]
    subprocess.run(command, check=True, capture_output=True, timeout=60, env=api['alloy_runtime'].java_env())
    return dict(source=oracle.digest(HERE/'AlloyPR113Inspect.java'),
                binary=oracle.digest(runtime['classes']/'AlloyPR113Inspect.class'),
                warnings=oracle.digest(runtime['classes']/'AlloyPR113Inspect$Warnings.class'))


# [impl->req~compiler-temporal-oracles~1]
def prepare(static_tools, build_cache, output, candidate='9a0f16e'):
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    api = oracle.adapters()
    _, _, alloy = oracle.load_tools(static_tools, api)
    receipt = build.prepare(build_cache, api, candidate)
    runtime = temporal.compile_bridge(alloy, output/'classes', api)
    inspection = inspector(runtime, api)
    tools = dict(schema='clafer-pr113-tools/1', profile=build.profile(candidate),
        build=str(receipt), build_identity=oracle.digest(receipt),
        static_tools=str(oracle.external(static_tools)), static_tools_identity=oracle.digest(static_tools),
        temporal_bridge=runtime['temporal_bridge'], inspector=inspection)
    notices = output/'notices'
    notices.mkdir()
    for name in ('LICENSE','stack.yaml','stack.yaml.lock','clafer.cabal'):
        shutil.copyfile(receipt.parent/'compiler'/name, notices/name)
    oracle.write(output/'notice-index.json',{p.name:oracle.digest(p) for p in notices.iterdir()})
    oracle.write(output/'tools.json',tools)
    return output/'tools.json'


def load_tools(path):
    t = read(oracle.external(path))
    protocol.closed(t, 'schema profile build build_identity static_tools static_tools_identity temporal_bridge inspector', 'tools')
    selected = build.candidate_for(t['profile']['haskell_commit'])
    protocol.require(t['schema']=='clafer-pr113-tools/1' and t['profile']==build.profile(selected), 'Wrong PR113 tools/profile')
    for key in ('alloy_version','alloy_jar_sha256','java_major','solver','options','resources'):
        protocol.require(t['profile'][key]==temporal.temporal_build.profile()[key],
                         'Reused temporal solver profile differs: '+key)
    receipt = oracle.external(t['build'])
    protocol.require(oracle.digest(receipt)==t['build_identity'] and build.valid(receipt.parent, selected), 'Changed PR113 build')
    build.sources(receipt.parent, selected)
    protocol.require(oracle.digest(t['static_tools'])==t['static_tools_identity'], 'Changed provisioning receipt')
    api = oracle.adapters()
    _, _, alloy = oracle.load_tools(t['static_tools'], api)
    scratch = Path(tempfile.mkdtemp(prefix='pr113-bridge-'))
    runtime = temporal.compile_bridge(alloy,scratch/'classes',api)
    runtime['inspector'] = inspector(runtime,api)
    protocol.require(runtime['temporal_bridge']==t['temporal_bridge'] and runtime['inspector']==t['inspector'], 'Changed PR113 bridge')
    runtime['pr113_candidate'] = selected
    return dict(candidate=selected, build=receipt, exporter=receipt.parent/'clafer-pr113-capture',runtime=runtime,api=api,tools=t)


def inputs(case, tools):
    base = tools['build'].parent/'compiler/test/positive' if case['origin']=='haskell' else CORPUS.parent
    result = {}
    for name,digest in case['files'].items():
        protocol.require(Path(name).name==name, 'Flat registered input path required')
        path = base/name
        protocol.require(oracle.digest(path)==digest, 'Changed fixture: '+name)
        result[name] = path.read_bytes()
    protocol.require(case['entry'] in result, 'Missing entry fixture')
    return result


def capture(tools, files, entry, output, *, backend=None):
    output.mkdir(parents=True,exist_ok=False)
    input_dir = output/'inputs'
    input_dir.mkdir()
    for name,data in files.items():
        protocol.require(Path(name).name==name, 'Invalid input filename')
        (input_dir/name).write_bytes(data)
    command = [str(tools['exporter']), *(['--static'] if backend == 'als' else []), entry]
    oracle.write(output/'capture-command.json',dict(command=command,cwd='inputs'))
    with (output/'generation.json').open('wb') as out, (output/'capture.stderr').open('wb') as err:
        process = subprocess.run(command,cwd=input_dir,stdout=out,stderr=err,timeout=30)
    protocol.require(process.returncode==0, 'Haskell exporter failed; inspect capture.stderr')
    g = read(output/'generation.json')
    if g['status']!='captured':
        return g
    protocol.generation(g)
    protocol.require(g['compiler_commit'] == build.profile(candidate(tools))['haskell_commit'], 'Wrong capture revision')
    protocol.require(g['backend']==(backend or 'tmp.als'), 'Capture backend differs from selection')
    for name,key in [('model.als','alloy'),('model.json','json'),('explicit.cfr','explicit'),
                     ('original.cfr-scope','original_scopes'),('explicit.cfr-scope','explicit_scopes')]:
        (output/name).write_text(g[key])
    return g


def inspect(tools, g, output, query_directory=None):
    if query_directory is None:
        runtime = tools['runtime']
        command = [str(runtime['java']),'-XX:ActiveProcessorCount=1','-cp',
            os.pathsep.join(map(str,(runtime['classes'],runtime['jar']))),'AlloyPR113Inspect']
        oracle.write(output/'inspect-command.json',command)
        with (output/'inspect.stdout').open('wb') as out, (output/'inspect.stderr').open('wb') as err:
            subprocess.run(command,cwd=output,stdout=out,stderr=err,check=True,timeout=30,
                           env=tools['api']['alloy_runtime'].java_env())
    else:
        # Retain the actual shared invocation; this did not start another JVM.
        runtime = read(query_directory/'runtime.json')
        oracle.write(output/'inspect-command.json',dict(command=runtime['command'],
            cwd=os.path.relpath(query_directory,output), shared_with='result.json'))
        for source,destination in [('stdout.log','inspect.stdout'),('stderr.log','inspect.stderr')]:
            shutil.copyfile(query_directory/source,output/destination)
        observed = query_directory/'inspection.json'
        if not observed.is_file():
            failed = read(query_directory/'result.json')
            if failed['status']=='timeout':
                raise subprocess.TimeoutExpired(runtime['command'],runtime['timeout_seconds'])
            raise ValueError('Analyzer inspection failed: '+failed['status']+' during '+
                             failed.get('stage','unknown')+'; see query result.json')
        shutil.copyfile(observed,output/'inspection.json')
    observed = read(output/'inspection.json')
    validate_inspection(g,observed)
    return observed


def assertions(g):
    """Source preorder is the pinned explicit printer's assertion emission order."""
    result = []
    def visit(elements):
        for e in elements:
            if e['tag']=='IEClafer': visit(e['_iClafer']['_elements'])
            elif e['tag']=='IEConstraint' and not e['_isHard']:
                p = e['_cpexp']['_inPos']['start']
                result.append('assertAt_'+str(p['line'])+'_'+str(p['column']))
    visit(g['post_analysis']['_mDecls'])
    return result


# [impl->req~compiler-temporal-oracles~1]
def validate_inspection(g, observed):
    protocol.layout(g,observed)
    order = assertions(g)
    commands = observed['commands']
    protocol.require(len(commands)==len(order)+1, 'Unexpected extra commands')
    protocol.require(commands[0]['check'] is False, 'Command zero must be a model run')
    protocol.require(all(c['check'] is True for c in commands[1:]), 'Only one model run expected')
    positions = {c['label']:i for i,c in enumerate(commands) if c['check']}
    protocol.require(len(positions)==len(order) and set(positions)==set(order), 'Assertion command coverage differs')


def query(tools, generation, request, directory, *, inspection=False):
    directory.mkdir()
    (directory/'model.als').write_text(generation['alloy'])
    selected = candidate(tools)
    inspection = inspection or selected == 'c7a2fb7'
    runtime = dict(tools['runtime'], static_backend=generation.get('backend') == 'als')
    result = temporal.solve(runtime,tools['api'],directory,request,
        inspection=inspection,**build.profile(selected)['resources'])
    if selected == 'c7a2fb7' and result['status'] == 'ok':
        try:
            diagnostics = read(directory/'warnings.json')
            protocol.closed(diagnostics, 'schema warnings', 'warning receipt')
            protocol.require(diagnostics['schema']=='clafer-alloy-warnings/1' and
                type(diagnostics['warnings']) is list, 'Invalid warning receipt')
            for warning in diagnostics['warnings']:
                protocol.closed(warning, 'message line column end_line end_column', 'warning')
                protocol.require(type(warning['message']) is str and all(type(warning[k]) is int
                    for k in ('line','column','end_line','end_column')), 'Invalid warning fields')
        except (OSError,ValueError,KeyError,TypeError) as error:
            result = dict(result,status='error',outcome=None,detail='Invalid warnings: '+str(error))
    if inspection and result['status']=='ok':
        try:
            validate_inspection(generation,read(directory/'inspection.json'))
        except (OSError,ValueError,KeyError,TypeError,IndexError) as error:
            result = dict(result,status='error',outcome=None,detail='Invalid inspection: '+str(error))
    oracle.write(directory/'result.json',result)
    return result


def index(output):
    oracle.write(output/'evidence-index.json',{str(p.relative_to(output)):oracle.digest(p)
        for p in sorted(output.rglob('*')) if p.is_file() and p!=output/'evidence-index.json'})


def declaration_paths(module):
    result = {}
    def visit(elements, parent):
        for element in elements:
            if element['tag'] == 'IEClafer':
                c = element['_iClafer']
                path = parent + (c['_ident'],)
                protocol.require(path not in result, 'Ambiguous revision correspondence')
                result[path] = c['_uid']
                visit(c['_elements'], path)
    visit(module['_mDecls'], ())
    return result


def historical(tools, case, original, output):
    """Reproduce the old discrepancy, matching authored paths, never UID prefixes."""
    old = tools['old']
    output.mkdir()
    files = inputs(case, tools)
    protocol.require(len(files) == 1, 'Historical witness must be self-contained')
    (output/'input.cfr').write_bytes(files[case['entry']])
    command = [str(old['exporter']), 'input.cfr']
    oracle.write(output/'capture-command.json', command)
    with (output/'generation.json').open('wb') as out, (output/'capture.stderr').open('wb') as err:
        subprocess.run(command, cwd=output, stdout=out, stderr=err, check=True, timeout=30)
    g = read(output/'generation.json')
    protocol.require(g['status'] == 'captured' and g['backend'] == 'tmp.als', 'Historical capture failed')
    old_paths, new_paths = declaration_paths(g['post_analysis']), declaration_paths(original['post_analysis'])
    protocol.require(old_paths.keys() == new_paths.keys(), 'Revision declaration paths differ')
    request = protocol.request(original, 0, scopes=case.get('scopes'), steps=case.get('steps'))
    request['identities'] = {'this/root': request['identities']['this/root'], **{
        'this/'+u: request['identities']['this/'+original['names'][new_paths[path]]]
        for path,u in old_paths.items()}}
    oracle.write(output/'correspondence.json', {u:new_paths[path] for path,u in old_paths.items()})
    oracle.write(output/'profile.json', old['tools']['profile'])
    shutil.copyfile(old['build'],output/'build.json')
    (output/'model.als').write_text(g['alloy'])
    (output/'model.json').write_text(g['json'])
    result = temporal.solve(old['runtime'],old['api'],output,request,**build.profile()['resources'])
    oracle.write(output/'result.json',result)
    protocol.require(result['status']=='ok' and result['outcome']==case['old_expected'],
                     'Historical discrepancy outcome differs: '+str(result.get('outcome')))
    return dict(status=result['status'],outcome=result['outcome'])


# [impl->req~compiler-temporal-oracles~1]
def run_case(tools, case, output):
    output = oracle.external(output)
    output.mkdir(parents=True,exist_ok=False)
    oracle.write(output/'case.json',case)
    oracle.write(output/'source-identity.json',identity())
    oracle.write(output/'profile.json',build.profile(candidate(tools)))
    shutil.copyfile(tools['build'],output/'build.json')
    result = dict(status='error', checks=[])
    try:
        original = capture(tools,inputs(case,tools),case['entry'],output/'original',
            **({'backend':case['backend']} if 'backend' in case else {}))
        if original['status']!='captured':
            result.update(status=original['status'],detail=original.get('detail'),outputs=original.get('outputs'))
        else:
            explicit = capture(tools,{'explicit.cfr':original['explicit'].encode()},'explicit.cfr',output/'explicit',
                **({'backend':case['backend']} if 'backend' in case else {}))
            protocol.require(explicit['status']=='captured','Explicit recompile failed: '+str(explicit))
            result['fixed_point'] = original['explicit']==explicit['explicit']
            protocol.require(result['fixed_point'],'Explicit corpus fixed point failed')
            protocol.require(original['names']==explicit['names'],'Explicit declaration identities changed')
            protocol.require(original['trace_length']==explicit['trace_length'],'Explicit trace length changed')
            request = protocol.request(original,0,scopes=case.get('scopes'),steps=case.get('steps'))
            first_a = query(tools,original,request,output/'original-query-0',inspection=True)
            a = inspect(tools,original,output/'original',output/'original-query-0')
            first_b = query(tools,explicit,request,output/'explicit-query-0',inspection=True)
            b = inspect(tools,explicit,output/'explicit',output/'explicit-query-0')
            original_order,explicit_order = assertions(original),assertions(explicit)
            protocol.require(len(original_order)==len(explicit_order),'Assertion count changed')
            positions_a = {c['label']:i for i,c in enumerate(a['commands']) if c['check']}
            positions_b = {c['label']:i for i,c in enumerate(b['commands']) if c['check']}
            protocol.require(set(positions_a)==set(original_order) and set(positions_b)==set(explicit_order), 'Assertion command coverage differs')
            protocol.require(len(a['commands'])==len(original_order)+1 and len(b['commands'])==len(explicit_order)+1,
                             'Unexpected extra commands')
            pairs = [('run',0,0)] + [(x,positions_a[x],positions_b[y]) for x,y in zip(original_order,explicit_order)]
            for ordinal,(label,ia,ib) in enumerate(pairs):
                if ordinal == 0:
                    ra,rb = first_a,first_b
                else:
                    request = protocol.request(original,ia,scopes=case.get('scopes'),steps=case.get('steps'))
                    ra = query(tools,original,request,output/('original-query-'+str(ordinal)))
                    rb = query(tools,explicit,dict(request,command_index=ib),output/('explicit-query-'+str(ordinal)))
                check = dict(label=label,original_index=ia,explicit_index=ib,
                    original_status=ra['status'],explicit_status=rb['status'],
                    original_outcome=ra.get('outcome'),explicit_outcome=rb.get('outcome'))
                result['checks'].append(check)
            failures = [c for c in result['checks'] if c['original_status']!='ok' or c['explicit_status']!='ok']
            result['status'] = 'query_failure' if failures else 'ok'
            if not failures:
                result['agreement'] = all(c['original_outcome']==c['explicit_outcome'] for c in result['checks'])
                if not result['agreement']: result['status']='discrepancy'
                if 'expected' in case:
                    result['expected_match'] = [c['original_outcome'] for c in result['checks']]==case['expected']
                    if 'expected_explicit' in case:
                        result['expected_match'] = result['expected_match'] and [c['explicit_outcome']
                            for c in result['checks']]==case['expected_explicit']
                    if not result['expected_match']: result['status']='unexpected_outcome'
                result['assertions_nonvacuous'] = all(c['original_outcome']=='sat' and c['explicit_outcome']=='sat'
                    for c in result['checks'][:1]) if len(result['checks']) > 1 else None
                if 'old_expected' in case:
                    protocol.require('old' in tools, 'Historical tools required for revision witnesses')
                    result['historical'] = historical(tools,case,original,output/'historical')
            result['strength'] = 'printer fixed point and paired bounded run/check outcomes; no exact-lasso equivalence'
    except subprocess.TimeoutExpired as error:
        result.update(status='timeout',detail=str(error))
    except (OSError,ValueError,KeyError,TypeError,RuntimeError,subprocess.SubprocessError) as error:
        result.update(status='error',detail=str(error))
    oracle.write(output/'result.json',result)
    index(output)
    return result


def replay(tools, bundle, output):
    bundle = oracle.external(bundle)
    for name,digest in read(bundle/'evidence-index.json').items():
        path = (bundle/name).resolve()
        protocol.require(path.is_relative_to(bundle) and oracle.digest(path)==digest,'Replay artifact changed: '+name)
    protocol.require(read(bundle/'source-identity.json')==identity(),'Replay adapter source changed')
    protocol.require(read(bundle/'profile.json')==build.profile(candidate(tools)),'Replay revision/profile changed')
    protocol.require(oracle.digest(bundle/'build.json')==oracle.digest(tools['build']), 'Replay build changed')
    if (bundle/'historical').exists():
        protocol.require('old' in tools and oracle.digest(bundle/'historical/build.json')==oracle.digest(tools['old']['build']),
                         'Historical replay build changed')
    case = read(bundle/'case.json')
    protocol.require(case in read(corpus(tools))['cases'], 'Replay fixture is not registered')
    result = run_case(tools,case,output)
    protocol.require(result['status']==case.get('expected_status','ok'), 'Fresh replay did not complete')
    for mode in ('original','explicit'):
        for name in ('generation.json','model.als','model.json','explicit.cfr','original.cfr-scope','explicit.cfr-scope'):
            if (bundle/mode/name).exists():
                protocol.require(oracle.digest(bundle/mode/name)==oracle.digest(Path(output)/mode/name),'Fresh generation differs: '+mode+'/'+name)
    protocol.require(read(bundle/'result.json')==result,'Fresh bounded outcomes differ')
    if (bundle/'historical').exists():
        for name in ('generation.json','model.als','model.json','correspondence.json','request.json'):
            protocol.require(oracle.digest(bundle/'historical'/name)==oracle.digest(Path(output)/'historical'/name),
                             'Historical generation/query differs: '+name)
    return result


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    sub = cli.add_subparsers(dest='command',required=True)
    p = sub.add_parser('prepare')
    p.add_argument('--static-tools',required=True,type=Path)
    p.add_argument('--build-cache',required=True,type=Path)
    p.add_argument('--candidate',choices=build.PROFILES,default='9a0f16e')
    p.add_argument('output',type=Path)
    for name in ('run','suite','replay'):
        p = sub.add_parser(name)
        p.add_argument('--tools',required=True,type=Path)
        p.add_argument('--old-tools',type=Path)
        if name=='run': p.add_argument('case')
        if name=='replay': p.add_argument('bundle',type=Path)
        p.add_argument('output',type=Path)
    args = cli.parse_args()
    if args.command=='prepare':
        print(prepare(args.static_tools,args.build_cache,args.output,args.candidate)); return 0
    tools = load_tools(args.tools)
    if args.old_tools: tools['old'] = temporal.load_tools(args.old_tools)
    if args.command=='replay':
        print(json.dumps(replay(tools,args.bundle,args.output))); return 0
    cases = read(corpus(tools))['cases']
    if args.command=='run': cases = [c for c in cases if c['id']==args.case]
    protocol.require(bool(cases),'Unknown PR113 case')
    ok = True
    for case in cases:
        r = run_case(tools,case,args.output/case['id'] if args.command=='suite' else args.output)
        print(json.dumps(dict(case=case['id'],**r)),flush=True)
        ok = ok and r['status']==case.get('expected_status','ok')
    return 0 if ok else 1


if __name__=='__main__':
    try: sys.exit(main())
    except (OSError,ValueError,KeyError,RuntimeError,subprocess.SubprocessError) as error:
        print(json.dumps(dict(status='error',detail=str(error))),file=sys.stderr)
        sys.exit(1)
