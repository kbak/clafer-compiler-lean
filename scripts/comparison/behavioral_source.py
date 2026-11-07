#!/usr/bin/env python3
"""Full source exact candidates and retained replay (executable, not proved)."""
import argparse
import copy
import importlib
import json
from pathlib import Path
import shutil
import subprocess
import time

import temporal_compare as tc
from behavioral_observation import Observation

ROOT, oracle, temporal = tc.ROOT, tc.oracle, tc.temporal
PROFILE = 'behavioral-0.5.7-candidate/v1'
SCALAR = 'this/cc0/cc3'


def source_identity():
    result = tc.source_identity()
    result.update(importlib.import_module("pr113").identity())
    for name in ('tests/BehavioralSourceTraceNative.lean', 'tests/test_behavioral_source_comparison.py',
                 'tests/behavioral_source_cases.py', 'tests/test_behavioral_source_cli.py',
                 'scripts/qualification.py'):
        result[name] = oracle.digest(ROOT/name)
    return result


def candidate_valid(c, p):
    tc.closed(c, 'version profile root length loop identities frames')
    tc.require(c['version']=='clafer-behavioral-trace/2' and c['profile']==PROFILE, 'trace profile')
    n, loop = tc.natural(c['length']), tc.natural(c['loop'])
    tc.require(0 <= loop < n and type(c['frames']) is list and len(c['frames'])==n, 'lasso shape')
    tc.require(type(c['identities']) is list and c['identities'], 'identity inventory')
    ds = {d['id']:d for d in p['declarations']}
    ids = {}
    for r in c['identities']:
        tc.closed(r,'id type parent')
        x = tc.natural(r['id'])
        tc.require(x not in ids and tc.natural(r['type']) in ds and not ds[r['type']]['primitive'], 'direct type')
        tc.require(r['parent'] is None or type(r['parent']) is int, 'parent identity')
        ids[x] = r
    tc.require(tc.natural(c['root']) in ids and all(r['parent'] is None or r['parent'] in ids for r in ids.values()), 'unknown identity')
    for f in c['frames']:
        tc.closed(f,'live references values')
        tc.require(type(f['live']) is list and all(type(x) is int and x in ids for x in f['live']) and
                   len(set(f['live']))==len(f['live']), 'live identities')
        tc.require(type(f['references']) is list, 'reference rows')
        for row in f['references']:
            tc.require(type(row) is list and len(row)==3 and all(type(x) is int for x in row), 'reference tuple')
            d,x,y = row
            tc.require(d in ds and x in ids and y in ids, 'reference endpoint')
        tc.require(len(set(map(tuple,f['references'])))==len(f['references']), 'duplicate reference')
        tc.require(type(f['values']) is list, 'scalar rows')
        for row in f['values']:
            tc.require(type(row) is list and len(row)==2 and all(type(x) is int for x in row), 'scalar tuple')
        tc.require(len(f['values'])==len(ids) and {x for x,z in f['values']}==set(ids), 'complete unique scalar heads')
        tc.require(all(-(2**(p['bitwidth']-1)) <= z < 2**(p['bitwidth']-1) for x,z in f['values']), 'scalar bitwidth')
        tc.require(all(p['integers']['lower'] <= z <= p['integers']['upper'] for x,z in f['values']), 'scalar value interval')
    return ids, ds


def target(c,p):
    ids, ds = candidate_valid(c,p)
    names = {x:'object_'+str(x) for x in ids}
    sigs = {s:[] for s in p['signatures']}
    sigs['this/cc0'] = [[names[x]] for x in ids]
    for x,r in ids.items():
        sigs[ds[r['type']]['signature']].append([names[x]])
    parents = [[names[x],names[r['parent']]] for x,r in ids.items() if r['parent'] is not None]
    frames = []
    for f in c['frames']:
        fields = {s:[] for s in p['fields']}
        fields['this/cc0/cc1'] = copy.deepcopy(parents)
        fields['this/cc0/cc5'] = [[names[c['root']],names[x]] for x in f['live']]
        for d,x,y in f['references']:
            fields[ds[d]['referenceField']].append([names[x],names[y]])
        fields[SCALAR] = [[names[x],str(z)] for x,z in f['values']]
        frames.append(dict(signatures=copy.deepcopy(sigs),fields=fields))
    return dict(length=c['length'],loop=c['loop'],inventory=sorted(names.values()),frames=frames,
                signatures=p['signatures'],fields=p['fields'])


def within_bounds(c,p,bounds):
    trace=target(c,p)
    tc.require(p['minSteps']<=c['length']<=p['maxSteps'],'step bounds')
    for name,b in p['scopes'].items():
        count=len(trace['frames'][0]['signatures'][name])
        tc.require(count<=b['count'] and (not b['exact'] or count==b['count']),'identity bounds')
    ds={d['id']:d for d in p['declarations']}
    for b in bounds['declarations']:
        count=sum(b['id'] in tc.ancestors(ds,r['type']) for r in c['identities'])
        tc.require(count<=b['size'] and (not b['exact'] or count==b['size']),'inherited identity bounds')


def graph(c):
    g = tc.graph(c)
    g['members'] += [[f'value:{t}:{z}',x] for t,f in enumerate(c['frames']) for x,z in f['values']]
    return g


def isomorphism(a,b):
    if (a['length'],a['loop'])!=(b['length'],b['loop']): return None
    return importlib.import_module('relation').isomorphism(graph(a),graph(b))


# [impl->req~compiler-behavioral-qualification~1]
class Runtime:
    def __init__(self,tools,output):
        self.output=oracle.external(output);self.output.mkdir(parents=True,exist_ok=False)
        self.api=oracle.adapters()
        _,_,runtime=oracle.load_tools(tools,self.api)
        self.runtime=temporal.compile_bridge(runtime,self.output/'classes',self.api)
        import sys
        sys.path.insert(0,str(ROOT/'scripts'))
        from qualification import machine
        oracle.write(self.output/'machine.json',machine())
        self.source=source_identity()
        for name in self.source:
            dest=self.output/'source'/name;dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/name,dest)
        module='tests.BehavioralSourceTraceNative'
        def command(name,args,timeout=240):
            tc.run(args,self.output,name,timeout=timeout)
            return (self.output/(name+'-stdout.log')).read_text()
        command('compiler-build',['lake','build','clafer-compiler'])
        modules=[module,*json.loads(command('imports',['lake','query','--json','+'+module+':transImports']))]
        tc.require(not any(m.startswith(('Clafer.','Mathlib.','ClaferCompiler.SemanticsBridge','ClaferCompiler.Correctness'))
                           for m in modules),'runtime imports semantics/proofs')
        objects=[json.loads(s) for s in command('objects',['lake','query','--json',*[f'+{m}:o.export' for m in modules]]).splitlines()]
        harness=self.output/'Harness.lean';c=self.output/'Harness.c';self.native=self.output/'decode'
        harness.write_text(f'import {module}\ndef main (args : List String) : IO Unit := ClaferCompiler.Tests.BehavioralSourceTrace.run args\n')
        command('native-compile',['lake','env','lean',f'--root={self.output}','-c',c,harness])
        command('native-link',['lake','env','leanc',c,*objects,'-o',self.native])
        self.compiler=ROOT/'.lake/build/bin/clafer-compiler'
        self.identity=dict(version='clafer-behavioral-source-runtime/1',sources=self.source,
            compiler=oracle.digest(self.compiler),decoder=oracle.digest(self.native),
            tools=temporal.read(tools),semantics=oracle.SEMANTICS)
        oracle.write(self.output/'runtime.json',self.identity)

    def compile(self,directory,case):
        (directory/'input.cfr').write_text(case['source'])
        oracle.write(directory/'bounds.json',case['bounds'])
        args=[self.compiler,'compile-behavioral-source',directory/'input.cfr','--bounds',directory/'bounds.json',
              '--output',directory/'compilation.json','--format','json','--diagnostics','json']
        q=case['query'];tc.require(type(q) is dict,'query object')
        if q.get('kind')=='model': tc.closed(q,'kind')
        elif q.get('kind')=='check':
            tc.closed(q,'kind assertion');args += ['--assertion',str(tc.natural(q['assertion']))]
        elif q.get('kind')=='scenario':
            tc.closed(q,'kind source owner')
            (directory/'scenario.cfr').write_text(q['source']);args += ['--scenario',directory/'scenario.cfr']
            if q['owner'] is not None: args += ['--owner',str(tc.natural(q['owner']))]
        else: raise ValueError('unknown query kind')
        tc.run(['/usr/bin/time','-f','%e %M','-o',directory/'compile-time.txt','timeout','--kill-after=2s','45s',*args],directory,'compile')
        return temporal.read(directory/'compilation.json')

    def decode(self,directory,trace,name):
        oracle.write(directory/(name+'.json'),trace)
        tc.run([self.native,directory/'input.cfr',directory/(name+'.json')],directory,name)
        decoded=temporal.read(directory/(name+'-stdout.log'))
        tc.require('status' not in decoded,'native trace decode failed: '+str(decoded))
        return decoded

    def solve(self,directory,text,trace,p):
        directory.mkdir()
        pin,scopes=tc.pin(trace,integer_fields=[SCALAR],typed_aliases=True,positions=True)
        (directory/'model.als').write_text(text+'\n'+pin)
        request=dict(command_index=0,overall=1,bitwidth=p['bitwidth'],min_steps=trace['length'],
                     max_steps=trace['length'],identities=p['scopes']|scopes)
        answer=temporal.solve(self.runtime,self.api,directory,request,timeout=120,integer_fields=[SCALAR])
        oracle.write(directory/'result.json',answer)
        return answer

    def compare(self,case,output,*,mutation='none'):
        output=oracle.external(output);output.mkdir(parents=True,exist_ok=False)
        oracle.write(output/'case.json',case);oracle.write(output/'runtime.json',self.identity)
        oracle.write(output/'settings.json',dict(mutation=mutation))
        started=time.monotonic()
        try:
            tc.require(source_identity()==self.source and oracle.digest(self.compiler)==self.identity['compiler'] and
                       oracle.digest(self.native)==self.identity['decoder'],'runtime changed')
            tc.closed(case,'version source query bounds candidate')
            tc.require(case['version']=='clafer-behavioral-source-case/1','case version')
            tc.require(mutation in ('none','reject-all','drop-constraints'),'mutation')
            p=self.compile(output,case);c=case['candidate'];trace=target(c,p)
            within_bounds(c,p,case['bounds'])
            decoded=self.decode(output,trace,'candidate')
            tc.require(isomorphism(c,decoded) is not None,'decode changed candidate')
            start=time.monotonic();source=Observation(p,c).check();check_seconds=time.monotonic()-start
            oracle.write(output/'observation.json',source)
            text=p['alloy']
            if mutation=='reject-all':text+='\nfact { no univ }\n'
            if mutation=='drop-constraints':
                # Explicit fixture mutation: compile a separately supplied source
                # with every authored bracket constraint removed by whole lines.
                lines=case['source'].splitlines(keepends=True)
                tc.require(all(not line.strip().startswith('[') or line.strip().endswith(']') for line in lines),
                           'mutation requires whole-line constraints')
                altered=dict(case,source=''.join(line for line in lines if not line.strip().startswith('[')))
                md=output/'mutation';md.mkdir();text=self.compile(md,altered)['alloy']
            answer=self.solve(output/'compiler',text,trace,p)
            if answer['status']=='timeout': raise TimeoutError('solver wall-clock limit')
            tc.require(answer['status']=='ok','inconclusive solver: '+str({k:answer.get(k) for k in ('status','stage','detail')}))
            sat=answer['outcome']=='sat'
            if sat:
                observed=tc.project_clock(answer['trace'],trace)
                witness=self.decode(output,observed,'witness')
                tc.require(isomorphism(c,witness) is not None,'solver witness differs from exact candidate')
            directions=[] if sat==(source['status']=='satisfied') else ['target-only' if sat else 'source-only']
            result=dict(status='complete',source=source['status'],target=answer['outcome'],directions=directions)
            elapsed,rss=(output/'compile-time.txt').read_text().split()
            oracle.write(output/'measurements.json',dict(compile_seconds=float(elapsed),compile_max_rss_kib=int(rss),
                observation_seconds=check_seconds,total_seconds=time.monotonic()-started,
                identities=len(c['identities']),length=c['length'],loop=c['loop'],scopes=p['scopes'],
                bitwidth=p['bitwidth'],integers=p['integers']))
        except (subprocess.TimeoutExpired,TimeoutError) as e: result=dict(status='timeout',detail=str(e),directions=[])
        except (ValueError,KeyError,TypeError) as e: result=dict(status='malformed',detail=str(e),directions=[])
        except subprocess.CalledProcessError as e:
            result=dict(status='timeout' if e.returncode==124 else 'unsupported' if e.returncode==3 else 'error',detail=str(e),directions=[])
        except OSError as e: result=dict(status='error',detail=str(e),directions=[])
        oracle.write(output/'result.json',result)
        oracle.write(output/'evidence-index.json',{str(p.relative_to(output)):oracle.digest(p)
            for p in sorted(output.rglob('*')) if p.is_file()})
        return result


def replay(runtime,bundle,output):
    bundle=oracle.external(bundle)
    actual={str(p.relative_to(bundle)):oracle.digest(p) for p in sorted(bundle.rglob('*'))
            if p.is_file() and p!=bundle/'evidence-index.json'}
    tc.require(actual==temporal.read(bundle/'evidence-index.json'),'changed replay inventory')
    tc.require(runtime.identity==temporal.read(bundle/'runtime.json'),'changed runtime identity')
    result=runtime.compare(temporal.read(bundle/'case.json'),output,**temporal.read(bundle/'settings.json'))
    tc.require(result==temporal.read(bundle/'result.json'),'changed replay result')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('run','replay'));parser.add_argument('input',type=Path)
    parser.add_argument('output',type=Path);parser.add_argument('--tools',required=True,type=Path)
    args=parser.parse_args();runtime=Runtime(args.tools,args.output/'runtime')
    result=(replay(runtime,args.input,args.output/'case') if args.command=='replay' else
            runtime.compare(temporal.read(args.input),args.output/'case'))
    print(json.dumps(result,sort_keys=True))
    return 0 if result['status']=='complete' and not result['directions'] else 1


if __name__=='__main__': raise SystemExit(main())
