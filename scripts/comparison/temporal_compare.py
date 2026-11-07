#!/usr/bin/env python3
"""Exact behavioral-core/1 lassos; retained native, independent and Haskell evidence."""
import argparse
import copy
import importlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/oracles'))
import oracle
import temporal
import temporal_build
from pr113_protocol import unique
from compare import run


def require(condition, message):
    if not condition:
        raise ValueError(message)


def closed(value, keys):
    require(type(value) is dict and set(value) == set(keys.split()), 'closed schema: ' + keys)


def natural(n):
    require(type(n) is int and n >= 0, 'natural number required')
    return n


class Unsupported(ValueError):
    pass


def source_identity():
    paths = [*sorted((ROOT/'ClaferCompiler').rglob('*.lean')),
             *sorted((ROOT/'scripts/comparison').glob('*.py')),
             ROOT/'scripts/oracles/temporal.py', ROOT/'scripts/oracles/temporal_build.py',
             ROOT/'scripts/oracles/oracle.py', ROOT/'scripts/oracles/pr113_protocol.py',
             ROOT/'scripts/oracles/AlloyTemporalBridge.java', ROOT/'scripts/oracles/temporal-profile.json',
             ROOT/'tests/TemporalComparisonNative.lean', ROOT/'tests/test_temporal_comparison.py',
             ROOT/'lean-toolchain', ROOT/'lakefile.toml', ROOT/'lake-manifest.json']
    return {str(p.relative_to(ROOT)): oracle.digest(p) for p in paths}


# [impl->req~compiler-temporal-decode~1]
def candidate_valid(c, doc):
    closed(c, 'version profile root length loop identities frames integerObservations')
    require(c['version'] == 'clafer-behavioral-trace/1' and c['profile'] == 'behavioral-core/1', 'trace profile')
    if c['integerObservations'] != []:
        raise Unsupported('primitive observations unsupported in behavioral-core/1')
    n, loop = natural(c['length']), natural(c['loop'])
    require(0 <= loop < n and type(c['frames']) is list and len(c['frames']) == n, 'lasso shape')
    require(type(c['identities']) is list and c['identities'], 'identity inventory')
    ds = {d['id']: d for d in doc['structure']['declarations']}
    ids = {}
    for row in c['identities']:
        closed(row, 'id type parent')
        i = natural(row['id'])
        require(i not in ids and natural(row['type']) in ds, 'duplicate identity or unknown type')
        require(row['parent'] is None or type(row['parent']) is int, 'parent identity')
        ids[i] = row
    require(natural(c['root']) in ids, 'root identity')
    require(all(r['parent'] is None or r['parent'] in ids for r in ids.values()), 'unknown parent')
    for f in c['frames']:
        closed(f, 'live references')
        require(type(f['live']) is list and all(type(x) is int and x in ids for x in f['live']), 'live identities')
        require(len(set(f['live'])) == len(f['live']), 'duplicate live identity')
        require(type(f['references']) is list, 'reference rows')
        for row in f['references']:
            require(type(row) is list and len(row) == 3 and all(type(x) is int for x in row), 'reference tuple')
            d, x, y = row
            require(d in ds and x in ids and y in ids, 'reference endpoint')
        require(len(set(map(tuple, f['references']))) == len(f['references']), 'duplicate reference row')
    return ids, ds


def ancestors(ds, d):
    result = []
    while d is not None:
        require(d not in result, 'super cycle')
        result.append(d)
        d = ds[d]['super']
    return result


def compiler_trace(c, doc, product):
    ids, ds = candidate_valid(c, doc)
    maps = {d['id']: d for d in product['declarations']}
    names = {x: 'object_' + str(x) for x in ids}
    sigs = {s: [] for s in product['signatures']}
    sigs['this/cc0'] = [[names[x]] for x in ids]
    for x, row in ids.items():
        for d in ancestors(ds, row['type']):
            sigs[maps[d]['signature']].append([names[x]])
    parent = [[names[x], names[r['parent']]] for x,r in ids.items() if r['parent'] is not None]
    root_sig = maps[doc['structure']['root']]['signature']
    frames = []
    for frame in c['frames']:
        fields = {f: [] for f in product['fields']}
        fields['this/cc0/cc1'] = parent
        fields[root_sig + '/cc5'] = [[names[c['root']], names[x]] for x in frame['live']]
        for d,x,y in frame['references']:
            symbol = maps[d]['referenceField']
            require(symbol is not None, 'reference on basic declaration')
            fields[symbol].append([names[x], names[y]])
        frames.append(dict(signatures=copy.deepcopy(sigs), fields=fields))
    return dict(length=c['length'], loop=c['loop'], inventory=sorted(names.values()), frames=frames,
                signatures=product['signatures'], fields=product['fields'])


def graph(c):
    """Embed the whole observation in the existing exact graph-isomorphism API."""
    members = [['type:'+str(r['type']), r['id']] for r in c['identities']]
    members += [[f'live:{t}', x] for t,f in enumerate(c['frames']) for x in f['live']]
    return dict(objects=[r['id'] for r in c['identities']], root=c['root'], members=members,
        containment=[['parent',[r['id'],r['parent']]] for r in c['identities'] if r['parent'] is not None],
        references=[[f'ref:{t}:{d}', [x,y]] for t,f in enumerate(c['frames']) for d,x,y in f['references']])


def isomorphism(left, right):
    if (left['length'],left['loop']) != (right['length'],right['loop']):
        return None
    return importlib.import_module('relation').isomorphism(graph(left),graph(right))


def symbol(name):
    parts = name.split('/')
    require(parts[0] == 'this' and len(parts) in (2,3) and
            all(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*', x) for x in parts[1:]), 'unsafe Alloy symbol')
    return ('@' if len(parts) == 3 else '') + parts[-1]


# [impl->req~compiler-temporal-comparison~1]
def pin(trace, *, integer_fields=(), typed_aliases=False, positions=False):
    """Frozen global aliases plus a distinct phase for every stored position.

    With exactly N steps, initial phase zero and the specified successor graph,
    the Analyzer loop must close to precisely the requested loop position.
    """
    n, loop = trace['length'], trace['loop']
    aliases = {a: 'tc_object_'+str(i) for i,a in enumerate(trace['inventory'])}
    require(aliases, 'nonempty candidate pool')
    require(all(not symbol(s).lstrip('@').startswith('tc_') for kind in ('signatures','fields') for s in trace[kind]),
            'reserved exact-trace namespace')
    declarations = 'abstract sig tc_Phase {}\n' + '\n'.join(f'one sig tc_phase{i} extends tc_Phase {{}}' for i in range(n))
    declarations += '\none sig tc_Clock { var tc_now: one tc_Phase }\n'
    equations = ['tc_Clock.tc_now = tc_phase0']
    for i in range(n):
        successor = i+1 if i+1<n else loop
        equations.append(f'always (tc_Clock.tc_now = tc_phase{i} implies after tc_Clock.tc_now = tc_phase{successor})')
        rows = []
        for kind in ('signatures','fields'):
            for name, tuples in trace['frames'][i][kind].items():
                empty = 'none' if kind == 'signatures' else 'none->none'
                def atom(i, x):
                    if name in integer_fields and i == 1:
                        require(type(x) is str and re.fullmatch(r'0|-?[1-9][0-9]*', x),
                                'noncanonical scalar integer')
                        return '(' + x + ')'
                    return aliases[x]
                value = ' + '.join('->'.join(atom(j, x) for j,x in enumerate(row)) for row in tuples) or empty
                rows.append(f'{symbol(name)} = ({value})')
        prefix=('after '*i+'((' if positions else f'always (tc_Clock.tc_now = tc_phase{i} implies (')
        equations.append(prefix+'\n'+'\nand\n'.join(rows)+'\n))')
    universe = ' + '.join(symbol(s) for s in trace['signatures'])
    if typed_aliases:
        # These memberships follow from the fixed initial signature equations.
        # Restricting each binder avoids enumerating irrelevant type permutations.
        binders=[]
        for atom, alias in aliases.items():
            choices=[s for s,rows in trace['frames'][0]['signatures'].items()
                     if not trace['signatures'][s]['mutable'] and [atom] in rows]
            require(choices, 'no static alias domain')
            selected=min(choices,key=lambda s:(len(trace['frames'][0]['signatures'][s]),s))
            binders.append(f'some {alias}: {symbol(selected)} | ')
        equations += [f'{a} != {b}' for i,a in enumerate(aliases.values())
                      for b in list(aliases.values())[i+1:]]
        fact='\nfact { '+''.join(binders)+'{\n'
    else:
        fact = '\nfact { some disj ' + ', '.join(aliases.values()) + ': ('+universe+') | {\n'
    fact += '\nand\n'.join(equations) + '\n} }\n'
    scopes = {'this/tc_Phase':dict(count=n,exact=True),'this/tc_Clock':dict(count=1,exact=True)}
    scopes.update({f'this/tc_phase{i}':dict(count=1,exact=True) for i in range(n)})
    return declarations + fact, scopes


def project_clock(trace, expected):
    """Reject a solver result with the wrong loop or phase, then remove auxiliaries."""
    require((trace['length'],trace['loop']) == (expected['length'],expected['loop']), 'solver changed exact lasso')
    n=trace['length']
    extra_sigs={'this/tc_Phase','this/tc_Clock',*[f'this/tc_phase{i}' for i in range(n)]}
    require(set(trace['signatures']) == set(expected['signatures']) | extra_sigs, 'unknown signature')
    require(set(trace['fields']) == set(expected['fields']) | {'this/tc_Clock/tc_now'}, 'unknown field')
    require({s:trace['signatures'][s] for s in expected['signatures']} == expected['signatures'], 'signature metadata')
    require({s:trace['fields'][s] for s in expected['fields']} == expected['fields'], 'field metadata')
    frames=[]
    for i, frame in enumerate(trace['frames']):
        clock=frame['signatures']['this/tc_Clock']
        phase=frame['signatures'][f'this/tc_phase{i}']
        require(len(clock)==len(phase)==1 and frame['fields']['this/tc_Clock/tc_now']==[[clock[0][0],phase[0][0]]], 'wrong clock phase')
        frames.append(dict(signatures={s:frame['signatures'][s] for s in expected['signatures']},
                           fields={f:frame['fields'][f] for f in expected['fields']}))
    inventory=sorted({a for f in frames for rs in f['signatures'].values() for row in rs for a in row})
    return dict(length=n,loop=trace['loop'],inventory=inventory,frames=frames,
                signatures=expected['signatures'],fields=expected['fields'])


def haskell_declarations(value):
    result={}
    def walk(elements):
        for e in elements:
            if e['tag']=='IEClafer':
                d=e['_iClafer']; u=d['_uid']
                require(u not in result, 'duplicate Haskell UID')
                result[u]=d
                walk(d['_elements'])
            else:
                require(e['tag']=='IEConstraint' and e['_isHard'], 'unsupported Haskell declaration')
    walk(value['iModule']['_mDecls'])
    return result


def reference_path(node):
    e=node['_exp']
    if e['tag']=='IClaferId':
        require(e['_binding']==dict(tag='GlobalBind',contents=e['_sident']) and e['_modName']=='',
                'unresolved reference target')
        return [e['_sident']]
    require(e['tag']=='IFunExp' and e['_op']=='.' and len(e['_exps'])==2, 'unsupported reference target path')
    return reference_path(e['_exps'][0])+reference_path(e['_exps'][1])


def haskell_layout(doc, generation, uids):
    """One checked compiler-ID/paired-Haskell-UID map for every stored frame."""
    require(generation['schema']=='clafer-temporal-generation/1' and generation['status']=='captured' and
            generation['backend']=='tmp.als', 'historical paired capture required')
    rows=haskell_declarations(json.loads(generation['json'],object_pairs_hook=unique))
    ds={d['id']:d for d in doc['structure']['declarations']}
    root=doc['structure']['root']
    require(set(uids)==set(map(str,ds)) and uids[str(root)]=='root', 'complete explicit UID mapping required')
    require(set(uids.values())==set(rows)|{'root'} and len(set(uids.values()))==len(uids), 'UID map not bijective')
    names={int(k):v for k,v in uids.items()}
    signatures={'this/root':dict(mutable=False,parent='univ',abstract=False)}
    fields={}
    for id,d in ds.items():
        if id==root: continue
        u=names[id]; r=rows[u]
        require(re.fullmatch('[A-Za-z_][A-Za-z_0-9]*',u) is not None, 'unsupported historical Alloy UID')
        require(r['_ident']==d['name'] and r['_parentUID']==names.get(d['parent'],'clafer'), 'declaration/parent mismatch')
        require(r['_modifiers']==dict(_abstract=d['isAbstract'],_initial=False,_final=False,_finalReference=None), 'unsupported modifiers')
        require(r['_card']==[d['localBounds']['lower'], -1 if d['localBounds']['upper']=='*' else d['localBounds']['upper']] and
                r['_gcard']['_interval']==[d['groupBounds']['lower'],-1 if d['groupBounds']['upper']=='*' else d['groupBounds']['upper']], 'effective cardinality mismatch')
        # Guarded direct concrete declarations form the current common exporter domain.
        # Richer inherited mappings need their own receipt adapter; never guess them.
        if d['super'] is not None or d['isAbstract'] or d['parent'] is None:
            raise Unsupported('unsupported Haskell inheritance mapping')
        require(r['_super'] is None, 'unexpected Haskell super')
        signatures['this/'+u]=dict(mutable=False,parent='univ',abstract=False)
        fields[f'this/{u}/p_{u}']=dict(mutable=False,arity=2)
        fields[f'this/{names[d["parent"]]}/r_{u}']=dict(mutable=True,arity=2)
        ref=r['_reference']
        if d['reference']['kind']=='basic': require(ref is None,'reference mismatch')
        else:
            require(ref is not None and ref['_isSet']==(d['reference']['kind']=='set'), 'reference mode mismatch')
            path=[];target=d['reference']['target']
            while target!=root:
                require(target is not None and names[target] not in path,'invalid target ancestry')
                path.insert(0,names[target]);target=ds[target]['parent']
            require(ref['_refModifier'] is None and reference_path(ref['_ref'])==path, 'reference target mismatch')
            fields[f'this/{u}/{u}_ref']=dict(mutable=True,arity=2)
    return dict(names=names,signatures=signatures,fields=fields)


def haskell_trace(c, doc, layout):
    ids,ds=candidate_valid(c,doc)
    names=layout['names']; labels={x:'object_'+str(x) for x in ids}
    sigs={'this/'+names[d]:[[labels[x]] for x,r in ids.items() if r['type']==d] for d in ds}
    frames=[]
    for frame in c['frames']:
        fields={f:[] for f in layout['fields']}
        live=set(frame['live'])
        for x,r in ids.items():
            d=r['type']; u=names[d]
            if d==doc['structure']['root']: continue
            if r['parent'] is not None:
                fields[f'this/{u}/p_{u}'].append([labels[x],labels[r['parent']]])
                if x in live:
                    fields[f'this/{names[ds[d]["parent"]]}/r_{u}'].append([labels[r['parent']],labels[x]])
        for d,x,y in frame['references']:
            u=names[d];fields[f'this/{u}/{u}_ref'].append([labels[x],labels[y]])
        frames.append(dict(signatures=copy.deepcopy(sigs),fields=fields))
    return dict(length=c['length'],loop=c['loop'],inventory=sorted(labels.values()),frames=frames,
                signatures=layout['signatures'],fields=layout['fields'])


def to_compiler_trace(trace, doc, product, layout):
    """Translate actual Haskell observations without evaluating source constraints."""
    names=layout['names']; maps={d['id']:d for d in product['declarations']}
    frames=[]
    for f in trace['frames']:
        sigs={s:[] for s in product['signatures']};sigs['this/cc0']=[[x] for x in trace['inventory']]
        fields={s:[] for s in product['fields']}
        root=f['signatures']['this/root']
        require(len(root)==1, 'Haskell root')
        live=[root[0][0]]
        for d in doc['structure']['declarations']:
            id=d['id'];u=names[id]
            sigs[maps[id]['signature']]=f['signatures']['this/'+u]
            if id==doc['structure']['root']: continue
            fields['this/cc0/cc1'] += f['fields'][f'this/{u}/p_{u}']
            live += [row[1] for row in f['fields'][f'this/{names[d["parent"]]}/r_{u}']]
            if maps[id]['referenceField']:
                fields[maps[id]['referenceField']]=f['fields'][f'this/{u}/{u}_ref']
        fields[maps[doc['structure']['root']]['signature']+'/cc5']=[[root[0][0],x] for x in live]
        frames.append(dict(signatures=sigs,fields=fields))
    return dict(trace,frames=frames,signatures=product['signatures'],fields=product['fields'])


class Runtime:
    def __init__(self, tools, directory):
        self.directory=oracle.external(directory);self.directory.mkdir(parents=True,exist_ok=False)
        self.tools_path=str(oracle.external(tools));self.tools=temporal.load_tools(tools)
        self.source=source_identity()
        oracle.write(self.directory/'source.json',self.source)
        for name in self.source:
            dest=self.directory/'source'/name;dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/name,dest)
        self.compiler=ROOT/'.lake/build/bin/clafer-compiler'
        def command(name,args,timeout=120):
            run(args,self.directory,name,timeout=timeout)
            return (self.directory/(name+'-stdout.log')).read_text()
        module='tests.TemporalComparisonNative'
        command('compiler-build',['lake','build','clafer-compiler'],240)
        modules=[module,*json.loads(command('native-imports',['lake','query','--json','+'+module+':transImports']))]
        objects=[json.loads(line) for line in command('native-objects',['lake','query','--json',*[f'+{m}:o.export' for m in modules]],240).splitlines()]
        harness=self.directory/'Harness.lean'
        harness.write_text('import tests.TemporalComparisonNative\ndef main (args : List String) : IO Unit := ClaferCompiler.Tests.TemporalComparison.run args\n')
        c=self.directory/'Harness.c';self.native=self.directory/'temporal-check'
        command('native-compile',['lake','env','lean',f'--root={self.directory}','-c',c,harness])
        command('native-link',['lake','env','leanc',c,*objects,'-o',self.native])
        self.identity=dict(compiler=oracle.digest(self.compiler),checker=oracle.digest(self.native),
            tools=self.tools['tools'],haskell_profile=temporal_build.profile(),
            sources=self.source,semantics=json.loads((ROOT/'lake-manifest.json').read_text())['packages'][0]['rev'])
        oracle.write(self.directory/'runtime.json',self.identity)

    def check(self, directory, trace, name):
        oracle.write(directory/(name+'-trace.json'),trace)
        run([self.native,directory/'input.json',directory/(name+'-trace.json')],directory,name,timeout=45)
        return temporal.read(directory/(name+'-stdout.log'))

    def compile(self, directory, doc, bounds):
        oracle.write(directory/'input.json',doc);oracle.write(directory/'bounds.json',bounds)
        try:
            run([self.compiler,'compile-behavioral-ir',directory/'input.json','--bounds',directory/'bounds.json',
                 '--output',directory/'compilation.json','--format','json','--diagnostics','json'],directory,'compile')
        except subprocess.CalledProcessError as e:
            if e.returncode in (2,3):
                diagnostic=temporal.read(directory/'compile-stderr.log')
                error=Unsupported if e.returncode==3 else ValueError
                raise error(diagnostic['code']+': '+diagnostic['message']) from e
            raise
        return temporal.read(directory/'compilation.json')

    def capture(self, directory, source):
        (directory/'input.cfr').write_text(source)
        run([self.tools['exporter'],directory/'input.cfr'],directory,'capture',timeout=30)
        g=temporal.read(directory/'capture-stdout.log')
        oracle.write(directory/'generation.json',g)
        if g['status']=='unsupported':raise Unsupported(g.get('detail','Haskell input unsupported'))
        require(g['status']=='captured',g.get('detail','Haskell capture did not complete'))
        return g

    def solve(self, directory, text, trace, scopes, width):
        directory.mkdir()
        fixation,ghost_scopes=pin(trace)
        (directory/'model.als').write_text(text+'\n'+fixation)
        oracle.write(directory/'fixed-trace.json',trace)
        request=dict(command_index=0,overall=1,bitwidth=width,min_steps=trace['length'],max_steps=trace['length'],
                     identities=scopes|ghost_scopes)
        result=temporal.solve(self.tools['runtime'],self.tools['api'],directory,request,timeout=30)
        oracle.write(directory/'result.json',result)
        return result

    # [impl->req~compiler-temporal-comparison~1]
    def compare(self, case, directory, *, mutation='none'):
        directory=oracle.external(directory);directory.mkdir(parents=True,exist_ok=False)
        oracle.write(directory/'case.json',case)
        oracle.write(directory/'runtime.json',self.identity)
        oracle.write(directory/'settings.json',dict(mutation=mutation))
        result=dict(status='error',directions=[])
        try:
            require(source_identity()==self.source and oracle.digest(self.compiler)==self.identity['compiler'] and
                    oracle.digest(self.native)==self.identity['checker'],'runtime sources or binaries changed')
            closed(case,'version document bounds source uids candidate seed')
            require(case['version']=='clafer-temporal-case/1','case version')
            natural(case['seed'])
            require(mutation in ('none','reject-all','drop-attachments'),'unknown sensitivity mutation')
            doc,bounds,c=case['document'],case['bounds'],case['candidate']
            candidate_valid(c,doc)
            product=self.compile(directory,doc,bounds)
            trace=compiler_trace(c,doc,product)
            checked=self.check(directory,trace,'source')
            oracle.write(directory/'source-result.json',checked)
            if checked['status'] not in ('satisfied','violated'):
                result=dict(status=checked['status'],directions=[])
            else:
                require(isomorphism(c,checked['trace']) is not None,'native decode changed candidate')
                require(product['minSteps']<=c['length']<=product['maxSteps'],'candidate outside requested step bounds')
                for name,scope in product['scopes'].items():
                    count=len(trace['frames'][0]['signatures'][name])
                    require(count<=scope['count'] and (not scope['exact'] or count==scope['count']), 'candidate outside identity bounds')
                g=self.capture(directory,case['source'])
                layout=haskell_layout(doc,g,case['uids'])
                oracle.write(directory/'haskell-layout.json',layout)
                ht=haskell_trace(c,doc,layout)
                compiler_text=product['alloy']
                if mutation=='reject-all':compiler_text+='\nfact { no univ }\n'
                if mutation=='drop-attachments':
                    mutated=copy.deepcopy(doc);mutated['attachments']=[]
                    md=directory/'mutation';md.mkdir()
                    compiler_text=self.compile(md,mutated,bounds)['alloy']
                # The historical explicit root is intrinsically live. Fixing its
                # absence is impossible, not permission to substitute a live root.
                haskell_text=g['alloy']
                if any(c['root'] not in f['live'] for f in c['frames']):
                    haskell_text+='\nfact { no root }\n'
                hs={f'this/{layout["names"][d["id"]]}':dict(count=d['size'],exact=d['exact']) for d in bounds['declarations']}
                targets={
                    'compiler':self.solve(directory/'compiler',compiler_text,trace,product['scopes'],product['bitwidth']),
                    'haskell':self.solve(directory/'haskell',haskell_text,ht,hs,product['bitwidth'])}
                complete=True;directions=[]
                for name,answer in targets.items():
                    if answer['status']!='ok': complete=False;continue
                    accepted=answer['outcome']=='sat'
                    if accepted:
                        observed=project_clock(answer['trace'],trace if name=='compiler' else ht)
                        if name=='haskell':observed=to_compiler_trace(observed,doc,product,layout)
                        decoded=self.check(directory,observed,name+'-witness')
                        require(decoded['status'] in ('satisfied','violated') and isomorphism(c,decoded['trace']) is not None,
                                'SAT witness differs from the fixed candidate')
                    if accepted != (checked['status']=='satisfied'):
                        directions.append(name+':'+('target-only' if accepted else 'source-only'))
                result=dict(status='complete' if complete else 'inconclusive',source=checked['status'],
                    targets={name:dict(status=r['status'],outcome=r.get('outcome')) for name,r in targets.items()},
                    directions=directions,haskell_profile=temporal_build.profile()['profile'])
        except Unsupported as e:
            result=dict(status='unsupported',detail=str(e),directions=[])
        except subprocess.TimeoutExpired as e:
            result=dict(status='timeout',detail=str(e),directions=[])
        except (ValueError,KeyError,TypeError) as e:
            result=dict(status='malformed',detail=str(e),directions=[])
        except TimeoutError as e:
            result=dict(status='timeout',detail=str(e),directions=[])
        except (OSError,subprocess.CalledProcessError) as e:
            result=dict(status='error',detail=str(e),directions=[])
        oracle.write(directory/'result.json',result)
        oracle.write(directory/'evidence-index.json',{str(p.relative_to(directory)):oracle.digest(p)
            for p in sorted(directory.rglob('*')) if p.is_file()})
        return result


def validate_bundle(bundle):
    bundle=oracle.external(bundle)
    actual={str(p.relative_to(bundle)):oracle.digest(p) for p in sorted(bundle.rglob('*'))
            if p.is_file() and p!=bundle/'evidence-index.json'}
    require(actual==temporal.read(bundle/'evidence-index.json'),'changed replay artifact inventory')
    identity=temporal.read(bundle/'runtime.json')
    require(identity['sources']==source_identity(),'changed compiler/harness sources')
    return identity


def replay_case(runtime,bundle,output):
    require(runtime.identity==validate_bundle(bundle),'changed compiler/checker/tool identity')
    result=runtime.compare(temporal.read(bundle/'case.json'),output,**temporal.read(bundle/'settings.json'))
    require(result==temporal.read(bundle/'result.json'),'replayed outcomes differ')
    return result


def replay(tools, bundle, output):
    bundle=oracle.external(bundle)
    validate_bundle(bundle)
    runtime=Runtime(tools,Path(output)/'runtime')
    return replay_case(runtime,bundle,Path(output)/'case')


def reductions(case):
    """Single live/reference-row deletions at the original identity/step bounds."""
    for t,frame in enumerate(case['candidate']['frames']):
        for field in ('live','references'):
            for i in range(len(frame[field])):
                smaller=copy.deepcopy(case)
                del smaller['candidate']['frames'][t][field][i]
                yield smaller


# [impl->req~compiler-temporal-comparison~1]
def minimize(runtime,bundle,output):
    bundle=oracle.external(bundle);output=oracle.external(output)
    output.mkdir(parents=True,exist_ok=False)
    initial=replay_case(runtime,bundle,output/'initial')
    require(initial['status']=='complete' and initial['directions'],'minimization requires a completed discrepancy')
    current=temporal.read(bundle/'case.json');settings=temporal.read(bundle/'settings.json')
    attempts=0
    while True:
        for smaller in reductions(current):
            attempts+=1
            trial=runtime.compare(smaller,output/f'trial-{attempts}',**settings)
            if trial['status']!='complete':
                result=dict(status='inconclusive',deletion_minimal=False,attempts=attempts,last=trial)
                oracle.write(output/'result.json',result)
                return result
            if trial['directions']==initial['directions']:
                current=smaller
                break
        else:break
    final=runtime.compare(current,output/'minimal',**settings)
    require(final['status']=='complete' and final['directions']==initial['directions'],'final replay lost discrepancy')
    result=dict(status='complete',directions=final['directions'],deletion_minimal=True,attempts=attempts,
                reductions='one live or reference row; fixed identities, frames, loop and bounds')
    oracle.write(output/'result.json',result)
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=['run','replay','minimize'])
    p.add_argument('input',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--tools',required=True,type=Path)
    args=p.parse_args()
    if args.command=='replay':result=replay(args.tools,args.input,args.output)
    else:
        runtime=Runtime(args.tools,args.output/'runtime')
        result=(minimize(runtime,args.input,args.output/'reduction') if args.command=='minimize' else
                runtime.compare(temporal.read(args.input),args.output/'case'))
    print(json.dumps(result,sort_keys=True))
    return 0 if result['status']=='complete' and (result.get('deletion_minimal') or not result['directions']) else 1

if __name__=='__main__':
    raise SystemExit(main())
