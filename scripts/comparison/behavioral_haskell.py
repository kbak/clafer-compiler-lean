"""Revision-qualified exact observations for the selected PR113 source pairing.

The existing generation/inspection adapter owns UID and field-type validation.
Only source models/checks are paired here; scenario composition is tested by the
compiler source harness. No normalized explicit-source workflow is selected.
"""
import argparse
import copy
from pathlib import Path
import importlib
import json
import behavioral_source as bs
import pr113
import pr113_protocol as protocol

tc,oracle,temporal=bs.tc,bs.oracle,bs.temporal


def pairing(p,g,inspected):
    rows=protocol.layout(g,inspected)
    ds={d['id']:d for d in p['declarations'] if not d['primitive']}
    names={p['root']:'root'}
    # Match unique authored names and lexical ownership; ambiguous names fail.
    pending={d for d in ds if d!=p['root']}
    while pending:
        matched=[]
        for d in pending:
            row=ds[d]
            if row['parent'] is not None and row['parent'] not in names:continue
            parent='clafer' if row['parent'] is None else names[row['parent']]
            choices=[u for u,r in rows.items() if r['_ident']==row['name'] and r['_parentUID']==parent]
            tc.require(len(choices)==1,'ambiguous source declaration mapping')
            names[d]=choices[0];matched.append(d)
        tc.require(matched,'cyclic source ownership');pending.difference_update(matched)
    tc.require(set(names.values())==set(rows)|{'root'} and len(set(names.values()))==len(names),'incomplete source bijection')
    primitive=next(d['id'] for d in p['declarations'] if d['primitive'])
    for d,row in ds.items():
        if d==p['root']:continue
        h=rows[names[d]]
        tc.require(h['_modifiers']['_abstract']==row['abstract'],'authored abstractness')
        sup=h['_super'];actual=None if sup is None else sup['_exp']['_sident']
        tc.require(actual==names.get(row['super']),'source superclass')
        for key,b in (('_card',row['localBounds']),('_gcard',row['groupBounds'])):
            if key=='_card' and row['parent'] is None:
                # Parentless abstract declarations have no local fiber. Haskell
                # stores 0..* here; the frontend retains its authored default.
                tc.require(row['abstract'] and h[key]==[0,-1],'parentless local card')
                continue
            interval=h[key] if key=='_card' else h[key]['_interval']
            tc.require(interval==[b['lower'],-1 if b['upper'] is None else b['upper']],'effective cardinality pairing')
        ref=h['_reference']
        if row['reference']['kind']=='basic':tc.require(ref is None,'unexpected reference')
        else:
            tc.require(ref is not None and ref['_isSet']==(row['reference']['kind']=='set'),'reference mode')
            target=row['reference']['target']
            expected=['Int'] if target==primitive else ['this/'+g['names'][names[target]]]
            tc.require(protocol.reference_targets(ref['_ref'],rows,g['names'])==expected,'reference target')
    alloy={d:('root' if u=='root' else g['names'][u]) for d,u in names.items()}
    return ds,names,alloy


def target(c,p,g,inspected):
    ids,_=bs.candidate_valid(c,p);ds,names,alloy=pairing(p,g,inspected)
    primitive=next(d['id'] for d in p['declarations'] if d['primitive'])
    labels={x:'object_'+str(x) for x in ids}
    signatures={s:dict(mutable=False,parent=r['parent'],abstract=r['abstract']) for s,r in inspected['signatures'].items()}
    fields={f:dict(mutable=r['mutable'],arity=r['arity']) for f,r in inspected['fields'].items()}
    sigs={'this/'+alloy[d]:[[labels[x]] for x,r in ids.items() if d in tc.ancestors(ds,r['type'])] for d in ds}
    scalar=[];frames=[]
    for f in c['frames']:
        table={s:[] for s in fields};live=set(f['live']);zs=dict(f['values'])
        for d,row in ds.items():
            if d==p['root']:continue
            u=alloy[d];heads=[x for x,r in ids.items() if d in tc.ancestors(ds,r['type'])]
            parent=alloy.get(row['parent'],'root')
            forward=f'this/{parent}/r_{u}';back=f'this/{u}/p_{u}';ref=f'this/{u}/{u}_ref'
            for x in heads:
                par=ids[x]['parent']
                if back in table and par is not None:table[back].append([labels[x],labels[par]])
                if forward in table and x in live and par is not None:table[forward].append([labels[par],labels[x]])
            if ref in table:
                if row['reference']['target']==primitive:
                    table[ref]=[[labels[x],str(zs[x])] for x in heads if x in live]
                    if ref not in scalar:scalar.append(ref)
                else:table[ref]=[[labels[x],labels[y]] for decl,x,y in f['references'] if decl==d]
        frames.append(dict(signatures=copy.deepcopy(sigs),fields=table))
    return dict(length=c['length'],loop=c['loop'],inventory=sorted(labels.values()),frames=frames,
                signatures=signatures,fields=fields),scalar,alloy,names


def graph(t,scalar):
    members=[[f'sig:{i}:{s}',row[0]] for i,f in enumerate(t['frames']) for s,rs in f['signatures'].items() for row in rs]
    members += [[f'value:{i}:{s}:{row[1]}',row[0]] for i,f in enumerate(t['frames'])
                for s,rs in f['fields'].items() if s in scalar for row in rs]
    return dict(objects=t['inventory'],root=t['frames'][0]['signatures']['this/root'][0][0],members=members,
        containment=[],references=[[f'field:{i}:{s}',row] for i,f in enumerate(t['frames'])
            for s,rs in f['fields'].items() if s not in scalar for row in rs])


# [impl->req~compiler-behavioral-qualification~1]
def compare(runtime,tools,case,output):
    output=oracle.external(output);output.mkdir(parents=True,exist_ok=False)
    oracle.write(output/'case.json',case)
    tc.require(bs.source_identity()==runtime.source and oracle.digest(runtime.compiler)==runtime.identity['compiler'] and
               oracle.digest(runtime.native)==runtime.identity['decoder'],'runtime changed')
    tc.closed(case,'version source query bounds candidate')
    tc.require(case['version']=='clafer-behavioral-source-case/1','case version')
    p=runtime.compile(output,case);c=case['candidate']
    bs.within_bounds(c,p,case['bounds'])
    tc.require(case['query']['kind'] in ('model','check'),'Haskell scenario pairing not selected')
    g=pr113.capture(tools,{'input.cfr':case['source'].encode()},'input.cfr',output/'capture')
    tc.require(g['status']=='captured','Haskell capture failed')
    inspected=pr113.inspect(tools,g,output/'capture')
    trace,scalar,alloy,names=target(c,p,g,inspected)
    oracle.write(output/'source-map.json',dict(uids=names,alloy=alloy))
    oracle.write(output/'expected-trace.json',trace)
    fixture,clock=tc.pin(trace,integer_fields=scalar,typed_aliases=True)
    directory=output/'haskell';directory.mkdir()
    (directory/'model.als').write_text(g['alloy']+'\n'+fixture)
    index=0
    if case['query']['kind']=='check':
        label=pr113.assertions(g)[case['query']['assertion']]
        index=next(i for i,x in enumerate(inspected['commands']) if x['label']==label)
    request=dict(command_index=index,overall=1,bitwidth=p['bitwidth'],min_steps=c['length'],max_steps=c['length'],
        identities={**{'this/'+alloy[b['id']]:dict(count=b['size'],exact=b['exact'])
            for b in case['bounds']['declarations']},**clock})
    result=temporal.solve(tools['runtime'],tools['api'],directory,request,timeout=60,integer_fields=scalar)
    oracle.write(directory/'result.json',result)
    tc.require(result['status']=='ok','inconclusive Haskell solver: '+str(result))
    if result['outcome']=='sat':
        actual=tc.project_clock(result['trace'],trace)
        tc.require(importlib.import_module('relation').isomorphism(graph(trace,scalar),graph(actual,scalar)) is not None,
                   'Haskell SAT witness differs from fixed observation')
    source=bs.Observation(p,c).check()
    answer=dict(profile=tools['tools']['profile']['profile'],source=source['status'],target=result['outcome'],
        directions=[] if (result['outcome']=='sat')==(source['status']=='satisfied') else
            ['target-only' if result['outcome']=='sat' else 'source-only'])
    oracle.write(output/'runtime.json',dict(compiler=runtime.identity,haskell=tools['tools']))
    oracle.write(output/'result.json',answer)
    pr113.index(output)
    return answer


def replay(runtime,tools,bundle,output):
    bundle=oracle.external(bundle)
    actual={str(p.relative_to(bundle)):oracle.digest(p) for p in sorted(bundle.rglob('*'))
            if p.is_file() and p!=bundle/'evidence-index.json'}
    tc.require(actual==temporal.read(bundle/'evidence-index.json'),'changed Haskell replay inventory')
    tc.require(temporal.read(bundle/'runtime.json')==dict(compiler=runtime.identity,haskell=tools['tools']),
               'changed Haskell replay runtime')
    result=compare(runtime,tools,temporal.read(bundle/'case.json'),output)
    tc.require(result==temporal.read(bundle/'result.json'),'changed Haskell replay result')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('run','replay'))
    parser.add_argument('input',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--tools',required=True,type=Path)
    parser.add_argument('--haskell-tools',required=True,type=Path)
    args=parser.parse_args();runtime=bs.Runtime(args.tools,args.output/'runtime')
    tools=pr113.load_tools(args.haskell_tools)
    tc.require(tools['tools']['profile']['profile']=='behavioral-pr113-c7a2fb7/v1','Haskell profile')
    result=(replay(runtime,tools,args.input,args.output/'case') if args.command=='replay' else
            compare(runtime,tools,temporal.read(args.input),args.output/'case'))
    print(json.dumps(result,sort_keys=True))
    return 1 if result['directions'] else 0


if __name__=='__main__': raise SystemExit(main())
