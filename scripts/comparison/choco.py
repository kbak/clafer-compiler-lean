#!/usr/bin/env python3
"""Check actual Choco instances through the existing guarded structural protocol."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET

import compare
import choco_build

oracle = compare.oracle
ROOT = oracle.ROOT
FIXTURES = ROOT/'tests/fixtures/choco'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def identity():
    paths = [Path(__file__), Path(choco_build.__file__), Path(__file__).with_name('ChocoInstances.java'),
             Path(__file__).with_name('ExplicitExport.hs'), ROOT/'tests/test_choco_instances.py',
             *sorted(FIXTURES.glob('*'))]
    return dict(compare.source_identity(), **{str(p.relative_to(ROOT)): oracle.digest(p) for p in paths})


def seal(output):
    oracle.write(output/'manifest.json', {str(p.relative_to(output)): oracle.digest(p)
        for p in sorted(output.rglob('*')) if p.is_file() and p != output/'manifest.json'})


def verify(output):
    recorded = json.loads((output/'manifest.json').read_text())
    observed = {str(p.relative_to(output)): oracle.digest(p)
        for p in sorted(output.rglob('*')) if p.is_file() and p != output/'manifest.json'}
    require(recorded == observed, 'Replay bundle identity changed')


class Runtime:
    def __init__(self, tools, directory):
        self.tools_path = oracle.external(tools)
        self.tools = choco_build.load(self.tools_path)
        self.directory = self.tools_path.parent
        self.comparison = compare.Runtime(self.tools['static_tools'], directory)
        self.api = self.comparison.api
        self.source = identity()


def attributes(element, tag, keys):
    require(element.tag == tag and set(element.attrib) == set(keys.split()), 'Malformed '+tag+' attributes')
    require(not (element.text or '').strip() and not (element.tail or '').strip(), 'Unexpected XML text')
    return element.attrib


def number(text, minimum=0):
    require(isinstance(text, str) and text == str(int(text)) and int(text) >= minimum, 'Invalid numeric field')
    return int(text)


# [impl->req~compiler-choco-instances~1]
def envelope(raw, core, bounds):
    require(b'<!DOCTYPE' not in raw and b'<!ENTITY' not in raw, 'XML declarations forbidden')
    tree = ET.fromstring(raw)
    attrs = attributes(tree, 'choco-instances', 'schema')
    require(attrs['schema'] == 'clafer-choco-instances/1', 'Wrong instance schema')
    children = list(tree)
    require(len(children) >= 2 and children[0].tag == 'declarations' and children[-1].tag == 'search',
            'Missing declaration/search inventory')
    attributes(children[0], 'declarations', '')
    expected = {d['uid']: d for d in core['declarations']}
    observed = {}
    for element in children[0]:
        a = attributes(element, 'declaration', 'uid parent super abstract cardLow cardHigh groupLow groupHigh mode target scope')
        require(not list(element) and a['uid'] not in observed and a['uid'] in expected, 'Declaration inventory')
        d = expected[a['uid']]
        # The admitted protocol uses its built-in "clafer" UID for a parentless
        # abstract. Choco keeps these under its implicit abstract model root.
        row = dict(parent=a['parent'] or 'clafer', super=a['super'] or None, abstract=a['abstract'],
                   card=[number(a['cardLow']), number(a['cardHigh'], -1)],
                   group=[number(a['groupLow']), number(a['groupHigh'], -1)],
                   mode=a['mode'], target=a['target'] or None, scope=number(a['scope']))
        wanted = {k: d[k] for k in ('parent', 'super', 'card', 'group', 'mode', 'target')}
        wanted.update(abstract=str(d['abstract']).lower(), scope=bounds[d['uid']])
        require(row == wanted, 'Choco declaration differs from admitted core: '+a['uid'])
        observed[a['uid']] = row
    require(set(observed) == set(expected), 'Missing declaration')
    search = attributes(children[-1], 'search', 'generated termination detail')
    require(not list(children[-1]) and search['termination'] in ('exhausted', 'limit', 'insufficient_scope'),
            'Search termination')
    instances = children[1:-1]
    require(number(search['generated']) == len(instances), 'Generated count mismatch')
    require(search['termination'] != 'insufficient_scope' or (not instances and search['detail']),
            'Invalid scope rejection')
    for index, instance in enumerate(instances):
        a = attributes(instance, 'instance', 'index')
        require(number(a['index']) == index, 'Instance sequence')
    return instances, dict(generated=len(instances), termination=search['termination'],
                          generator_detail=search['detail']), observed


# [impl->req~compiler-choco-instances~1]
def decode(instance, core, bounds, relation):
    """Identity is (declaration UID, local ID), including reference heads."""
    declarations = {d['uid']: d for d in core['declarations']}
    objects = {}
    for element in instance:
        a = attributes(element, 'object', 'type id parentType parentId')
        key = (a['type'], number(a['id']))
        require(key[0] in declarations and not declarations[key[0]]['abstract'] and key not in objects,
                'Unknown, abstract or duplicate object identity')
        refs = list(element)
        require(len(refs) <= 1, 'Multiple references')
        target = None
        if refs:
            r = attributes(refs[0], 'reference', 'type id')
            require(not list(refs[0]), 'Nested reference')
            target = (r['type'], number(r['id']))
        objects[key] = ((a['parentType'], number(a['parentId'])), target)
    keys = {('root', 0): 0, **{key: index+1 for index, key in enumerate(sorted(objects))}}
    candidate = dict(objects=list(keys.values()), root=0, members=[['root', 0]], containment=[], references=[])
    for key, (parent, target) in objects.items():
        require(parent in keys and (target is None or target in keys), 'Dangling parent or reference target')
        uid, obj = key[0], keys[key]
        current = uid
        seen = set()
        while current is not None:
            require(current in declarations and current not in seen, 'Invalid super chain')
            seen.add(current)
            candidate['members'].append([current, obj])
            current = declarations[current]['super']
        candidate['containment'].append([uid, [keys[parent], obj]])
        if target is not None:
            candidate['references'].append([uid, [obj, keys[target]]])
    relation.validate_candidate(candidate, core, bounds)
    candidate = relation.canonical(candidate)
    tables = {kind: {uid: [] for uid in ['root', *declarations]} for kind in ('members', 'containment', 'references')}
    for kind in tables:
        for uid, value in candidate[kind]:
            tables[kind][uid].append(value)
    mapping = [dict(uid=u, local_id=i, object=o) for (u,i),o in keys.items()]
    return candidate, mapping, tables


def export(runtime, source, bounds, output):
    p = runtime.api['protocol']
    captured = oracle.capture_case(source, bounds, output/'admission', runtime.api,
                                  runtime.comparison.exporter, runtime.comparison.build)
    if captured['status'] != 'admitted':
        raise p.Rejection(captured['status'], 'source_admission', str(captured))
    bundle = output/'admission/capture'
    core, metadata = p.import_bundle(bundle)
    oracle.write(output/'core.json', core)
    compare.run([runtime.directory/'explicit-export', source, output/'bounds.json'], output, 'explicit', timeout=120)
    g = p.loads((output/'explicit-stdout.log').read_bytes())
    require(g.get('status') == 'captured' and g.get('schema') == 'clafer-choco-explicit/1', 'Explicit generation failed')
    original = p.loads((bundle/'generation.json').read_bytes())
    require(g['bounds'] == bounds, 'Explicit generation bounds differ')
    for key in ('effective_options', 'post_analysis', 'json', 'alloy'):
        require(g[key] == original[key], 'Explicit generation differs from accepted capture: '+key)
    require(g['explicit'].startswith('//# OPTIONS --explicit\n'), 'Missing generated explicit directive')
    scopes = p.loads(g['explicit_scopes'])
    per_uid = [row for row in scopes if 'lpqName' in row]
    require(len(per_uid) == len(bounds)-1 and {row['lpqName']: row['scope'] for row in per_uid}
            == {u:n for u,n in bounds.items() if u != 'root'}, 'Explicit scope inventory differs')
    (output/'explicit.cfr').write_text(g['explicit'])
    (output/'explicit.cfr-scope').write_text(g['explicit_scopes'])
    return core, metadata, bundle


def solve(runtime, output, timeout, limit):
    require(type(timeout) is int and timeout > 0 and type(limit) is int and 1 <= limit <= 1000,
            'Positive timeout and instance limit 1..1000 required')
    java = Path(runtime.tools['java_home'])/'bin/java'
    command = [java, '-Xmx512m', '-Xss1m', '-XX:ActiveProcessorCount=1', '-XX:+UseSerialGC',
        '-cp', os.pathsep.join(map(str, [runtime.directory/'classes', runtime.directory/'chocosolver.jar'])),
        'ChocoInstances', output/'explicit.cfr', output/'explicit.cfr-scope', output/'raw.xml', str(limit)]
    compare.run(command, output, 'choco', timeout=timeout)


# [impl->req~compiler-choco-instances~1]
def run_case(runtime, source, bounds, output, *, supplied=None, timeout=30, limit=10):
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    (output/'input.cfr').write_bytes(Path(source).read_bytes())
    oracle.write(output/'bounds.json', bounds)
    oracle.write(output/'settings.json', dict(timeout=timeout, limit=limit))
    oracle.write(output/'source.json', runtime.source)
    oracle.write(output/'tools.json', runtime.tools)
    oracle.write(output/'supplied.json', supplied or {})
    oracle.write(output/'replay-command.json', ['python3', str(Path(__file__).resolve()), 'replay',
        '--tools', str(runtime.tools_path), str(output), str(output.with_name(output.name+'-replay'))])
    result = dict(schema='clafer-choco-check/1', status='error', generated=None, decoded=0, checked=0,
                  satisfies=0, violates=0, instances=[], supplied={}, termination=None)
    try:
        core, metadata, bundle = export(runtime, output/'input.cfr', bounds, output)
        solve(runtime, output, timeout, limit)
        instances, search, declarations = envelope((output/'raw.xml').read_bytes(), core, bounds)
        result.update(search)
        oracle.write(output/'declarations.json', declarations)
        for index, instance in enumerate(instances):
            directory = output/('instance-'+str(index))
            directory.mkdir()
            observation = dict(status='malformed')
            try:
                candidate, mapping, tables = decode(instance, core, bounds, runtime.comparison.relation)
                result['decoded'] += 1
                oracle.write(directory/'candidate.json', candidate)
                oracle.write(directory/'mapping.json', mapping)
                oracle.write(directory/'tables.json', tables)
                verdict = runtime.comparison.check(core, candidate)
                oracle.write(directory/'checker.json', verdict)
                result['checked'] += 1
                observation = dict(status=verdict['status'])
                if verdict['status'] in ('satisfies', 'violates'):
                    result[verdict['status']] += 1
                    exact = compare.compare(runtime.comparison, bundle, runtime.api['protocol'].encoded(candidate),
                                            directory/'exact')
                    observation['exact'] = exact['category']
                    observation['complete'] = exact['complete']
            except runtime.api['protocol'].Rejection as error:
                observation = dict(status=error.category, detail=str(error))
            except (ValueError, KeyError, TypeError) as error:
                observation['detail'] = str(error)
            result['instances'].append(observation)
            oracle.write(directory/'result.json', observation)
        for label, candidate in (supplied or {}).items():
            require(label and Path(label).name == label and label not in ('.','..'), 'Invalid candidate label')
            exact = compare.compare(runtime.comparison, bundle, runtime.api['protocol'].encoded(candidate),
                                    output/('supplied-'+label))
            result['supplied'][label] = dict(category=exact['category'], complete=exact['complete'])
        result['status'] = 'completed' if (
            all(o.get('complete') and o.get('exact') == 'agree_'+o['status'] for o in result['instances'])
            and all(o['complete'] for o in result['supplied'].values())) else 'inconclusive'
        if result['termination'] == 'insufficient_scope': result['status'] = 'scope_rejected'
    except runtime.api['protocol'].Rejection as error:
        result.update(status=error.category, detail=str(error))
    except subprocess.TimeoutExpired as error:
        result.update(status='timeout', detail=str(error))
    except (OSError, subprocess.SubprocessError) as error:
        result.update(status='error', detail=str(error))
    except (ValueError, KeyError, TypeError, ET.ParseError) as error:
        result.update(status='malformed', detail=str(error))
    oracle.write(output/'result.json', result)
    seal(output)
    return result


def replay(runtime, original, output):
    original = oracle.external(original)
    verify(original)
    p = runtime.api['protocol']
    require(p.loads((original/'source.json').read_bytes()) == runtime.source, 'Replay source changed')
    require(p.loads((original/'tools.json').read_bytes()) == runtime.tools, 'Replay tools changed')
    result = run_case(runtime, original/'input.cfr', p.loads((original/'bounds.json').read_bytes()), output,
        supplied=p.loads((original/'supplied.json').read_bytes()), **p.loads((original/'settings.json').read_bytes()))
    # Replay each retained exact candidate independently of newly generated identities.
    for path in sorted(original.glob('instance-*/exact')):
        exact = compare.replay(runtime.comparison, path, Path(output)/('retained-'+path.parent.name))
        require(exact['complete'], 'Retained exact comparison did not complete')
    seal(Path(output))
    return result


def demonstration(runtime, output):
    output = oracle.external(output)
    output.mkdir(parents=True, exist_ok=False)
    shared = json.loads((FIXTURES/'shared.json').read_text())
    collapsed = copy.deepcopy(shared)
    collapsed['objects'].remove(3)
    collapsed['members'].remove(['refs',3])
    collapsed['containment'].remove(['refs',[0,3]])
    collapsed['references'].remove(['refs',[3,1]])
    missing = copy.deepcopy(shared)
    missing['references'].pop()
    results = {}
    for name in ('bag', 'set', 'set-distinct'):
        supplied = {'shared': shared} if name in ('bag','set') else {}
        if name == 'bag': supplied.update(collapsed=collapsed, missing_reference=missing)
        results[name] = run_case(runtime, FIXTURES/(name+'.cfr'),
            dict(root=1, Target=2 if name == 'set-distinct' else 1, refs=2), output/name, supplied=supplied)
    oracle.write(output/'summary.json', results)
    require(results['bag']['status'] == 'completed' and results['bag']['satisfies'] >= 1
            and results['bag']['violates'] == 0, 'Bag generation/check failed')
    require(results['set']['status'] == 'scope_rejected' and results['set']['generated'] == 0
            and results['set']['termination'] == 'insufficient_scope', 'Expected bounded set scope rejection')
    require(results['set-distinct']['status'] == 'completed' and results['set-distinct']['satisfies'] >= 1
            and results['set-distinct']['violates'] == 0, 'Distinct-target set control failed')
    for name, label, expected in [('bag','shared','agree_satisfies'), ('set','shared','agree_violates'),
                                   ('bag','collapsed','agree_violates'), ('bag','missing_reference','agree_violates')]:
        require(results[name]['supplied'][label] == dict(category=expected, complete=True),
                'Unexpected supplied candidate: '+name+'/'+label)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('demo', 'check', 'replay'):
        p = sub.add_parser(name)
        p.add_argument('--tools', required=True, type=Path)
        if name != 'demo': p.add_argument('input', type=Path)
        if name == 'check': p.add_argument('--bounds', required=True, type=Path)
        p.add_argument('output', type=Path)
    args = parser.parse_args()
    runtime = Runtime(args.tools, args.output.with_name(args.output.name+'-runtime'))
    if args.command == 'demo':
        result = demonstration(runtime, args.output)
    elif args.command == 'replay':
        result = replay(runtime, args.input, args.output)
    else:
        result = run_case(runtime, args.input, runtime.api['protocol'].loads(args.bounds.read_bytes()), args.output)
    print(json.dumps(result, indent=2))
    if args.command != 'demo' and result['status'] != 'completed': return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
