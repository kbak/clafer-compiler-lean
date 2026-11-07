"""Closed PR113 capture boundary; no structural-profile admission is changed."""
import json
import re

import pr113_build


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def closed(value, keys, label):
    require(type(value) is dict and set(value) == set(keys.split()), 'Wrong ' + label + ' schema')


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def modifiers(value):
    require(type(value) is list and all(type(x) is str and x in
        ('FinalRefTarget', 'FinalRef', 'FinalTarget') for x in value), 'Wrong modifier array')


def declarations(im):
    closed(im, '_mName _mDecls', 'module')
    result = {}
    def elements(items):
        require(type(items) is list, 'Element array required')
        for e in items:
            require(type(e) is dict, 'Element object required')
            if e.get('tag') == 'IEClafer':
                closed(e, 'tag _iClafer', 'clafer element')
                c = e['_iClafer']
                closed(c, '_card _cinPos _elements _gcard _glCard _ident _modifiers _parentUID _reference _super _uid', 'declaration')
                u = c['_uid']
                require(type(u) is str and u and u not in result, 'Missing or duplicate UID')
                require(u not in ('root', 'clafer', 'integer', 'int', 'noclafer'), 'Distinguished UID collision')
                require(type(c['_ident']) is str and type(c['_parentUID']) is str, 'Name/parent types')
                m = c['_modifiers']
                closed(m, '_abstract _initial _final _finalReferences', 'modifier-array')
                require(all(type(m[k]) is bool for k in ('_abstract','_initial','_final')), 'Modifier Boolean required')
                modifiers(m['_finalReferences'])
                r = c['_reference']
                if r is not None:
                    closed(r, '_isSet _refModifiers _ref', 'reference-array')
                    require(type(r['_isSet']) is bool, 'Reference Boolean required')
                    modifiers(r['_refModifiers'])
                result[u] = c
                elements(c['_elements'])
            elif e.get('tag') == 'IEConstraint':
                closed(e, 'tag _isHard _cpexp', 'constraint')
                require(type(e['_isHard']) is bool, 'Constraint Boolean required')
            elif e.get('tag') == 'IEGoal':
                closed(e, 'tag _isMaximize _cpexp', 'goal')
            else:
                raise ValueError('Unknown element tag')
    elements(im['_mDecls'])
    require(all(c['_parentUID'] in result or c['_parentUID'] in ('root','clafer')
                for c in result.values()), 'Unknown parent UID')
    return result


def renamed(value, names):
    """Check the whole captured transformation, preserving local binder identities."""
    if isinstance(value, list):
        return [renamed(x, names) for x in value]
    if not isinstance(value, dict):
        return value
    r = {k: renamed(v, names) for k, v in value.items()}
    name = lambda u: names.get(u, u)
    if '_uid' in value:
        r['_uid'], r['_parentUID'] = name(value['_uid']), name(value['_parentUID'])
    if value.get('tag') == 'IClaferId':
        b = value['_binding']
        if b['tag'] == 'GlobalBind':
            r['_sident'] = name(value['_sident'])
            r['_binding']['contents'] = name(b['contents'])
        elif b['tag'] == 'NoBind':
            r['_sident'] = name(value['_sident'])
        else:
            require(b['tag'] == 'LocalBind', 'Unknown binding')
    if value.get('tag') == 'TClafer':
        r['_hi'] = [name(u) for u in value['_hi']]
    return r


# [impl->req~compiler-temporal-oracles~1]
def generation(g):
    closed(g, 'schema compiler_commit effective_options trace_length files post_analysis outputs status backend json alloy explicit explicit_observed explicit_scopes original_scopes scopes backend_input backend_ir backend_alloy names', 'generation')
    require(g['schema'] == 'clafer-pr113-generation/1' and
            g['compiler_commit'] == pr113_build.profile()['haskell_commit'], 'Wrong generation revision')
    require(g['status'] == 'captured' and g['backend'] == 'tmp.als', 'Wrong generation backend')
    require(type(g['trace_length']) is int and 1 <= g['trace_length'] <= 100, 'Invalid trace length')
    rows = declarations(g['post_analysis'])
    declarations(g['backend_input'])
    declarations(g['backend_ir'])
    # This selected object-only corpus has no string-to-integer abstraction.
    require(g['backend_input'] == g['post_analysis'], 'Unsupported string abstraction')
    require(json.loads(g['json'], object_pairs_hook=unique)['iModule'] == g['post_analysis'], 'JSON/source IR mismatch')
    def bindings(value):
        if type(value) is list:
            for x in value: bindings(x)
        elif type(value) is dict:
            if value.get('tag') == 'GlobalBind':
                require(value['contents'] in rows or value['contents'] in
                        ('root', 'clafer', 'noclafer'), 'Dangling global binding')
            if value.get('tag') == 'TClafer':
                require(all(u in rows or u in ('root','clafer','noclafer') for u in value['_hi']),
                        'Dangling type UID')
            for x in value.values(): bindings(x)
    bindings(g['post_analysis'])
    names = g['names']
    require(type(names) is dict and names.keys() == rows.keys(), 'Incomplete UID mapping')
    require(all(type(n) is str and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', n)
                and n not in ('root','Int','univ','none') for n in names.values()), 'Invalid Alloy name')
    require(len(set(names.values())) == len(names), 'Noninjective UID mapping')
    require(renamed(g['backend_input'], names) == g['backend_ir'], 'Renamed IR correspondence failed')
    require(g['alloy'] == g['backend_alloy'], 'Backend replay differs from generate')
    require(g['explicit'] == g['explicit_observed'], 'Explicit replay differs from generate')
    for key, field in [('JSON','json'), ('Alloy','alloy'), ('Clafer','explicit')]:
        require(g['outputs'][key]['text'] == g[field], 'Output/receipt mismatch')
    require(type(g['scopes']) is list, 'Scope array required')
    scope_ids = set()
    for entry in g['scopes']:
        require(type(entry) is list and len(entry) == 2, 'Invalid source scope')
        u, n = entry
        require(u in rows and u not in scope_ids and type(n) is int and n >= 0, 'Invalid scope UID/count')
        scope_ids.add(u)
    original_scopes = json.loads(g['original_scopes'], object_pairs_hook=unique)
    require(type(original_scopes) is list and len(original_scopes) == len(g['scopes']), 'Wrong original scope file')
    for entry in original_scopes: closed(entry, 'lpqName scope', 'original scope')
    require({e['lpqName']:e['scope'] for e in original_scopes} == dict(g['scopes']), 'Original scope file disagrees')
    explicit_scopes = json.loads(g['explicit_scopes'], object_pairs_hook=unique)
    declared = [e for e in explicit_scopes if 'lpqName' in e]
    require(len(declared)==len(rows) and {e['lpqName']:e['scope'] for e in declared} ==
            {u:dict(g['scopes']).get(u,1) for u in rows}, 'Explicit scope file disagrees')
    require({'defaultScope':1} in explicit_scopes, 'Missing explicit default scope')
    return rows


def layout(g, inspected):
    """Check Analyzer declarations against forward names in the checked backend IR."""
    rows = generation(g)
    names = dict(g['names'], root='root')
    sigs = inspected['signatures']
    require(set(sigs) == {'this/' + n for n in names.values()}, 'Alloy signature inventory differs')
    require(sigs['this/root'] == dict(parent='univ', one=True, abstract=False), 'Wrong root signature')
    def primitive(label):
        seen = set()
        while label in sigs and sigs[label]['parent'] != 'univ':
            require(label not in seen, 'Cyclic signature hierarchy')
            seen.add(label)
            label = sigs[label]['parent']
        return label
    expected = {}
    def field(owner, label, target=None):
        expected['this/' + owner + '/' + label] = target
    for uid, c in rows.items():
        n = names[uid]
        parent = c['_parentUID']
        abstract = c['_modifiers']['_abstract']
        sup = c['_super']
        super_name = 'univ' if sup is None else 'this/' + names[sup['_exp']['_sident']]
        require(sigs['this/' + n]['parent'] == super_name and
                sigs['this/' + n]['abstract'] == abstract, 'Signature hierarchy differs')
        if not (abstract and parent == 'clafer'):
            owner = names.get(parent, 'root')
            field(owner, 'r_' + n, 'this/' + n)
            if not abstract:
                field(n, 'p_' + n, 'this/' + owner)
        if c['_reference'] is not None:
            ref = c['_reference']['_ref']['_iType']
            require(ref['tag'] == 'TClafer' and ref['_hi'], 'Object reference type required')
            field(n, n + '_ref', 'this/' + names[ref['_hi'][0]])
    fields = inspected['fields']
    require(set(fields) == set(expected), 'Alloy field inventory/ownership differs')
    for key, target in expected.items():
        f = fields[key]
        require(f['arity'] == 2 and f['owner'] == key.rsplit('/',1)[0], 'Wrong field owner/arity')
        if target is not None:
            require(f['targets'] == [target], 'Wrong declared field endpoint: ' + key)
            require(len(f['columns']) == 1 and len(f['columns'][0]) == 2 and
                    [primitive(x) for x in f['columns'][0]] ==
                    [primitive(f['owner']), primitive(target)], 'Wrong field type: ' + key)
    return rows


def request(g, index, *, scopes=None, steps=None):
    """Use the ORIGINAL generation's scopes; explicit mode disables inference."""
    rows = generation(g)
    counts = dict(g['scopes']) if scopes is None else scopes
    require(set(counts) <= set(rows), 'Foreign source scope')
    return dict(command_index=index, overall=1, bitwidth=8, min_steps=1,
        max_steps=g['trace_length'] if steps is None else steps,
        identities={'this/root': dict(count=1, exact=False), **{
            'this/' + g['names'][u]: dict(count=counts.get(u,1), exact=False) for u in rows}})
