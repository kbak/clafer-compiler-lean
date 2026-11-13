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
    selected = pr113_build.candidate_for(g['compiler_commit'])
    keys = 'schema compiler_commit effective_options trace_length files post_analysis outputs status backend json alloy explicit explicit_observed explicit_scopes original_scopes scopes backend_input backend_ir backend_alloy names'
    if selected != '9a0f16e': keys += ' source_map backend_map'
    closed(g, keys, 'generation')
    if selected != '9a0f16e':
        require(type(g['source_map']) is str and g['source_map']==g['backend_map'], 'Source-map replay differs')
    require(g['schema'] == 'clafer-pr113-generation/1', 'Wrong generation schema')
    require(g['status'] == 'captured' and g['backend'] in
            (('tmp.als', 'als') if selected != '9a0f16e' else ('tmp.als',)), 'Wrong generation backend')
    require(type(g['trace_length']) is int and 1 <= g['trace_length'] <= 100, 'Invalid trace length')
    rows = declarations(g['post_analysis'])
    declarations(g['backend_input'])
    declarations(g['backend_ir'])
    # Objects and selected integer references need no string-to-integer abstraction.
    require(g['backend_input'] == g['post_analysis'], 'Unsupported string abstraction')
    require(json.loads(g['json'], object_pairs_hook=unique)['iModule'] == g['post_analysis'], 'JSON/source IR mismatch')
    def bindings(value):
        if type(value) is list:
            for x in value: bindings(x)
        elif type(value) is dict:
            if value.get('tag') == 'GlobalBind':
                require(value['contents'] in rows or value['contents'] in
                        (('root', 'clafer', 'noclafer', 'integer', 'int') if selected != '9a0f16e' else
                         ('root', 'clafer', 'noclafer')), 'Dangling global binding')
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


def reference_targets(pexp, rows, names):
    """Selected resolved IDs, containment navigation and unions; never arbitrary Alloy text."""
    exp = pexp['_exp']
    if exp['tag'] == 'IClaferId':
        uid = exp['_sident']
        require(exp['_binding'] == {'tag':'GlobalBind', 'contents':uid}, 'Unresolved reference endpoint')
        if uid in ('integer', 'int'):
            require(pexp['_iType'] == {'tag':'TInteger'}, 'Wrong integer endpoint type')
            return ['Int']
        require(uid in rows and pexp['_iType']['tag']=='TClafer' and
                pexp['_iType']['_hi'][0] == uid, 'Wrong reference endpoint type')
        return ['this/' + names[uid]]
    require(exp['tag']=='IFunExp' and exp['_op'] in ('.','++') and
            len(exp['_exps'])==2, 'Unsupported reference expression')
    left, right = exp['_exps']
    a, b = reference_targets(left,rows,names), reference_targets(right,rows,names)
    if exp['_op']=='++':
        require('Int' not in a+b, 'Mixed integer/object reference union')
        return a+b
    # The selected navigation is a containment path, not a computed target or dereference.
    require(len(a)==len(b)==1 and right['_exp']['tag']=='IClaferId', 'Unsupported target navigation')
    child = rows[right['_exp']['_sident']]
    parent = child['_parentUID']
    require(parent in names and a==['this/'+names[parent]], 'Target navigation owner differs')
    return b


def layout(g, inspected):
    """Check declaration endpoints and actual type products under the captured hierarchy."""
    rows = generation(g)
    modern = pr113_build.candidate_for(g['compiler_commit']) != '9a0f16e'
    static = g['backend']=='als'
    names = dict(g['names'], **({} if static else {'root':'root'}))
    sigs = inspected['signatures']
    require(set(sigs) == {'this/' + n for n in names.values()}, 'Alloy signature inventory differs')
    if not static:
        require(sigs['this/root'] == dict(parent='univ', one=True, abstract=False), 'Wrong root signature')
    expected = {}
    def field(owner, label, targets):
        expected['this/' + owner + '/' + label] = targets
    for uid, c in rows.items():
        n, parent, abstract = names[uid], c['_parentUID'], c['_modifiers']['_abstract']
        sup = c['_super']
        super_name = 'univ' if sup is None else 'this/' + names[sup['_exp']['_sident']]
        require(sigs['this/' + n]['parent'] == super_name and
                sigs['this/' + n]['abstract'] == abstract, 'Signature hierarchy differs')
        if static:
            if parent in rows:
                field(names[parent], 'r_' + n, ['this/' + n])
        elif not (abstract and parent == 'clafer'):
            owner = names.get(parent, 'root')
            field(owner, 'r_' + n, ['this/' + n])
            if not abstract:
                field(n, 'p_' + n, ['this/' + owner])
        if c['_reference'] is not None:
            ref = c['_reference']['_ref']
            if modern:
                targets = reference_targets(ref, rows, names)
            else:
                require(ref['_iType']['tag']=='TClafer' and ref['_iType']['_hi'], 'Object reference type required')
                targets = ['this/'+names[ref['_iType']['_hi'][0]]]
            field(n, n + '_ref', targets)
    # Alloy folds type unions using abstract covers. Compare products as disjoint
    # symbolic regions; concrete parents retain their own residual region. This
    # admits cover folding without collapsing every endpoint to its top ancestor.
    def regions(label, seen=frozenset()):
        if label=='Int': return {'Int'}
        require(label in sigs and label not in seen, 'Unknown or cyclic type signature')
        children = [n for n,s in sigs.items() if s['parent']==label]
        result = set() if sigs[label]['abstract'] and children else {label}
        for child in children: result.update(regions(child,seen|{label}))
        return result
    fields = inspected['fields']
    require(set(fields) == set(expected), 'Alloy field inventory/ownership differs')
    for key, targets in expected.items():
        f = fields[key]
        require(f['arity'] == 2 and f['owner'] == key.rsplit('/',1)[0], 'Wrong field owner/arity')
        require(f['targets'] == targets, 'Wrong declared field endpoint: ' + key)
        require(type(f['columns']) is list and f['columns'] and
                all(type(p) is list and len(p)==2 for p in f['columns']), 'Wrong field products')
        actual = {(a,b) for x,y in f['columns'] for a in regions(x) for b in regions(y)}
        wanted = {(a,b) for a in regions(f['owner']) for t in targets for b in regions(t)}
        require(actual==wanted, 'Wrong field type: ' + key)
    return rows


def request(g, index, *, scopes=None, steps=None):
    """Use the ORIGINAL generation's scopes; explicit mode disables inference."""
    rows = generation(g)
    counts = dict(g['scopes']) if scopes is None else scopes
    require(set(counts) <= set(rows), 'Foreign source scope')
    return dict(command_index=index, overall=1, bitwidth=8, min_steps=1,
        max_steps=(1 if g['backend']=='als' else g['trace_length']) if steps is None else steps,
        identities={**({} if g['backend']=='als' else {'this/root': dict(count=1, exact=False)}), **{
            'this/' + g['names'][u]: dict(count=counts.get(u,1), exact=False) for u in rows}})
