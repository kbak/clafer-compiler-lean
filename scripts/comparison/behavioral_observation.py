"""Supplementary finite source observations, independent of target lowering.

Constructor equations follow the MIT source at clafer-semantics
5182c8f5884eddfd8bff8a26b493a8550f0162b6: Denotation, PartialObservation,
Lifetime, Modifiers and Structural. Copyright 2026 Kacper Bak.
This Python adapter is tested, not kernel proved. The verified first-slice
checker and full compiler preservation theorems retain their own boundaries.
"""
from itertools import product


class Undefined(ValueError):
    pass


def ordinary(x):
    return ('object', x)


def integer(x):
    return ('integer', x)


def quantifier(q, values):
    count = sum(values)
    return dict(all=count == len(values), some=count > 0, no=count == 0,
                one=count == 1, lone=count <= 1)[q]


# [impl->req~compiler-behavioral-qualification~1]
class Observation:
    def __init__(self, compiled, candidate):
        self.compiled, self.candidate = compiled, candidate
        self.ds = {d['id']: d for d in compiled['declarations']}
        self.ids = {r['id']: r for r in candidate['identities']}
        self.frames, self.loop = candidate['frames'], candidate['loop']
        self.root = candidate['root']
        self.primitive = next(d['id'] for d in self.ds.values() if d['primitive'])

    def index(self, t):
        return t if t < len(self.frames) else self.loop + (t-self.loop) % (len(self.frames)-self.loop)

    def frame(self, t):
        return self.frames[self.index(t)]

    def orbit(self, t):
        # The first visit to a loop state has different birth history. Preserve
        # the predecessor as well as the current stored frame before repeating.
        seen, result = set(), []
        while (key := (self.index(t), None if t == 0 else self.index(t-1))) not in seen:
            seen.add(key)
            result.append(t)
            t += 1
        return result

    def ancestors(self, d):
        result = []
        while d is not None:
            if d in result:
                raise ValueError('cyclic source inheritance')
            result.append(d)
            d = self.ds[d]['super']
        return result

    def typed(self, x, d):
        return (d == self.primitive if x[0] == 'integer'
                else d in self.ancestors(self.ids[x[1]]['type']))

    def live(self, x, t):
        return x[0] == 'integer' or x[1] in self.frame(t)['live']

    def heads(self, d, t):
        if d == self.primitive:
            raise Undefined('whole mathematical integer extent is not finite')
        return {ordinary(x) for x in self.frame(t)['live'] if self.typed(ordinary(x), d)}

    def parent(self, x):
        if x[0] == 'integer':
            return ordinary(self.root)
        p = self.ids[x[1]]['parent']
        return ordinary(p) if p is not None else None

    def parent_present(self, context, t):
        parent = self.parent(context)
        return parent is None or self.live(parent, t)

    def starts(self, x, t):
        return self.live(x, t) and (t == 0 or not self.live(x, t-1))

    def ends(self, x, t):
        return self.live(x, t) and not self.live(x, t+1)

    def reference(self, d, x, t):
        owner = self.ds[d]['referenceOwner']
        if owner is None or not self.typed(x, d) or not self.live(x, t):
            return set()
        target = self.ds[owner]['reference']['target']
        if target == self.primitive:
            return {integer(dict(self.frame(t)['values'])[x[1]])}
        return {ordinary(y) for decl, head, y in self.frame(t)['references']
                if decl == owner and head == x[1]}

    def step(self, st, xs, t):
        if st[0] == 'parent':
            return {p for x in xs if (p := self.parent(x)) is not None and self.live(p, t)}
        if st[0] == 'child':
            return {y for y in self.heads(st[1], t) if self.parent(y) in xs
                    and self.live(self.parent(y), t)}
        if st[0] == 'deref':
            return set().union(*(self.reference(st[1], x, t) for x in xs))
        raise ValueError('unknown navigation')

    def set(self, a, context, env, t):
        tag, *args = a
        if tag == 'empty': return set()
        if tag == 'this': return {context} if self.live(context, t) else set()
        if tag == 'root': return {ordinary(self.root)}
        if tag == 'var': return env[args[0]]
        if tag == 'extent': return self.heads(args[0], t)
        if tag == 'thisStep': return self.step(args[0], {context}, t)
        if tag == 'step': return self.step(args[0], self.set(args[1], context, env, t), t)
        left, right = [self.set(x, context, env, t) for x in args]
        return {'union': set.union, 'inter': set.intersection, 'diff': set.difference}[tag](left, right)

    def collection(self, a, c, e, t):
        tag, *args = a
        if tag == 'set': return self.set(args[0], c, e, t)
        if tag == 'literal': return {integer(args[0])}
        if tag == 'integer': return {integer(self.integer(args[0], c, e, t))}
        if tag == 'step': return self.step(args[0], self.collection(args[1], c, e, t), t)
        if tag == 'ofType': return {x for x in self.collection(args[1], c, e, t) if self.typed(x, args[0])}
        if tag == 'ite':
            condition = self.checked(args[0], c, e, t, raw=True)
            yes, no = [self.collection(x, c, e, t) for x in args[1:]]
            return yes if condition else no
        if tag == 'extreme':
            values = self.numbers(self.collection(args[1], c, e, t))
            return {integer((min if args[0] == 'minimum' else max)(values))} if values else set()
        left, right = [self.collection(x, c, e, t) for x in args]
        return {'union': set.union, 'inter': set.intersection, 'diff': set.difference}[tag](left, right)

    @staticmethod
    def numbers(xs):
        if any(x[0] != 'integer' for x in xs):
            raise Undefined('noninteger numeric observation')
        return {x[1] for x in xs}

    def integer(self, a, c, e, t):
        tag, *args = a
        if tag == 'literal': return args[0]
        if tag == 'negate': return -self.integer(args[0], c, e, t)
        if tag in ('coerce', 'extract', 'cardinality'):
            xs = self.collection(args[0], c, e, t)
            if tag == 'cardinality': return len(xs)
            values = self.numbers(xs)
            if tag == 'extract' and len(values) != 1: raise Undefined('nonsingleton extraction')
            return sum(values)
        if tag == 'ite':
            condition = self.checked(args[0], c, e, t, raw=True)
            yes, no = [self.integer(x, c, e, t) for x in args[1:]]
            return yes if condition else no
        if tag == 'fold':
            values = [self.integer(args[2], c, [{x}, *e], t)
                      for xs in self.collections(args[1], c, e, t) for x in sorted(xs)]
            result = 0 if args[0] == 'sum' else 1
            for value in values:
                result = result + value if args[0] == 'sum' else result * value
            return result
        if tag == 'binary':
            op = args[0]
            x, y = [self.integer(a, c, e, t) for a in args[1:]]
            if op == 'add': return x+y
            if op == 'subtract': return x-y
            if op == 'multiply': return x*y
            if y == 0: raise Undefined('zero divisor')
            quotient = (abs(x)//abs(y)) * (-1 if (x < 0) != (y < 0) else 1)
            return quotient if op == 'divide' else x-quotient*y
        raise ValueError('unknown integer constructor')

    def collections(self, a, c, e, t):
        if a[0] == 'nil': return []
        if a[0] == 'cons': return [self.collection(a[1], c, e, t), *self.collections(a[2], c, e, t)]
        raise ValueError('unknown collection family')

    def atom(self, a, c, e, t):
        if a[0] == 'primitive':
            tag, *args = a[1]
            values = [(self.integer if tag in ('integerEqual', 'less') else self.collection)(x, c, e, t)
                      for x in args]
            if tag == 'inhabited': return bool(values[0])
            if tag in ('equal', 'integerEqual'): return values[0] == values[1]
            if tag == 'subset': return values[0] <= values[1]
            if tag == 'less': return values[0] < values[1]
        if a[0] == 'count':
            _, q, arity, disjoint, domain, body = a
            xs = sorted(self.collection(domain, c, e, t))
            tuples = [v for v in product(xs, repeat=arity) if not disjoint or len(set(v)) == arity]
            values = [self.checked(body, c, [*({x} for x in reversed(v)), *e], t, raw=True) for v in tuples]
            return quantifier(q, values)
        raise ValueError('unknown atom')

    def active(self, c, t):
        result = []
        for j in self.orbit(t):
            if not self.parent_present(c, j): return result, True
            result.append(j)
        return result, False

    def defined(self, f, c, e, t):
        tag, *args = f
        if tag == 'truth': return
        if tag == 'atom': self.atom(args[0], c, e, t); return
        if tag == 'next':
            if self.parent_present(c, t+1): self.defined(args[0], c, e, t+1)
            return
        if tag in ('eventually', 'always', 'strongUntil', 'weakUntil'):
            for j in self.active(c, t)[0]:
                for a in args: self.defined(a, c, e, j)
            return
        if tag in ('initially', 'finally'):
            if (self.starts if tag == 'initially' else self.ends)(c, t): self.defined(args[0], c, e, t)
            return
        if tag == 'letSet':
            self.defined(args[1], c, [self.collection(args[0], c, e, t), *e], t)
            return
        if tag == 'quant':
            for x in self.collection(args[1], c, e, t): self.defined(args[2], c, [{x}, *e], t)
            return
        for a in args: self.defined(a, c, e, t)

    def checked(self, f, c, e, t, raw=False):
        self.defined(f, c, e, t)
        return self.truth(f, c, e, t, None if raw else True)

    def truth(self, f, c, e, t, sign=True):
        tag, *args = f
        value = lambda a, s=sign, j=t, env=e: self.truth(a, c, env, j, s)
        polar = lambda v: v if sign is not False else not v
        if tag == 'truth': return polar(True)
        if tag == 'atom': return polar(self.atom(args[0], c, e, t))
        if sign is None and tag in ('not', 'and', 'or', 'implies', 'iff', 'xor', 'ite'):
            xs = [value(a) for a in args]
            if tag == 'not': return not xs[0]
            if tag == 'and': return xs[0] and xs[1]
            if tag == 'or': return xs[0] or xs[1]
            if tag == 'implies': return not xs[0] or xs[1]
            if tag == 'iff': return xs[0] == xs[1]
            if tag == 'xor': return xs[0] != xs[1]
            return xs[1] if xs[0] else xs[2]
        if tag == 'not': return value(args[0], not sign)
        if tag in ('and', 'or'):
            xs = [value(a) for a in args]
            return all(xs) if (tag == 'and') == sign else any(xs)
        if tag == 'implies':
            xs = [value(args[0], not sign), value(args[1])]
            return any(xs) if sign else all(xs)
        if tag in ('iff', 'xor'):
            if tag == 'xor': sign = not sign
            a, b = args
            return ((value(a, False) or value(b, True)) and (value(b, False) or value(a, True)) if sign else
                    (value(a, True) and value(b, False)) or (value(b, True) and value(a, False)))
        if tag == 'ite':
            a, b, d = args
            return ((value(a, False) or value(b, True)) and (value(a, True) or value(d, True)) if sign else
                    (value(a, True) and value(b, False)) or (value(a, False) and value(d, False)))
        if tag == 'next': return not self.parent_present(c, t+1) or value(args[0], j=t+1)
        if tag in ('initially', 'finally'):
            active = (self.starts if tag == 'initially' else self.ends)(c, t)
            return not active or value(args[0])
        if tag in ('eventually', 'always'):
            times, cancelled = self.active(c, t)
            xs = [value(args[0], j=j) for j in times]
            eventual = (tag == 'eventually') != (sign is False)
            return cancelled or any(xs) if eventual else all(xs)
        if tag in ('strongUntil', 'weakUntil'):
            times, cancelled = self.active(c, t)
            weak = (tag == 'weakUntil') != (sign is False)
            left = lambda j: value(args[0], j=j) if sign is not False else value(args[1], False, j)
            right = lambda j: value(args[1], j=j) if sign is not False else value(args[0], False, j) and value(args[1], False, j)
            prefix = True
            for j in times:
                if prefix and right(j): return True
                prefix = prefix and left(j)
            return prefix and (cancelled or weak)
        if tag == 'letSet': return value(args[1], env=[self.collection(args[0], c, e, t), *e])
        if tag == 'quant':
            q, domain, body = args
            xs = sorted(self.collection(domain, c, e, t))
            if q in ('one', 'lone'):
                return polar(quantifier(q, [value(body, None, env=[{x}, *e]) for x in xs]))
            if sign is None:
                return quantifier(q, [value(body, None, env=[{x}, *e]) for x in xs])
            if q == 'no': q, body_sign = ('all' if sign else 'some'), not sign
            else: q, body_sign = (q if sign else {'all': 'some', 'some': 'all'}[q]), sign
            return quantifier(q, [value(body, body_sign, env=[{x}, *e]) for x in xs])
        raise ValueError('unknown formula')

    def attached(self, constraint):
        values = []
        for t in self.orbit(0):
            for c in sorted(self.heads(constraint['owner'], t)):
                values.append(self.checked(constraint['body'], c, [], t))
        return all(values)

    def structural(self):
        root = ordinary(self.root)
        if self.ids[self.root]['type'] != self.compiled['root'] or self.parent(root) is not None: return False
        for x, row in self.ids.items():
            d = self.ds[row['type']]
            if d['primitive'] or d['abstract']: return False
            if x != self.root and (row['type'] == self.compiled['root'] or row['parent'] is None): return False
            if d['parent'] is not None and (row['parent'] is None or not self.typed(ordinary(row['parent']), d['parent'])): return False
        def fits(b, size): return b['lower'] <= size and (b['upper'] is None or size <= b['upper'])
        for t in self.orbit(0):
            live = {ordinary(x) for x in self.frame(t)['live']}
            if root not in live: return False
            if any(x != root and self.parent(x) not in live for x in live): return False
            for x in live:
                seen = set()
                while x != root:
                    if x in seen or x is None: return False
                    seen.add(x); x = self.parent(x)
            for d, x, y in self.frame(t)['references']:
                ref = self.ds[d]['reference']
                if ref['kind'] == 'basic' or ref['target'] == self.primitive: return False
                if ordinary(x) not in self.heads(d,t) or ordinary(y) not in self.heads(ref['target'],t): return False
            for x in live:
                targets = set().union(*(self.reference(d,x,t) for d in self.ds))
                if len(targets) > 1: return False
            for d, row in self.ds.items():
                if row['primitive']: continue
                heads = self.heads(d,t)
                if row['reference']['kind'] != 'basic' and any(len(self.reference(d,x,t)) != 1 for x in heads): return False
                if row['parent'] is not None:
                    parents = self.heads(row['parent'],t)
                    if any(self.parent(x) not in parents for x in heads): return False
                    for p in parents:
                        children = {x for x in heads if self.parent(x) == p}
                        if not fits(row['localBounds'],len(children)): return False
                        owner = row['referenceOwner']
                        if owner is not None and self.ds[owner]['reference']['kind'] == 'set':
                            refs = [frozenset(self.reference(d,x,t)) for x in children]
                            if len(set(refs)) != len(refs): return False
                if not row['abstract'] and row['groupBounds'] != dict(lower=0,upper=None):
                    child_ds = [j for j,r in self.ds.items() if r['parent'] in self.ancestors(d)]
                    for p in heads:
                        children = {x for j in child_ds for x in self.heads(j,t) if self.parent(x) == p}
                        if not fits(row['groupBounds'],len(children)): return False
        return True

    def modifiers(self):
        for t in self.orbit(0):
            live = {ordinary(x) for x in self.frame(t)['live']}
            for d,row in self.ds.items():
                for modifier in row['modifiers']:
                    if modifier == 'initial':
                        if row['parent'] is not None:
                            for p in self.heads(row['parent'],t):
                                if self.starts(p,t) and not self.step(['child',d],{p},t): return False
                    if modifier in ('final','finalref'):
                        for x in self.heads(d,t):
                            if self.live(x,t+1) and self.reference(d,x,t) != self.reference(d,x,t+1): return False
                    if modifier in ('final','finaltarget'):
                        for p in live:
                            if not self.live(p,t+1): continue
                            a,b = [self.step(['child',d],{p},j) for j in (t,t+1)]
                            if modifier == 'finaltarget':
                                a,b = [self.step(['deref',d],xs,j) for xs,j in ((a,t),(b,t+1))]
                            if a != b: return False
        return True

    def check(self):
        structural = self.structural()
        if not structural: return dict(status='violated', structural=False)
        resolved = self.compiled['resolved']
        try:
            model = self.modifiers() and all([self.attached(c) for c in resolved['constraints']])
            if not model: return dict(status='violated', structural=True)
            if self.compiled['command']['kind'] == 'check':
                try:
                    property_holds = self.attached(resolved['assertions'][self.compiled['command']['assertion']])
                except Undefined:
                    property_holds = False
                satisfied = not property_holds
            else:
                satisfied = all([self.attached(c) for c in resolved['scenario']])
            return dict(status='satisfied' if satisfied else 'violated', structural=True)
        except Undefined:
            return dict(status='undefined', structural=True)
