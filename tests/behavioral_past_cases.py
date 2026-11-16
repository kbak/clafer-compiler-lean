"""Independent fixed-trace witnesses for the explicitly selected past profile."""
from behavioral_source_cases import case


def selected(*args, **kwargs):
    c = case(*args, **kwargs)
    c['bounds']['profile'] = c['candidate']['profile'] = 'behavioral-rich-core/1'
    return c


def past_cases():
    for good in (False, True):
        sign = '' if good else '!'
        yield f'child-before-birth-{good}', 'satisfied' if good else 'violated', selected(
            'P\n  event ?\n  child ?\n    ['+sign+' (previous some parent.event)]\n', 4,
            [(1,1,0),(2,2,1),(3,3,1)], [[1,2],[1,3],[1]])
        yield f'parent-reset-{good}', 'satisfied' if good else 'violated', selected(
            'P ?\n  child ?\n    ['+('!' if good else '')+' (previous one root)]\n', 3,
            [(1,1,0),(2,2,1)], [[1],[],[1,2],[1]], loop=3)
        yield f'nested-past-future-{good}', 'satisfied' if good else 'violated', selected(
            '[initially '+('F' if good else 'G')+' (previous (previous (previous one root)))]\n',
            1, [], [[]], interval=(0,0), width=2)
        yield f'temporal-rhs-before-instance-{good}', 'satisfied' if good else 'violated', selected(
            'P\n  event ?\n  r -> int ? := if once some event then 1 else 0\n', 4,
            [(1,1,0),(2,2,1),(3,3,1)], [[1,2],[1,3],[1]], values=[{}, {3:int(good)}, {}])
        yield f'since-triggered-dual-{good}', 'satisfied' if good else 'violated', selected(
            '[initially '+('!' if good else '')+' (one root triggered (previous one root))]\n',
            1, [], [[]], interval=(0,0), width=2)
    yield 'inactive-past-rhs', 'satisfied', selected(
        'v -> int ?\nr -> int ? := if once (let old = v in X (sum old = 0)) then 0 else 0\n',
        3, [(1,1,0)], [[1],[]], values=[{1:0},{}], interval=(0,0),width=2)
    yield 'frozen-binder-past', 'satisfied', selected(
        'P\n  child ?\n    [let old = this in previous (some old)]\n', 3,
        [(1,1,0),(2,2,1)], [[1],[1,2],[1]])
