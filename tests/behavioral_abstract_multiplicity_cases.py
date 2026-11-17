"""Independent observations for the aggregate abstract multiplicity extension."""
from behavioral_source_cases import case

PROFILE = 'behavioral-abstract-multiplicity/1'


def selected(*args, **kwargs):
    # These observations have no integer references; all retained scalar rows
    # are zero. Cardinality ranges are checked separately from value intervals.
    kwargs.setdefault('interval', (0, 0))
    result = case(*args, **kwargs)
    result['bounds']['profile'] = result['candidate']['profile'] = PROFILE
    return result


def aggregate_cases():
    # Zero/optional/exact/both finite endpoints/unbounded and omitted defaults.
    # Individual realizations remain optional, independently of the aggregate.
    for spelling, lo, hi in [('0', 0, 0), ('?', 0, 1), ('2', 2, 2),
                             ('1..2', 1, 2), ('2..*', 2, None), ('', 0, None)]:
        for size in (0, 1, 2, 3):
            good = lo <= size and (hi is None or size <= hi)
            expected = 'satisfied' if good else 'violated'
            ids = [(i, 2, 0) for i in range(1, 4)]
            yield f'global-{spelling or "omitted"}-{size}', expected, selected(
                f'abstract A {spelling}\na : A *\n', 3, ids,
                [list(range(1, size+1))], supers={2: 1})
            # A nested abstract must count separately for each live inherited
            # parent, including P instances of the abstract declared parent Base.
            ids = [(1, 3, 0), *[(i, 4, 1) for i in range(2, 5)]]
            yield f'nested-{spelling or "omitted"}-{size}', expected, selected(
                f'abstract Base\n  abstract A {spelling}\nP : Base\n  a : Base.A *\n',
                5, ids, [[1, *range(2, size+2)]], supers={3: 1, 4: 2})
    for total in (3, 6, 8):
        left = 1 if total == 3 else total // 2
        ids = [(i, 2 if i <= left else 3, 0) for i in range(1, total+1)]
        yield f'sibling-total-{total}', 'violated' if total == 8 else 'satisfied', selected(
            'abstract Tools 3..6\na : Tools *\nb : Tools *\n', 4, ids,
            [list(range(1, total+1))], supers={2: 1, 3: 1}, width=5)
    for live, expected in [([1,2,3,4], 'violated'), ([1,2], 'satisfied'), ([], 'violated')]:
        yield f'cross-parent-{len(live)}', expected, selected(
            'abstract A 1\nP *\n  a : A\n', 4,
            [(1,2,0),(2,3,1),(3,2,0),(4,3,3)], [live], supers={3: 1})
    yield 'absent-ancestor-global-zero', 'satisfied', selected(
        'abstract A 0\nP ?\n  a : A 2\n', 4,
        [(1,2,0),(2,3,1),(3,3,1)], [[]], supers={3: 1})
    yield 'absent-declared-parent-positive', 'satisfied', selected(
        'abstract Base\n  abstract A 2\nP : Base ?\n  a : Base.A *\n', 5,
        [(1,3,0)], [[]], supers={3: 1, 4: 2})
    yield 'nested-two-parents-local-upper', 'satisfied', selected(
        'abstract Base\n  abstract A ?\nP : Base 2\n  a : Base.A\n', 5,
        [(1,3,0),(2,4,1),(3,3,0),(4,4,3)], [[1,2,3,4]], supers={3: 1, 4: 2})
    yield 'chain-once', 'satisfied', selected(
        'abstract A 1\nabstract B : A 1\nb : B\n', 4,
        [(1,3,0)], [[1]], supers={2: 1, 3: 2})
    yield 'shared-reference-target', 'satisfied', selected(
        'T\nabstract A -> T 2\na : A\nb : A\n', 5,
        [(1,1,0),(2,3,0),(3,4,0)], [[1,2,3]],
        refs=[[[2,2,1],[2,3,1]]], supers={3: 2, 4: 2})
    for bound, frames in [('1..*', [[1], []]), ('?', [[1], [1,2]])]:
        yield f'later-{bound}', 'violated', selected(
            f'abstract A {bound}\na : A *\n[initially one a]\n', 3,
            [(1,2,0),(2,2,0)], frames, supers={2: 1})
