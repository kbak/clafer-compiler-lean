"""Distinguishing hard-initializer observations from the accepted contract."""
from behavioral_source_cases import case

TEMPORAL = '[always one root]\n'


def initializers():
    for op in ('=', ':='):
        for change in (False, True):
            source = f'x -> int ? {op} 0\n' + TEMPORAL
            yield f'changing-{op}-{change}', ('violated' if op == '=' and change else 'satisfied'), case(
                source, 2, [(1, 1, 0)], [[], [1], [1]], values=[{}, {1: 0}, {1: int(change)}])
        for rebirth in (0, 1):
            yield f'rebirth-{op}-{rebirth}', ('satisfied' if rebirth == 0 else 'violated'), case(
                f'x -> int ? {op} 0\n' + TEMPORAL, 2, [(1, 1, 0)], [[1], [], [1]],
                values=[{1: 0}, {}, {1: rebirth}])
        # Static selection comes from authored syntax, so := agrees with =.
        yield f'static-{op}', 'violated', case(f'x -> int ? {op} 0\n', 2,
            [(1, 1, 0)], [[1], [1]], values=[{1: 0}, {1: 1}])
        # Empty heads suppress complete RHS observation, including undefined
        # temporal conditions (the captured reference is absent at the next time).
        for present in (False, True):
            rhs = 'if (let old = v in X (sum old = 0)) then 0 else 0'
            source = f'v -> int ?\nx -> int ? {op} {rhs}\n'
            if present:
                source = f'x -> int ? {op} {rhs.replace("= v", "= x")}\n'
            yield f'undefined-guard-{op}-{present}', ('undefined' if present else 'satisfied'), case(
                source, 2 if present else 3, [(1, 1, 0)], [[1], []],
                values=[{1: 0}, {}], interval=(0, 0), width=2)

    for added in (0, 1):
        yield f'collection-later-add-{added}', 'satisfied', case(
            'P\n  xs ->> int * := 0\n' + TEMPORAL, 3,
            [(1, 1, 0), (2, 2, 1), (3, 2, 1)], [[1, 2], [1, 2, 3]],
            values=[{2: 0}, {2: 0, 3: added}])
        yield f'collection-parent-rebirth-{added}', ('satisfied' if added == 0 else 'violated'), case(
            'P ?\n  xs ->> int * := 0\n' + TEMPORAL, 3,
            [(1, 1, 0), (2, 2, 1)], [[1, 2], [], [1, 2]], values=[{2: 0}, {}, {2: added}])
        yield f'global-later-add-{added}', 'satisfied', case(
            'abstract xs ->> int * := 0\ny : xs *\n' + TEMPORAL, 3,
            [(1, 2, 0), (2, 2, 0)], [[1], [1, 2]], values=[{1: 0}, {1: 0, 2: added}], supers={2: 1})

    # The accepted Box/flag/x counterexample: Box disappears, but the
    # original RHS next operator is attached to Box's root parent, so it does
    # not cancel. Moving the RHS into x would incorrectly cancel next.
    for value in (0, 1):
        yield f'box-original-anchor-{value}', ('satisfied' if value == 0 else 'violated'), case(
            'Box ?\n  flag ?\n  x -> int ? := if X (some flag) then 1 else 0\n', 4,
            [(1, 1, 0), (2, 2, 1), (3, 3, 1)], [[1, 2, 3], []], values=[{3: value}, {}])

    for wrong in (False, True):
        # Explicit this/parent/root and shadowing all refer to the original Box.
        yield f'original-names-{wrong}', ('violated' if wrong else 'satisfied'), case(
            'Outer\n  flag\n  Box\n    flag ?\n    x -> int ? := if (no this.flag && some parent.flag && one root) then 0 else 1\n'
            + TEMPORAL, 6, [(1, 1, 0), (2, 2, 1), (3, 3, 1), (4, 5, 3)],
            [[1, 2, 3, 4]], values=[{4: int(wrong)}])

    # An own initializer remains conjunctive with inherited constant equations.
    for present in (False, True):
        yield f'inherited-conflict-{present}', ('violated' if present else 'satisfied'), case(
            'abstract A -> int = 0\na : A ? := 1\n' + TEMPORAL, 3,
            [(1, 2, 0)], [[1] if present else []], values=[{1: 0}], supers={2: 1})
    yield 'bag-duplicate-targets', 'satisfied', case(
        'xs ->> int 2 := 0\n' + TEMPORAL, 2, [(1, 1, 0), (2, 1, 0)], [[1, 2]],
        values=[{1: 0, 2: 0}])
    yield 'simultaneous-equations', 'satisfied', case(
        'a -> int := b\nb -> int := a\n' + TEMPORAL, 3,
        [(1, 1, 0), (2, 2, 0)], [[1, 2]], values=[{1: 1, 2: 1}])
    for present in (False, True):
        yield f'parent-replacement-{present}', ('violated' if present else 'satisfied'), case(
            'P ?\n  x -> int ? := 0\n' + TEMPORAL, 3,
            [(1, 1, 0), (2, 1, 0), (3, 2, 1), (4, 2, 2)],
            [[1, 3], [2, 3 if present else 4]], values=[{3: 0}, {3: 0, 4: 0}])

    # Finalref fixes targets within a life, not the original RHS observation.
    for op in ('=', ':='):
        for changing in (False, True):
            yield f'finalref-rhs-{op}-{changing}', ('violated' if op == '=' and changing else 'satisfied'), case(
                f'v -> int\nfinalref x -> int {op} v\n', 3,
                [(1, 1, 0), (2, 2, 0)], [[1, 2], [1, 2]],
                values=[{1: 0, 2: 0}, {1: int(changing), 2: 0}])
        yield f'finalref-later-undefined-{op}', ('undefined' if op == '=' else 'satisfied'), case(
            f'v -> int ?\nfinalref x -> int {op} if (let old = v in X (sum old = 0)) then 0 else 0\n',
            3, [(1, 1, 0), (2, 2, 0)], [[1, 2], [1, 2], [2]],
            values=[{1: 0, 2: 0}] * 3, interval=(0, 0), width=2)

    for wrong in (False, True):
        yield f'global-across-parents-{wrong}', ('violated' if wrong else 'satisfied'), case(
            'abstract xs ->> int * := 0\nP *\n  a : xs ?\n' + TEMPORAL, 4,
            [(1, 2, 0), (2, 2, 0), (3, 3, 1), (4, 3, 2)], [[1, 2, 3, 4]],
            values=[{3: 0, 4: int(wrong)}], supers={3: 1})
    for bounds in ('', '*'):
        yield f'inherited-original-clock-{bounds or "omitted"}', ('violated' if not bounds else 'satisfied'), case(
            f'P\n  abstract xs -> int {bounds} := 0\n  a : xs ?\n' + TEMPORAL, 4,
            [(1, 1, 0), (2, 3, 1)], [[1], [1, 2]], values=[{}, {2: 1}], supers={3: 2})
    yield 'set-duplicate-targets', 'violated', case(
        'xs -> int 2 := 0\n' + TEMPORAL, 2, [(1, 1, 0), (2, 1, 0)], [[1, 2]],
        values=[{1: 0, 2: 0}])
    # Captures preserve identity through absence; substitution would instead
    # re-evaluate the current empty declaration at the next time.
    for wrong in (False, True):
        yield f'let-capture-absence-{wrong}', ('violated' if wrong else 'satisfied'), case(
            'flag ?\nx -> int ? := if (let old = flag in X (some old)) then 1 else 0\n', 3,
            [(1, 1, 0), (2, 2, 0)], [[1, 2], [2]],
            values=[{2: int(not wrong)}, {2: int(not wrong)}], width=2)
