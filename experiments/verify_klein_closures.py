"""Independently check the recovered closure certificates and reproduce Table 1.

Regenerates all maps and generators using exact NumPy integer operations.
Does not import or execute the C++ search program. See README.md for provenance.
"""
import csv
import json
from pathlib import Path

import numpy as np

if not __debug__:
    raise SystemExit("Verification requires assertions: omit python -O / -OO.")

root = Path(__file__).resolve().parent
rules = np.arange(65536, dtype=np.uint64)
configurations = np.arange(16, dtype=np.uint64)
shifted = np.zeros((4, 16), dtype=np.uint64)
for g in range(4):
    for h in range(4):
        shifted[g] |= ((configurations >> (h ^ g)) & 1) << h
maps = np.zeros((65536, 16), dtype=np.uint64)
for g in range(4):
    maps |= ((rules[:, None] >> shifted[g][None, :]) & 1) << g
identity = 43690
assert np.all(maps[identity] == configurations)
unit = np.all(np.diff(np.sort(maps, axis=1), axis=1) != 0, axis=1)
assert unit.sum() == 512
lazy = set()
definitions = []
for neighborhood in range(1, 16, 2):
    for pattern in range(16):
        if pattern & ~neighborhood:
            continue
        bits = [int(x & 1) ^ int((x & neighborhood) == pattern) for x in range(16)]
        rule = sum(v << x for x, v in enumerate(bits))
        lazy.add(rule)
        definitions.append((neighborhood, pattern, rule))
assert len(definitions) == len(lazy) == 54
assert not np.any(unit[list(lazy)])
with (root / 'lazy-generators.csv').open(newline='') as stream:
    reader = csv.DictReader(stream)
    assert reader.fieldnames == ['neighborhood_mask', 'active_pattern_bits', 'rule_id']
    assert [tuple(int(row[key]) for key in reader.fieldnames) for row in reader] == definitions

# Proposition 6.2: no swapping constants or a preserved two-point orbit.
no_swaps = (maps[:, 0] == maps[:, 15]) | ((maps[:, 0] == 0) & (maps[:, 15] == 15))
for s in (1, 2, 3):
    x = (1 << 0) | (1 << s)
    y = 15 ^ x
    no_swaps &= ~((maps[:, x] == y) & (maps[:, y] == x))

weights = 1 << configurations
results = {}
for stem, generators in [('lazy', sorted(lazy)),
                         ('units-lazy', sorted(lazy | set(rules[unit].tolist())))]:
    with (root / (stem + '-membership.csv')).open(newline='') as stream:
        reader = csv.DictReader(stream)
        assert reader.fieldnames == ['rule_id', 'member', 'shortest_length',
                                     'predecessor_rule', 'generator_rule',
                                     'application_order_generator_word']
        rows = list(reader)
    assert len(rows) == 65536
    assert [int(r['rule_id']) for r in rows] == list(range(65536))
    assert all(r['member'] in ('0', '1') for r in rows)
    inside = np.array([r['member'] == '1' for r in rows])
    depth = np.array([int(r['shortest_length']) for r in rows])
    assert inside[identity] and depth[identity] == 0
    assert rows[identity]['application_order_generator_word'] == ''
    assert int(rows[identity]['predecessor_rule']) == -1
    assert int(rows[identity]['generator_rule']) == -1
    assert np.all(depth[inside & (rules != identity)] > 0)
    assert np.all(depth[~inside] == -1)
    for row in rows:
        if row['member'] == '0':
            assert int(row['predecessor_rule']) == -2
            assert int(row['generator_rule']) == -1
            assert row['application_order_generator_word'] == ''
    assert all(inside[g] for g in generators)
    members = rules[inside]

    # Every certified nonroot is one left-generator step from a member.
    nonroot = [r for r in rows if r['member'] == '1' and int(r['rule_id']) != identity]
    predecessors = np.array([int(r['predecessor_rule']) for r in nonroot])
    gens = np.array([int(r['generator_rule']) for r in nonroot], dtype=np.uint64)
    ids = np.array([int(r['rule_id']) for r in nonroot])
    assert np.all((0 <= predecessors) & (predecessors < 65536))
    assert set(gens.tolist()) <= set(generators)
    composed = (((gens[:, None] >> maps[predecessors]) & 1) * weights).sum(axis=1)
    assert np.all(composed == ids) and np.all(inside[predecessors])
    assert np.all(depth[ids] == depth[predecessors] + 1)

    # With the empty root and strictly descending depths, these equations
    # certify every complete word and its length by induction on depth.
    for row in nonroot:
        words = row['application_order_generator_word'].split()
        parent = rows[int(row['predecessor_rule'])]['application_order_generator_word'].split()
        assert words == parent + [row['generator_rule']]
        assert len(words) == int(row['shortest_length'])

    # Closure proves completeness; edge inequalities prove shortest lengths.
    # These checks cover every member and every generator, including the unit id.
    nonempty = np.zeros(65536, dtype=bool) if stem == 'lazy' else None
    for gen in generators:
        composed = (((np.uint64(gen) >> maps[members]) & 1) * weights).sum(axis=1).astype(np.int64)
        assert np.all(inside[composed])
        assert np.all(depth[composed] <= depth[members] + 1)
        if nonempty is not None:
            nonempty[composed] = True
    if stem == 'lazy':
        assert np.array_equal(nonempty, inside & (rules != identity))
        assert not np.any(unit[inside & (rules != identity)])
        assert np.all(no_swaps[inside])
        nonempty_count = int(nonempty.sum())
    else:
        no_swaps_count = int(np.count_nonzero(inside & no_swaps))
        assert no_swaps_count == 19360
    results[stem] = {
        'monoid_count': int(inside.sum()),
        'max_shortest_length': int(depth.max()),
        'length_distribution': np.bincount(depth[inside]).tolist(),
        'generator_count': len(generators),
        'closure_and_distance_edges_checked': len(members) * len(generators),
        'certificates': 'Every predecessor, generator word, generator-closure edge, and shortest distance verified independently.'
    }

# Compare verified counts with all entries of v5 Table 1, including the totals.
assert results['lazy']['length_distribution'] == [1, 54, 678, 1894, 1218, 156, 6]
assert results['units-lazy']['length_distribution'] == [1, 565, 8806, 27424, 19004, 3870, 42]
assert results['lazy']['monoid_count'] == 4007
assert results['units-lazy']['monoid_count'] == 59712
assert nonempty_count == 4006
result = {
    'checks': results,
    'identity_rule': identity,
    'unit_count': int(unit.sum()),
    'lazy_generator_count': len(lazy),
    'lazy_nonempty_semigroup_count': nonempty_count,
    'lazy_monoid_count': results['lazy']['monoid_count'],
    'units_lazy_count': results['units-lazy']['monoid_count'],
    'no_swaps_in_units_lazy': no_swaps_count,
    'all_lazy_members_satisfy_no_swaps': True,
    'paper_v5_table_1_matches': True,
    'scope': 'Exact finite computation with independently checked membership and shortest-word certificates. Lean formalization is separate.',
    'Lean_run': False,
    'failures': 0
}
(root / 'closure-independent-verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
print('\nTable 1. Numbers of elements at each shortest-word length.')
print('Length k | l_L(T)=k | l_(U union L)(T)=k')
with (root / 'table-1.csv').open('w', newline='') as stream:
    writer = csv.writer(stream, lineterminator='\n')
    writer.writerow(['length', 'lazy', 'units_lazy'])
    for k, (lazy_count, mixed_count) in enumerate(zip(results['lazy']['length_distribution'],
                                                     results['units-lazy']['length_distribution'])):
        writer.writerow([k, lazy_count, mixed_count])
        print(f'{k} | {lazy_count:,} | {mixed_count:,}')
    writer.writerow(['Total', result['lazy_monoid_count'], result['units_lazy_count']])
print(f"Total | {result['lazy_monoid_count']:,} | {result['units_lazy_count']:,}")
