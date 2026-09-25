from __future__ import annotations

import itertools
from fractions import Fraction

from . import certificate, floating_tone_tie as native
from .core import read
from .evaluate import loci


def source_graphs():
    positive = ({'M0', 'M1', 'H1', 'M2'}, {('M0', 0), ('M1', 1), ('M2', 2)})
    negative = ({'M0', 'H0', 'M1', 'H1'}, {('M0', 0), ('M1', 1)})
    for name, ref, removed, additions in (
            ('positive_delete', positive, {'H1'}, set()),
            ('positive_dock', positive, {'M2'}, {('H1', 2)}),
            ('negative_delete', negative, {'H0', 'H1'}, set()),
            ('negative_dock', negative, {'M1', 'H1'}, {('H0', 1)})):
        present = ref[0] - removed
        links = {e for e in ref[1] if e[0] in present} | additions
        yield name, ref, (present, links)


def faithfulness(reference, candidate):
    tones, links = reference
    kept, realized = candidate
    return [sum(t.startswith('H') for t in tones - kept),
            sum(t.startswith('H') for t, _ in realized - links),
            sum(t.startswith('M') for t in tones - kept),
            sum(t.startswith('M') for t, _ in links - realized)]


def count_candidates(n):
    for states in itertools.product((False, True), repeat=n):
        kept = sum(states)
        yield states, (kept, n-kept), sum(n-1-i for i, present in enumerate(states) if present)


def main():
    source = [{'name': name, 'coefficients': faithfulness(ref, c),
               'present_tones': sorted(c[0]), 'links': sorted(c[1])}
              for name, ref, c in source_graphs()]
    source_coefficients = {r['name']: r['coefficients'] for r in source}
    assert source_coefficients == {'positive_delete': [1, 0, 0, 0],
        'positive_dock': [0, 1, 1, 1], 'negative_delete': [2, 0, 0, 0],
        'negative_dock': [1, 1, 1, 1]}
    sg, fl, mx = native.setup()
    ref = native.build((True,)*3)
    native_rows = []
    for states, pair, align in count_candidates(3):
        candidate = native.build(states)
        assert candidate.well_formed(ref)[0]
        observed = tuple(sum(read(sg, ref, candidate, d, x, 'tone').marked
                             for x in loci(candidate, d, 'tone', ref)) for d in (fl, mx))
        assert observed == pair
        native_rows.append({'retained': list(states), 'counts': pair, 'alignment': align})
    cases = 0
    for n in range(9):
        single = [r for r in count_candidates(n) if r[1][1] == 1]
        assert len(single) == n
        assert len({r[1] for r in single}) <= 1
        if n:
            best = min(r[2] for r in single)
            assert [r[0].index(False) for r in single if r[2] == best] == [0]
        cases += 2**n
    weights = 0
    for h, d, m, a in itertools.product((Fraction(0), Fraction(1, 2), Fraction(1), Fraction(3)), repeat=4):
        s = d+m+a
        positive = s < h
        negative = 2*h < h+s
        assert not (positive and negative)
        assert (s <= h and 2*h <= h+s) == (h == s)
        weights += 1
    record = {'source_graphs': source, 'native_rows': native_rows,
              'count_candidates_checked': cases, 'shared_weight_cases': weights,
              'positive_strict_preference': 'd+m+a<h', 'negative_strict_preference': 'h<d+m+a',
              'weak_preferences': 'h=d+m+a, with incorrect comparison candidates tied',
              'scope': 'Four source comparison candidates and the existing deletion-only count model. No full translation of directional HS or exclusion of all global evaluators.',
              'source': 'McPherson and Lamont: October2024 draft58,59,63,65; published2026 counterpart57,58,62,63. Published prose half-sum inequality differs from the displayed scores.',
              'alignment_control': 'Nonlocal alignment distinguishes single deletions; this control does not by itself fit the full language.'}
    certificate.write('poko_comparison.json', record)
    print(f'4 source graphs; {len(native_rows)} native count rows; {cases} count candidates; {weights} shared-weight cases')


if __name__ == '__main__':
    main()
