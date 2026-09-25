from __future__ import annotations

import itertools
import json
from fractions import Fraction

from . import certificate, compensatory_lengthening as native, frag_auto
from .evaluate import activation, coefficients


def structures(total):
    for coda in (True, False):
        moras = (0, 1) if total or coda else (0,)
        for host in ((1, 2, None) if 1 in moras else (None,)):
            present = {0, 1, 2} if coda else {0, 1}
            links = {(0, 1)}
            if 1 in moras and host is not None:
                links.add((1, host))
            yield coda, host, moras, present, links


def inspect(total, structure):
    coda, host, moras, present, links = structure
    old_links = {(0, 1), (1, 2)}
    maxseg = len({0, 1, 2} - present)
    nocoda = sum(node != 1 and not any(q > node for q in present) for node in present)
    floating = sum(not any(m == mora and s in present for m, s in links) for mora in moras)
    maxlink = sum((m, s) not in links for m, s in old_links if m in moras)
    long = sum(s == 1 for _, s in links) == 2
    observed = ''.join(('t', 'i', 'k')[i] + ('ː' if i == 1 and long else '')
                       for i in range(3) if i in present)
    return {'total': total, 'deleted': not coda, 'host': host,
            'coefficients': [maxseg, nocoda, floating, maxlink],
            'output': observed, 'compensates': not coda and long}


def pressure(row, weights, attenuation):
    a, b, c, d = row['coefficients']
    m, n, u, k = weights
    return a*m + b*n + c*attenuation*u + d*k


def main():
    rows = []
    for total in (False, True):
        regime = 'total' if total else 'derived'
        sg = frag_auto.make_sigma(regime)
        ref = native.build('total', {}, {0: 1, 1: 2})
        active = activation(sg, ref, native.D)
        nrows = {}
        for deleted, host, candidate in native.candidates(regime):
            assert candidate.well_formed(ref)[0]
            cf = coefficients(sg, ref, candidate, native.D, active)
            nrows[deleted, host] = (cf, native.surface(candidate))
        for structure in structures(total):
            row = inspect(total, structure)
            cf, observed = nrows.pop((row['deleted'], row['host']))
            a, b, c, d = row['coefficients']
            assert cf == {'MAX': (a, 0), 'NOCODA': (b, 0),
                          'MAX-mora': (0, c), 'MAXLINK-M': (d, 0)}
            assert observed == row['output']
            rows.append(row)
        assert not nrows
    assert len(rows) == 10
    checks = 0
    for weights in itertools.product((0, 1, 3), repeat=4):
        m, n, u, k = weights
        for attenuation in (Fraction(0), Fraction(1, 8), Fraction(1, 2), Fraction(1)):
            for total in (False, True):
                domain = [r for r in rows if r['total'] == total]
                scores = [pressure(r, weights, attenuation) for r in domain]
                winners = [r for r, s in zip(domain, scores) if s == min(scores)]
                assert winners
                if total:
                    assert all(r['compensates'] for r in winners) == (m+k < n and k < attenuation*u)
                else:
                    assert not any(r['compensates'] for r in domain)
                    assert all(r['deleted'] for r in winners) == (m < n)
                checks += 1
    record = {'rows': rows, 'native_coefficient_pairs': 80, 'finite_weight_checks': checks,
              'exact_total_region': 'max+maxlink<nocoda and maxlink<lambda*mora',
              'exact_derived_deletion_region': 'max<nocoda',
              'source_scope': 'Constructed tik mechanism comparison. The source UMQ stress system and its full GEN are not translated by this finite example.'}
    certificate.write('compensatory_lengthening_region.json', record)
    print(json.dumps({'canonical_candidates': len(rows), 'weight_checks': checks}))


if __name__ == '__main__':
    main()
