from pathlib import Path
from fractions import Fraction as Q
from datetime import datetime, timezone
import hashlib
import json
from phonological_requirements import certificate, paths
from .design_length import battery
from .dev_regions import CONTROL_ITEMS
from .guaext import ConstructedInput, fragment, named_fragment
from .sharedactivity import SharedActivityModel


def schematic(v1, v3):
    words = (('t',) + ('ɛ',) * v1, ('t', 'e'), ('ɔ',) + ('k', 'ɔ') * (v3 - 1))
    focal = (v1, v1 + 2, v1 + 3)
    inp = ConstructedInput(id=f'schema_{v1}_{v3}', words=words, phrases=(0, 0, 0),
                           focal=focal, note='Algebraic length-family instance, not attested data')
    target = list(sum(words, ()))
    target[focal[0]] = 'e'
    target[focal[1]] = 'ɔ'
    return fragment(inp, ''.join(target)), ''.join(target)


def main():
    cells = battery()
    lengths = [(c.v1, c.v3) for c in cells] + [(1, 1), (3, 9), (7, 20)]
    ratio = min([Q(1, 24)] + [Q(a, (1 + b) * (a + 1 + b)) / 2 for a, b in lengths])
    weights = dict(MARK_ATR=Q(10), MARK_HIA=Q(10), ID_INIT_V=Q(20),
                   ID_PLUS_ATR_G=Q(1), ID_MINUS_ATR=ratio, ID_QUAL=Q(2),
                   ID_HIGH=Q(20), MAX=Q(20), ID_NUC=Q(20), ID_PLUS_ATR=Q(1))
    cases = [(fragment(c.inp, c.opaque), c.opaque) for c in cells]
    cases += [schematic(a, b) for a, b in [(1, 1), (3, 9), (7, 20)]]
    cases += [(fragment(CONTROL_ITEMS[k][0], CONTROL_ITEMS[k][1]), CONTROL_ITEMS[k][1])
              for k in ('OR12a', 'OR25oE')]
    f = named_fragment('G34a')
    cases.append((f, f.record['observation']))
    rows = []
    for f, target in cases:
        model = SharedActivityModel(f, full_gen=True)
        values = []
        for idx, segs in model.candidates():
            violations = model.violations(segs)
            penalty = sum(weights[c] * violations[c] for c in model.constraints)
            values.append((penalty, idx, f.observe(segs)))
        best = min(x[0] for x in values)
        winners = sorted({x[2] for x in values if x[0] == best})
        bad_best = min(x[0] for x in values if x[2] != target)
        row = dict(id=f.id, candidates=len(values), target=target, winners=winners,
                   target_wins_exclusively=winners == [target],
                   minimum=str(best), bad_margin=str(bad_best - best))
        rows.append(row)
        print(json.dumps(row, ensure_ascii=False), flush=True)
    development = []
    for f, target in cases[-3:]:
        model = SharedActivityModel(f, full_gen=True)
        candidates = list(model.candidates())
        target_segs = next(segs for _, segs in candidates if f.observe(segs) == target)
        target_v = model.violations(target_segs)
        margins = []
        for idx, segs in candidates:
            if f.observe(segs) == target:
                continue
            vio = model.violations(segs)
            endpoints = []
            for endpoint in (Q(0), Q(1, 12)):
                w = {**weights, 'ID_MINUS_ATR': endpoint}
                endpoints.append(sum(w[c] * (vio[c] - target_v[c]) for c in model.constraints))
            assert all(d >= 0 for d in endpoints) and any(d > 0 for d in endpoints)
            margins.append({'candidate': idx, 'margin_at_0': str(endpoints[0]),
                            'margin_at_1_12': str(endpoints[1])})
        development.append({'id': f.id, 'bad_candidates': len(margins), 'margins': margins})
    result = dict(utc=datetime.now(timezone.utc).isoformat(), ratio=str(ratio),
                  weights={k: str(v) for k, v in weights.items()}, rows=rows,
                  development_open_interval_certificate=development,
                  passed=all(x['target_wins_exclusively'] for x in rows),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  scope='Finite exact full-product check; universal dominance bridge recorded separately')
    certificate.write('gua_battery_witness.json', result, paths.REPO / 'results/predictions')
    assert result['passed']


if __name__ == '__main__':
    main()
