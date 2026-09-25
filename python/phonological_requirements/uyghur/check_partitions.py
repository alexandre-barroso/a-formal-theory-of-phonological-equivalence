from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict, Counter
import csv, hashlib, json

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DATA = REPO / 'data/uyghur'
O = REPO / 'build/uyghur/partition_check'
O.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    with p.open(newline='', encoding='utf-8') as f:
        return list(csv.DictReader(f))
expected = {'clean_morphology_panel_v3.csv': 'd3ee14c623af2e0c6f7f842d68adfcadc188d05bde8d664b34da020d4964b130', 'clean_transfer_root_table_v2.csv': '8ed463dba3e78218a1625bc073c58562ff4c07d1bbc83ce06e52c4a12e31ecb0', 'uyghur_inner_fold_manifest_v1.csv': '314b784a12cfa5406fff3b673790aa881ab6e0e94ac2750e75c356ddf46a128e', 'uyghur_outer_fold_manifest_v1.csv': 'fded6710f48c1b63cfec4e8939537836c2a15b43c72b75d789d0a57b7ba448a6'}
for relative, digest in expected.items():
    assert sha(DATA / relative) == digest, relative
panel = read(DATA / 'clean_morphology_panel_v3.csv')
table = {r['root']:r for r in read(DATA / 'clean_transfer_root_table_v2.csv')}
inputs, covered, side, side_covered, sources = (defaultdict(Counter) for _ in range(5))
for row in panel:
    root, morph, n = row['root'], row['morphology'], int(row['incidences'])
    if morph in {'dat', 'loc'}:
        inputs[root][morph] += n
        if row['primary_observer_covered'].lower() == 'true':
            covered[root][morph] += n
            sources[root][row['source']] += n
    elif morph == 'acc':
        side[root][morph] += n
        if row['primary_observer_covered'].lower() == 'true':
            side_covered[root][morph] += n
roots = sorted(inputs)
assert len(roots) == 524
strata = {r:table[r]['last_two'] + '|' + table[r]['all_harmonic_vowels_unrounded'].lower() for r in roots}
seed = 'AUDIT-POLISH-2.0-CODEX-UYGHUR-NOMINAL-V1'
def partitions(members, k, salt):
    
    result = {}
    for stratum in sorted(set(strata[r] for r in members)):
        prefix = (salt + '\x00' + stratum).encode('utf-8')
        ordered = sorted((r for r in members if strata[r] == stratum),
                         key=lambda r: hashlib.sha256(prefix + b'\x00' + r.encode('utf-8')).digest())
        offset = int.from_bytes(hashlib.sha256(prefix).digest()[:4], 'big') % k
        result.update({r:(offset+i)%k for i,r in enumerate(ordered)})
    return result
outer = partitions(roots, 5, seed)
outer_path = DATA / 'uyghur_outer_fold_manifest_v1.csv'
inner_path = DATA / 'uyghur_inner_fold_manifest_v1.csv'
assert sha(outer_path) == expected['uyghur_outer_fold_manifest_v1.csv']
assert sha(inner_path) == expected['uyghur_inner_fold_manifest_v1.csv']
outer_rows, inner_rows = read(outer_path), read(inner_path)
assert len(outer_rows) == len(roots)
assert {r['root']:int(r['outer_fold']) for r in outer_rows} == outer
for row in outer_rows:
    r = row['root']
    assert int(row['target_intended_incidences']) == sum(inputs[r].values())
    assert int(row['target_covered_incidences']) == sum(covered[r].values())
    assert int(row['acc_intended_incidences']) == sum(side[r].values())
    assert int(row['acc_covered_incidences']) == sum(side_covered[r].values())
for fold in range(5):
    train = [r for r in roots if outer[r] != fold]
    ours = partitions(train, 3, seed + '\x00inner\x00' + str(fold))
    theirs = {r['root']:int(r['inner_fold']) for r in inner_rows if int(r['outer_fold']) == fold}
    assert len(theirs) == sum(int(r['outer_fold']) == fold for r in inner_rows)
    assert ours == theirs and set(ours).isdisjoint(r for r in roots if outer[r] == fold)
result = {
    'utc':datetime.now(timezone.utc).isoformat(),
    'status':'INDEPENDENT_PANEL_DENOMINATORS_AND_ALL_NESTED_FOLDS_PASS',
    'inputs':expected,
    'outer_manifest_sha256':sha(outer_path), 'inner_manifest_sha256':sha(inner_path),
    'intended_roots':len(roots), 'scored_roots':sum(bool(covered[r]) for r in roots),
    'intended_incidences':sum(sum(inputs[r].values()) for r in roots),
    'covered_incidences':sum(sum(covered[r].values()) for r in roots),
    'roots_with_any_side_input':sum(bool(side[r]) for r in roots),
    'roots_with_covered_side_input':sum(bool(side_covered[r]) for r in roots),
    'outer_folds':5, 'inner_folds_per_outer':3, 'inner_manifest_rows':len(inner_rows),
    'scope':'Independent no-fit manifest check against previously independently reconstructed panel. Fitting and empirical interpretation have separate checks.',
}
assert [result[k] for k in ['scored_roots','intended_incidences','covered_incidences','roots_with_any_side_input','roots_with_covered_side_input']] == [515,59632,58577,377,369]
(O / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
