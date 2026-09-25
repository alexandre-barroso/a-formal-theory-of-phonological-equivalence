
def run(data, work):
    from pathlib import Path
    from collections import defaultdict,Counter
    import csv,json,hashlib
    O=Path(work);D=Path(data)
    words1={'wubache','wugufen','wubaxia','wubaoche','wubaoshu','wubaixia'}
    words4={w+t for w in ['wubaoshui','wuduorou','wubamai','wudaixiang','wubupao'] for t in ['3','4']}
    results=[]
    for file in sorted(D.glob('*.csv')):
        groups=defaultdict(list)
        with file.open(encoding='utf-8-sig') as f:
            for r in csv.DictReader(f):groups[tuple(r[k] for k in ['speaker','word','startTime','endTime'])].append(r)
        for rs in groups.values():
            assert sorted(int(r['step']) for r in rs)==list(range(21))
            for key in rs[0]:
                if key not in ['step','pitch']:assert len({r[key] for r in rs})==1
        tokens=[v[0] for v in groups.values()];good=[r for r in tokens if r['quality']=='good']
        rec={'path':file.name,'sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'rows':sum(map(len,groups.values())),'tokens':len(tokens),'speakers':sorted({r['speaker'] for r in tokens},key=int),'columns':list(tokens[0])}
        if file.name=='Exp1Data.csv':
            target=[r for r in tokens if r['word'] in words1]
            allgood=[r for r in target if r['quality']=='good']
            primary=[r for r in allgood if r['ur'] in ['231','331','211','311']]
            rec.update(test_word_tokens=len(target),test_word_good=len(allgood),strict_good_valid_UR=len(primary),cells={'|'.join(k):v for k,v in Counter((r['ur'],r['sr']) for r in primary).items()},anomalous_test_word_UR=Counter(r['ur'] for r in target if r['ur'] not in ['231','331','211','311']))
            assert len(primary)==985
            rec['discrepancy']='Paper planned1056 and excluded71; deposit1055 target-word tokenblocks includes one extra2311 item, leaving1054 canonical-UR blocks and69 non-good. Strict985 included tokens reproduce source table; two planned tokens have no canonical-UR block in deposit. No invented missing records.'
        elif file.name=='Exp2Data.csv':
            target=[r for r in tokens if r['word'] in words4]
            primary=[r for r in target if r['quality']=='good'];cells=Counter()
            for r in primary:
                b,c=r['toneSandhiBefore'],r['toneSandhiCurrent'];assert b in ['none','yes','no'] and c in ['none','yes','no']
                first='2' if b=='none' else '3';second=r['word'][-1]
                u=first+second+'4';v=('2' if b=='yes' else first)+('3' if c=='yes' else second)+'4';cells[u+'|'+v]+=1
            assert len(primary)==1521
            rec.update(test_word_tokens=len(target),strict_good=len(primary),cells=dict(cells),discrepancy='Paper planned1600/excluded79; deposit1606 target-word blocks/85 non-good. Strict1521 matches source table; extra six non-good tokens are not silently deleted from provenance.')
        else:rec['unit_warning']='First-syllable measurement stream from original Experiment2, not third independent study. Ten source-specific lexical forms do not identify all first-syllable controls; no new first-syllable fit here.'
        results.append(rec)
    (O/'results/old_source_reconciliation.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
