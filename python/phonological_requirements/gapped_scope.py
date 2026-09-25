from pathlib import Path
from fractions import Fraction as F
import itertools, json, hashlib

from phonological_requirements import paths
from phonological_requirements import gapped_inventory as G
from phonological_requirements import recon_gouskova as OT
from phonological_requirements.evaluate import activation, coefficients
from phonological_requirements.frag_voice import sigma, struct

PAIRS = list(zip('ptksfčţxʂʃ', 'bdgzvǰʣɣʐʒ'))
VOICED = set('bdgzvǰʣɣʐʒ')
UNSPEC = dict(zip('ČŢXƩ', ['čǰ','ţʣ','xɣ','ʃʒ']))
CHOICES = {c: pair for pair in PAIRS for c in pair} | UNSPEC
CLASSES = {'AFF':set('čǰţʣČŢ'), 'DORFRIC':set('xɣX'), 'PALFRIC':set('ʃʒƩ')}

def parse(text):
    segs, words, word = [], [], 0
    for c in text:
        if c == ' ': word += 1
        elif c != '-':
            segs.append(c); words.append(word)
    return segs, words

def voice(c):
    return None if c in UNSPEC else c in VOICED

def independent(u, y, words, names):
    out = {k:[0,0] for k in names}
    for i, (a,b) in enumerate(zip(u,y)):
        if a not in CHOICES: continue
        va, vb = voice(a), voice(b)
        changed = va is not None and va != vb
        out['ID_VOICE'][0] += int(changed)
        preson = i+1 < len(u) and words[i] == words[i+1] and u[i+1] in 'aeioumn lrwj'.replace(' ','')
        out['ID_PRESON_VOICE'][0] += int(changed and preson)
        if vb is True:
            out['NO_VOICE'][0 if va is True else 1] += 1
            for k, chars in CLASSES.items():
                if 'NO_VOICED_'+k in out and a in chars:
                    out['NO_VOICED_'+k][0 if va is True else 1] += 1
        if i+1 < len(u) and u[i+1] in CHOICES:
            va2, vb2 = voice(u[i+1]), voice(y[i+1])
            old = va is not None and va2 is not None and va != va2
            current = vb is not None and vb2 is not None and vb != vb2
            if current: out['AGREE_BOTH'][0 if old else 1] += 1
    return {k:tuple(v) for k,v in out.items()}

def independent_rows(text, names):
    u, words = parse(text)
    for y in itertools.product(*(CHOICES.get(c,(c,)) for c in u)):
        s = ''.join((' ' if i and words[i] != words[i-1] else '')+c for i,c in enumerate(y))
        yield s, independent(u,y,words,names)

def cost(cf,w,lam):
    return sum(w[k]*(a+lam*b) for k,(a,b) in cf.items())

def native_pair(text, output, declarations):
    u,words = parse(text); y,ywords = parse(output)
    assert len(u)==len(y) and words==ywords
    sg=sigma('binary'); ref=struct(u,None,words); candidate=struct(y,None,words)
    assert candidate.well_formed(ref)[0]
    got=coefficients(sg,ref,candidate,declarations,activation(sg,ref,declarations))
    expected=independent(u,y,words,declarations)
    assert got==expected,(text,output,got,expected)
    return expected

def main():
    from phonological_requirements.observations import GOUSKOVA_21, GOUSKOVA_OTHER
    cases={}
    for stem, outputs in GOUSKOVA_21.items():
        cases.update(zip([stem+'-am',stem,stem+' ʐe',stem+' to'],outputs))
    cases.update(GOUSKOVA_OTHER)
    fingerprints={}
    for name in ['gapped_inventory.py','frag_voice.py','evaluate.py','recon_gouskova.py','observations.py']:
        p=Path(__file__).resolve().parent/name
        fingerprints[name]=hashlib.sha256(p.read_bytes()).hexdigest()
    results=[]; checks=0; comparisons=0
    for branch,ds in [('L',G.DECL_L),('R',G.DECL_R),('MSC',G.DECL_L)]:
        for lam in [F(1,8),F(1)]:
            w=dict(G.W_RU)
            if branch=='R' and lam==1:
                for k in CLASSES:w['NO_VOICED_'+k]=1
            for inp, expected in cases.items():
                lex=G.lexical_form(inp,branch)
                if branch=='MSC': assert not set(lex)&set('ǰʣɣʒ')
                exact=list(independent_rows(lex,ds)); e=G.evaluate(lex,ds,w,lam)
                native={s:(cf,v) for s,cf,v in e['rows']}
                assert len(exact)==len(native)==2**sum(c in CHOICES for c in parse(lex)[0])
                assert len({s for s,cf in exact})==len(exact)
                for s,cf in exact:
                    assert cf==native[s][0],(lex,s,cf,native[s][0])
                    assert cost(cf,w,lam)==native[s][1]
                    checks+=1; comparisons+=2*len(ds)
                best=min(cost(cf,w,lam) for s,cf in exact)
                winners=sorted(s for s,cf in exact if cost(cf,w,lam)==best)
                assert winners==e['winners']==[expected.replace('-','')],(branch,lam,inp,winners,expected)
                results.append({'branch':branch,'lambda':str(lam),'input':inp,'lexical':lex,'winners':winners,'candidates':len(exact),'score':str(best),'weights':{k:w[k] for k in ds}})
    typology={}
    inputs=('bat','pad','adpat','atbat')
    name_map={'Agree':'AGREE_BOTH','Id-pson':'ID_PRESON_VOICE','*ObsVoice':'NO_VOICE','Ident':'ID_VOICE'}
    for order in itertools.permutations(name_map):
        pattern=[]
        for u in inputs:
            rows=list(independent_rows(u,G.DECL_L))
            profiles={s:tuple(sum(cf[name_map[k]]) for k in order) for s,cf in rows}
            low=min(profiles.values()); winners=sorted(s for s,v in profiles.items() if v==low)
            assert winners==OT.ot_winners(u,order)
            pattern.append(winners)
        typology[' > '.join(order)]=pattern
    long=[]
    for n in list(range(1,9))+[16,52,128]:
        inp='t'*n+'ba'; target='d'*n+'ba'; competitor='t'*n+'pa'
        a=native_pair(inp,target,G.DECL_R); b=native_pair(inp,competitor,G.DECL_R)
        assert a['ID_VOICE']==(n,0) and a['NO_VOICE']==(1,n)
        assert b['ID_VOICE']==(1,0) and b['ID_PRESON_VOICE']==(1,0)
        assert b['NO_VOICE']==(0,0)
        for lam in [F(0),F(1,8),F(1)]:
            c1=cost(a,G.W_RU,lam); c2=cost(b,G.W_RU,lam)
            assert c1==n*(1+4*lam)+4 and c2==81
            long.append({'n':n,'lambda':str(lam),'target_cost':str(c1),'competitor_cost':str(c2),'target_strictly_loses':c2<c1})
    assert next(x for x in long if x['n']==52 and x['lambda']=='1/8')['target_strictly_loses']
    summary={'finite_inputs':len(cases),'branch_lambda_input_comparisons':len(results),'complete_candidate_checks':checks,'old_new_coefficient_comparisons':comparisons,'rankings':24,'ranking_patterns':len({json.dumps(p) for p in typology.values()}),'long_native_candidate_checks':22,'scope':'Fixed segment identity, binary voiced outputs, preserved word boundaries. MSC input admissibility excludes the four voiced gap symbols; this is a finite fragment, not every lexical exception in the source. L remains the distinct underspecification alternative. Long inputs are constructed diagnostics, not attested Russian data.','long_domain_conclusion':'For kappa=I+lambda*V>0 some n has n*kappa+V>I+P, so target fails even pairwise. If kappa=0 the final /t/ diagnostic ties. Universal inequality proof separate from finite native coefficient correspondence.','source_sha256':'48f7a88eec98ca2edb2f612ac66c36b756f9aefc567445be55454d8463ef858a','input_hashes':fingerprints}
    output={'summary':summary,'finite':results,'rankings':typology,'long':long}
    paths.CERTIFICATES.mkdir(parents=True,exist_ok=True)
    (paths.CERTIFICATES/'gapped_scope.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
