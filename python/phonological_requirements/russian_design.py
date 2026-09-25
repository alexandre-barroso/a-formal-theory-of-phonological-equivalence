from pathlib import Path
from functools import lru_cache
import csv
import hashlib
import itertools
import re
import unicodedata
import numpy as np

ABSENT = '∅'
MAP = dict(zip('пбмфвкгхтдсзнрлйаоеиуы', ['p','b','m','f','v','k','g','x','t','d','s','z','n','r','l','j','a','o','e','i','u','i'])) | {'ц':'ts','ш':'sh','ж':'zh','ч':'ch','щ':'shshj'}
PAL = set('pbmfvkgxtdsznrl')

def transliterate(word):
    result = []
    for c in word:
        if c == 'ь':
            if result and result[-1] in PAL: result[-1] += 'j'
            continue
        if c in 'еи' and result and result[-1] in PAL: result[-1] += 'j'
        result.append(MAP[c])
    return ' '.join(result)

def dictionary_tokens(word):
    word = ''.join(c for c in unicodedata.normalize('NFD', word) if not unicodedata.combining(c))
    for a,b in [('ʃʃʲ','shshj'),('ʃʃ','shshj'),('ʧʲ','ch'),('ʦ','ts'),('ʃ','sh'),('ʒ','zh'),('ʲ','j')]: word=word.replace(a,b)
    return ' '.join(t for t in word.split() if t!='-')

def fold(prefix, value):
    return int(hashlib.sha256((prefix+value).encode()).hexdigest(),16) % 5

class RussianDesign:
    def __init__(self, chart_path, patterns_path):
        with Path(chart_path).open() as f: table=list(csv.reader(f,delimiter='\t'))
        self.chart={row[0]:dict(zip(table[0][1:],row[1:])) for row in table[1:]}
        self.features={t: d|{'syllabic':d['syll'],'seg':'+'} for t,d in self.chart.items()}
        with Path(patterns_path).open() as f: header=next(csv.reader(f,delimiter='\t'))
        self.patterns=header[7:140]
        if header[140:273] != self.patterns or len(self.patterns)!=133: raise ValueError('Pattern inventory changed')
        self.groups=[]
        for p in self.patterns:
            if not re.fullmatch(r'\^?\[[^]]+\](?: \[[^]]+\])*\$?',p):raise ValueError(p)
            groups=tuple(tuple((v[1:],v[0]) for v in g.split(',')) for g in re.findall(r'\[([^]]+)\]',p))
            self.groups.append((groups,p.startswith('^'),p.endswith('$')))
        self.token_matches={t:tuple(tuple(all(self.features[t].get(k)==s for k,s in g) for g in groups) for groups,_,_ in self.groups) for t in self.chart}

    def generate(self, base):
        j=max(i for i,t in enumerate(base) if self.chart[t]['syll']=='+');k=j-1
        eligible=k>=0 and self.chart[base[k]]['syll']=='-'
        target=self.chart[base[k]]|{'back':'+'} if eligible else None
        matches=[t for t,d in self.chart.items() if d==target] if eligible else []
        if len(matches)>1:raise ValueError((base,matches))
        replacement=matches[0] if matches else base[k]
        ref=tuple(base)+('a',);states=[]
        for delete,depal in itertools.product((False,True),repeat=2):
            y=list(ref)
            if delete:y[j]=ABSENT
            if depal and eligible:y[k]=replacement
            y=tuple(y)
            if y not in states:states.append(y)
        return ref,states,j,k

    @lru_cache(maxsize=25000)
    def marks(self, tokens, orientation):
        live=[j for j,t in enumerate(tokens) if t!=ABSENT]
        match=np.zeros((133,len(tokens)),np.int16);pressure=np.zeros_like(match)
        for i,(groups,start,end) in enumerate(self.groups):
            endpoint=-1 if orientation=='right' else 0
            for j in live:pressure[i,j]=self.token_matches[tokens[j]][i][endpoint]
            for pos in range(len(live)-len(groups)+1):
                if start and pos!=0:continue
                if end and pos+len(groups)!=len(live):continue
                if all(self.token_matches[tokens[j]][i][g] for g,j in enumerate(live[pos:pos+len(groups)])):
                    anchor=live[pos+len(groups)-1] if orientation=='right' else live[pos]
                    match[i,anchor]=1
        return match,pressure

    def coefficients(self, bases):
        arrays={k:[] for k in ['right_old','right_new','left_old','left_new','current','faithfulness','base_marks']}
        metadata=[];ranges={}
        for base_string in sorted(set(bases)):
            base=tuple(base_string.split());ref,states,j,k=self.generate(base);start=len(metadata)
            reference={o:self.marks(ref,o)[0] for o in ['right','left']}
            bm=self.marks(base,'right')[0].sum(axis=1)
            for y in states:
                for o in ['right','left']:
                    now,p=self.marks(y,o)
                    arrays[o+'_old'].append((reference[o]*p).sum(axis=1))
                    arrays[o+'_new'].append(((1-reference[o])*now).sum(axis=1))
                current=self.marks(y,'right')[0].sum(axis=1)
                if not np.array_equal(current,self.marks(y,'left')[0].sum(axis=1)):raise ValueError('Current orientation mismatch')
                changed=(y[k]!=ref[k])
                ff=[int(y[j]==ABSENT),int(changed and self.chart[ref[k]]['lateral']=='+'),int(changed and self.chart[ref[k]]['lateral']=='-')]
                arrays['current'].append(current);arrays['faithfulness'].append(ff);arrays['base_marks'].append(bm)
                metadata.append({'base':base_string,'aligned':y,'output':' '.join(t for t in y if t!=ABSENT)})
            ranges[base_string]=[start,len(metadata)]
        return {k:np.asarray(v,dtype=np.int16) for k,v in arrays.items()},ranges,metadata

def read_responses(path):
    with Path(path).open() as f: raw=list(csv.DictReader(f,delimiter='\t'))
    rows=[]
    for i,r in enumerate(raw,1):
        if r['C'] not in ('2','3'):continue
        k=1 if r['position']=='0' else int(r['position'])
        base=transliterate(r['prefix']+r['cluster'][:k]+r['vowel']+r['cluster'][k:])
        rows.append(r|{'design_row':i,'model_base':base,'presented_faithful':base+' a','presented_deletion':transliterate(r['prefix']+r['cluster']+'а'),'person_test':fold('rus-person-v1|',r['userCode']) in (0,1),'cluster_test':fold('rus-cluster-v1|',r['cluster']) in (0,1)})
    return raw,rows
