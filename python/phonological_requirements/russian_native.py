from pathlib import Path
import argparse
import json
import numpy as np
from .core import ABSENT, And, Decl, Feat, NodeId, Not, Present, RelDecl, Resolves, Scope, Sigma, Slot, SortDecl, Struct, Positional, SameFeat
from .evaluate import activation, coefficients
from .certificate import write
from .russian_design import RussianDesign
from .russian_secondary import checked_inputs


def compile_pattern(groups,left,right,i):
    scope=Scope(same=('word',),label='word');slots=[Slot('s','Or','subject')];names=['s']
    for j in range(1,len(groups)):
        name=f'p{j}';slots.append(Slot(name,'Or','trigger',kind='step' if j==1 else 'stepof',relation='succ',scope=scope,direction=-1,policy='dynamic',of=None if j==1 else f'p{j-1}'));names.append(name)
    chronological=list(reversed(names));context=[Present('s')]
    for name,group in zip(chronological[:-1],groups[:-1]):
        context.append(Resolves(name));context.extend(Feat(k,name,sign) for k,sign in group)
    if left:
        slots.append(Slot('before','Or','trigger',kind='step' if chronological[0]=='s' else 'stepof',relation='succ',scope=scope,direction=-1,policy='dynamic',of=None if chronological[0]=='s' else chronological[0]));context.append(Not(Resolves('before')))
    if right:context.append(Positional('last_live_of','s','word'))
    consequence=Not(And((Present('s'),)+tuple(Feat(k,'s',sign) for k,sign in groups[-1])))
    return Decl(f'RUS_PATTERN_{i:03d}','Or',tuple(slots),And(tuple(context)),consequence,scope=scope)


def structure(tokens):
    nodes=tuple(NodeId('Or','lex',i) for i in range(len(tokens)))
    return Struct({'seg':nodes},dict(zip(nodes,tokens)),{n:{'word':0} for n in nodes})


def check(inputs,work,index,count):
    files=checked_inputs(inputs);design=RussianDesign(files['feature_chart_given_to_learners.txt'],files['sublexical_learner_predictions_with_faithfulness.txt'])
    features={t:d|{'present':True,'nuclear':d['syll']=='+'} for t,d in design.features.items()};features[ABSENT]={k:None for k in next(iter(features.values()))};features[ABSENT]['present']=False
    sigma=Sigma({'Or':SortDecl('Or','total','seg'),'Rel':SortDecl('Rel','derived','seg')},{'succ':RelDecl('succ','succession','Or','Or','Rel')},features,{'present':False},('word',))
    decls={f'RUS_PATTERN_{i:03d}':compile_pattern(*p,i) for i,p in enumerate(design.groups)}
    scope=Scope(same=('word',),label='word')
    faith={'MAXV':Decl('MAXV','Or',(Slot('s','Or','subject'),),Feat('syll','s','+','reference'),Present('s'),scope=scope,kind='faithfulness',locus_side='reference')}
    for name,sign in [('IDENT_LAT','+'),('IDENT_NONLAT','-')]:faith[name]=Decl(name,'Or',(Slot('s','Or','subject'),),And((Feat('syll','s','-','reference'),Feat('lateral','s',sign,'reference'))),SameFeat('back',('s','reference'),('s','current')),scope=scope,kind='faithfulness',locus_side='reference')
    if not all(d.well_typed(sigma)[0] for d in [*decls.values(),*faith.values()]):raise ValueError('Ill-typed declaration')
    metadata=json.loads((work/'metadata.json').read_text())['rows'];data=np.load(work/'design.npz');n=0
    for i,m in enumerate(metadata):
        if i%count!=index:continue
        ref=structure(tuple(m['base'].split())+('a',));s=structure(m['aligned'])
        if not s.well_formed(ref)[0]:raise ValueError('Malformed candidate')
        got=coefficients(sigma,ref,s,decls,activation(sigma,ref,decls));ff=coefficients(sigma,ref,s,faith,activation(sigma,ref,faith))
        if [got[k] for k in decls]!=list(zip(data['right_old'][i],data['right_new'][i])):raise ValueError(('Markedness bridge',i))
        if [ff[k] for k in faith]!=[(v,0) for v in data['faithfulness'][i]]:raise ValueError(('Faithfulness bridge',i))
        n+=1
    if n==0:raise ValueError('Empty native bridge shard')
    out={'status':'PASS','shard_index':index,'shard_count':count,'candidate_total':len(metadata),'checked_candidates':n,'markedness_pairs':n*133,'faithfulness_pairs':n*3,'scope':'Actual native typed interpreter against independent token-window coefficients on the declared exhaustive modular shard.'}
    write(f'russian_native_{index}_{count}.json',out,work);print(out)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--inputs',type=Path,required=True);p.add_argument('--work',type=Path,required=True);p.add_argument('--shard',default='0/100');a=p.parse_args();i,n=map(int,a.shard.split('/'))
    if not 0<=i<n:raise ValueError('Invalid shard')
    check(a.inputs,a.work,i,n)
