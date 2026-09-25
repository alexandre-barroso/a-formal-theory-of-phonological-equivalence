from pathlib import Path
import json,itertools,datetime
from . import certificate
OBS={'gahe':'gahe','gaht':'gat','mae':'mae','mat':'mat','mar@mu':'marmu','ah@pt':'ah@pt','ah@pr@mu':'ah@pr@mu','gahr@mu':'gar@mu','ah@pe':'ahpe'}
V=set('a@ue');C=set('ghrmpt')
def active(s,i,rule):
 left=[x for x in s[:i] if x is not None];right=[x for x in s[i+1:] if x is not None]
 return s[i]=='h' and bool(right) and right[0] in C if rule=='H' else s[i]=='@' and len(left)>=2 and left[-1] in C and left[-2] in V and len(right)>=2 and right[0] in C and right[1] in V
def app(s,i,rule):
 c=list(s)
 if active(s,i,rule):c[i]=None
 return c
def onepass(s,order):
 c=list(s)
 for rule in order:c=[None if active(c,i,rule) else x for i,x in enumerate(c)]
 return ''.join(x for x in c if x is not None)
def block(s,order,rtl):
 c=list(s)
 for i in (reversed(range(len(s))) if rtl else range(len(s))):
  for rule in order:c=app(c,i,rule)
 return ''.join(x for x in c if x is not None)
rows=[]
for order in ['HS','SH']:
 for kind,rtl in [('global',False),('blockLR',False),('blockRL',True)]:
  predictions={s:(onepass(s,order) if kind=='global' else block(s,order,rtl)) for s in OBS}
  bad={s:[OBS[s],t] for s,t in predictions.items() if t!=OBS[s]};assert bad
  rows.append({'order':order,'architecture':kind,'predictions':predictions,'failures':bad})
def finalblock(s,order):
 c=list(s)
 for i in range(len(s)):
  for target in order:
   if c[i]==target and all(x is None for x in c[i+1:]):c[i]=None
 return ''.join(x for x in c if x is not None)
for order in ['CV','VC']:
 assert finalblock('CVC',order)=='CV' and finalblock('CVCV',order)=='CVC'
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':'frischoffRasin2026absenceCruciallySimultaneous','source_pages':[12,13,39,40,41],'SH_full_paradigm_evaluations':54,'architectures':rows,'finalCVblock_positive_checks':4,'scope':'Exactly stated obligatory two-rule architectures; no unrestricted serial-theory exclusion.'}
certificate.write('serial_comparison.json',out);print(json.dumps(out))
