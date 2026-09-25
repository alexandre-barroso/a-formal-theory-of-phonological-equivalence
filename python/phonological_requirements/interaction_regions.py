from pathlib import Path
from fractions import Fraction as F
import json,itertools,sys,datetime,hashlib
from . import paths, certificate
SPEC={'patterns': {'counterfeeding': {'kind': 'schematic counterfeeding control',
                                 'alphabet': {'k': ['C'], 'V': ['V'], 'N': ['C', 'N'], 'T': ['C', 'T']},
                                 'rules': [['NDEL', 'N', [], ['#'], None], ['TDEL', 'T', ['N'], ['#'], None]],
                                 'mappings': {'kVN': 'kV', 'kVNT': 'kVN', 'kVNV': 'kVNV'},
                                 'options': {'N': ['N', None], 'T': ['T', None]}},
              'feeding': {'kind': 'schematic reversal of the Catalan counterfeeding control',
                          'alphabet': {'k': ['C'], 'V': ['V'], 'N': ['C', 'N'], 'T': ['C', 'T']},
                          'rules': [['NDEL', 'N', [], ['#'], None], ['TDEL', 'T', ['N'], ['#'], None]],
                          'mappings': {'kVN': 'kV', 'kVNT': 'kV', 'kVNV': 'kVNV'},
                          'options': {'N': ['N', None], 'T': ['T', None]}},
              'counterbleeding': {'kind': 'schematic counterbleeding control',
                                  'alphabet': {'k': ['C', 'k'],
                                               'kj': ['C'],
                                               'i': ['V', 'i'],
                                               'I': ['V'],
                                               'm': ['C'],
                                               't': ['C'],
                                               'n': ['C'],
                                               'a': ['V']},
                                  'rules': [['PAL', 'k', [], ['i'], 'kj'],
                                            ['SYNC', 'i', [], ['C', 'V'], None]],
                                  'mappings': {'kim': 'kjim', 'timIn': 'tmIn', 'kimIn': 'kjmIn'},
                                  'options': {'k': ['k', 'kj'], 'i': ['i', None]}},
              'bleeding': {'kind': 'schematic reversal of the Bedouin counterbleeding control',
                           'alphabet': {'k': ['C', 'k'],
                                        'kj': ['C'],
                                        'i': ['V', 'i'],
                                        'I': ['V'],
                                        'm': ['C'],
                                        't': ['C'],
                                        'n': ['C'],
                                        'a': ['V']},
                           'rules': [['PAL', 'k', [], ['i'], 'kj'], ['SYNC', 'i', [], ['C', 'V'], None]],
                           'mappings': {'kim': 'kjim', 'timIn': 'tmIn', 'kimIn': 'kmIn'},
                           'options': {'k': ['k', 'kj'], 'i': ['i', None]}},
              'mutual_counterbleeding': {'kind': 'schematic mutual counterbleeding control',
                                         'alphabet': {'g': ['C'],
                                                      'a': ['V'],
                                                      'h': ['C', 'h'],
                                                      'w': ['C', 'w'],
                                                      'u': ['V'],
                                                      't': ['C'],
                                                      'd': ['C'],
                                                      'r': ['C'],
                                                      'e': ['V'],
                                                      'm': ['C']},
                                         'rules': [['HDEL', 'h', [], ['C'], None],
                                                   ['VOC', 'w', ['C'], ['#'], 'u']],
                                         'mappings': {'gaht': 'gat',
                                                      'darw': 'daru',
                                                      'maw': 'maw',
                                                      'gahe': 'gahe',
                                                      'gahw': 'gau'},
                                         'options': {'h': ['h', None], 'w': ['w', 'u']}},
              'mutual_bleeding_h_first': {'kind': 'schematic mutual bleeding h first control',
                                          'alphabet': {'g': ['C'],
                                                       'a': ['V'],
                                                       'h': ['C', 'h'],
                                                       'w': ['C', 'w'],
                                                       'u': ['V'],
                                                       't': ['C'],
                                                       'd': ['C'],
                                                       'r': ['C'],
                                                       'e': ['V'],
                                                       'm': ['C']},
                                          'rules': [['HDEL', 'h', [], ['C'], None],
                                                    ['VOC', 'w', ['C'], ['#'], 'u']],
                                          'mappings': {'gaht': 'gat',
                                                       'darw': 'daru',
                                                       'maw': 'maw',
                                                       'gahe': 'gahe',
                                                       'gahw': 'gaw'},
                                          'options': {'h': ['h', None], 'w': ['w', 'u']}},
              'mutual_bleeding_voc_first': {'kind': 'schematic mutual bleeding voc first control',
                                            'alphabet': {'g': ['C'],
                                                         'a': ['V'],
                                                         'h': ['C', 'h'],
                                                         'w': ['C', 'w'],
                                                         'u': ['V'],
                                                         't': ['C'],
                                                         'd': ['C'],
                                                         'r': ['C'],
                                                         'e': ['V'],
                                                         'm': ['C']},
                                            'rules': [['HDEL', 'h', [], ['C'], None],
                                                      ['VOC', 'w', ['C'], ['#'], 'u']],
                                            'mappings': {'gaht': 'gat',
                                                         'darw': 'daru',
                                                         'maw': 'maw',
                                                         'gahe': 'gahe',
                                                         'gahw': 'gahu'},
                                            'options': {'h': ['h', None], 'w': ['w', 'u']}},
              'mutual_counterfeeding': {'kind': 'hypothetical categorical paradigm; variable cases disputed',
                                        'alphabet': {'g': ['C'],
                                                     'a': ['V'],
                                                     'h': ['C', 'h'],
                                                     'r': ['C'],
                                                     '@': ['@', 'V'],
                                                     'm': ['C'],
                                                     'u': ['V'],
                                                     'p': ['C'],
                                                     'e': ['V'],
                                                     't': ['C']},
                                        'rules': [['HDEL', 'h', [], ['C'], None],
                                                  ['SYNC', '@', ['C', 'V'], ['C', 'V'], None]],
                                        'mappings': {'gahe': 'gahe',
                                                     'gaht': 'gat',
                                                     'mae': 'mae',
                                                     'mat': 'mat',
                                                     'mar@mu': 'marmu',
                                                     'ah@pt': 'ah@pt',
                                                     'ah@pr@mu': 'ah@pr@mu',
                                                     'gahr@mu': 'gar@mu',
                                                     'ah@pe': 'ahpe'},
                                        'options': {'h': ['h', None], '@': ['@', None]}},
              'fed_counterfeeding': {'kind': 'schematic local context; Lardil reconstructed separately',
                                     'alphabet': {'C': ['C', 'L'], 'V': ['V'], 'K': ['C', 'K']},
                                     'rules': [['APO', 'V', ['C', 'V'], ['#'], None],
                                               ['KDEL', 'K', [], ['#'], None]],
                                     'mappings': {'CVCVCV': 'CVCVC', 'CVCVK': 'CVCV', 'CVCVKV': 'CVCV'},
                                     'options': {'V': ['V', None], 'K': ['K', None]}},
              'mutual_counterfeeding_deletions': {'kind': 'hypothetical final deletion; block rival admits it',
                                                  'alphabet': {'C': ['C'], 'V': ['V']},
                                                  'rules': [['CDEL', 'C', [], ['#'], None],
                                                            ['VDEL', 'V', [], ['#'], None]],
                                                  'mappings': {'CVC': 'CV', 'CVCV': 'CVC'},
                                                  'options': {'C': ['C', None], 'V': ['V', None]}},
              'noniterative_simultaneous': {'kind': 'schematic noniterative simultaneous control',
                                            'alphabet': {'V': ['V'], 'C': ['C'], '@': ['@', 'V']},
                                            'rules': [['SYNC', '@', ['C', 'V'], ['C', 'V'], None]],
                                            'mappings': {'VC@C@CV': 'VCCCV'},
                                            'options': {'@': ['@', None]}},
              'noniterative_left_to_right': {'kind': 'schematic noniterative left to right control',
                                             'alphabet': {'V': ['V'], 'C': ['C'], '@': ['@', 'V']},
                                             'rules': [['SYNC', '@', ['C', 'V'], ['C', 'V'], None]],
                                             'mappings': {'VC@C@CV': 'VCC@CV'},
                                             'options': {'@': ['@', None]}},
              'noniterative_right_to_left': {'kind': 'schematic noniterative right to left control',
                                             'alphabet': {'V': ['V'], 'C': ['C'], '@': ['@', 'V']},
                                             'rules': [['SYNC', '@', ['C', 'V'], ['C', 'V'], None]],
                                             'mappings': {'VC@C@CV': 'VC@CCV'},
                                             'options': {'@': ['@', None]}},
              'self_counterfeeding': {'kind': 'schematic self counterfeeding control',
                                      'alphabet': {'u': ['V', 'rd'], 'y': ['V', 'y']},
                                      'rules': [['RND', 'y', ['rd'], [], 'u']],
                                      'mappings': {'uyy': 'uuy'},
                                      'options': {'y': ['y', 'u']}},
              'self_feeding': {'kind': 'schematic self feeding control',
                               'alphabet': {'u': ['V', 'rd'], 'y': ['V', 'y']},
                               'rules': [['RND', 'y', ['rd'], [], 'u']],
                               'mappings': {'uyy': 'uuu'},
                               'options': {'y': ['y', 'u']}},
              'self_counterbleeding': {'kind': 'schematic self counterbleeding control',
                                       'alphabet': {'p': ['C'],
                                                    'L': ['L', 'V'],
                                                    's': ['C'],
                                                    'v': ['C'],
                                                    'a': ['V']},
                                       'rules': [['SHORT', 'L', ['C', 'L'], [], 'a']],
                                       'mappings': {'pLsLvL': 'pLsava'},
                                       'options': {'L': ['L', 'a']}},
              'self_bleeding': {'kind': 'schematic self bleeding control',
                                'alphabet': {'p': ['C'], 'L': ['L', 'V'], 's': ['C'], 'v': ['C'], 'a': ['V']},
                                'rules': [['SHORT', 'L', ['C', 'L'], [], 'a']],
                                'mappings': {'pLsLvL': 'pLsavL'},
                                'options': {'L': ['L', 'a']}},
              'circular_chain_shift': {'kind': 'schematic circular chain shift control',
                                       'alphabet': {'X': ['C', 'X'],
                                                    'Y': ['C', 'Y'],
                                                    'A': ['A', 'V'],
                                                    'B': ['B', 'V'],
                                                    'Q': ['Q', 'V']},
                                       'rules': [['AB', 'A', ['X'], ['Y'], 'B'],
                                                 ['BQ', 'B', ['X'], ['Y'], 'Q'],
                                                 ['QA', 'Q', ['X'], ['Y'], 'A']],
                                       'mappings': {'XAY': 'XBY', 'XBY': 'XQY', 'XQY': 'XAY'},
                                       'options': {'A': ['A', 'B', 'Q'],
                                                   'B': ['A', 'B', 'Q'],
                                                   'Q': ['A', 'B', 'Q']}},
              'vipratisedha_blocking': {'kind': 'schematic vipratisedha blocking control',
                                        'alphabet': {'i': ['V', 'i'],
                                                     'k': ['C', 'k'],
                                                     'kj': ['C'],
                                                     'ts': ['C'],
                                                     'a': ['V']},
                                        'rules': [['PAL', 'k', [], ['i'], 'kj'],
                                                  ['AFF', 'k', ['i'], [], 'ts']],
                                        'mappings': {'aki': 'akji', 'ika': 'itsa', 'iki': 'iki'},
                                        'options': {'k': ['k', 'kj', 'ts']}},
              'vipratisedha_first_wins': {'kind': 'schematic vipratisedha first wins control',
                                          'alphabet': {'i': ['V', 'i'],
                                                       'k': ['C', 'k'],
                                                       'kj': ['C'],
                                                       'ts': ['C'],
                                                       'a': ['V']},
                                          'rules': [['PAL', 'k', [], ['i'], 'kj'],
                                                    ['AFF', 'k', ['i'], [], 'ts']],
                                          'mappings': {'aki': 'akji', 'ika': 'itsa', 'iki': 'ikji'},
                                          'options': {'k': ['k', 'kj', 'ts']}},
              'changtin': {'kind': 'schematic reconstruction of source-reported Changtin',
                           'alphabet': {'M': ['M', 'V'], 'R': ['R', 'V'], 'H': ['V'], 'L': ['V']},
                           'rules': [['MR', 'M', [], ['R'], 'L'], ['RM', 'R', [], ['M'], 'H']],
                           'mappings': {'MR': 'LR', 'RM': 'HM', 'MRM': 'LHM', 'RMR': 'HLR'},
                           'options': {'M': ['M', 'L'], 'R': ['R', 'H']}}}}
MODES={'discharge':(True,True),'retain':(False,False),'ltr':(True,False),'rtl':(False,True)}
def toks(text,alphabet):
 out=[]
 while text:
  matches=[x for x in alphabet if text.startswith(x)]
  assert matches
  x=max(matches,key=len);out.append(x);text=text[len(x):]
 return tuple(out)
def kand(xs):
 return False if False in xs else (None if None in xs else True)
def kor(xs):
 return True if True in xs else (None if None in xs else False)
def kn(x):return None if x is None else not x
def rule_read(p,s,i,rule,mode):
 _,target,lctx,rctx,out=rule
 left=[j for j in range(i-1,-1,-1) if s[j] is not None];right=[j for j in range(i+1,len(s)) if s[j] is not None]
 slots={**{'l'+str(k+1):left[k] if k<len(left) else None for k in range(2)},**{'r'+str(k+1):right[k] if k<len(right) else None for k in range(2)},'t':i}
 def ctx(side,decl):
  return all((slots[side+str(k+1)] is None if c=='#' else slots[side+str(k+1)] is not None and c in p['alphabet'][s[slots[side+str(k+1)]]]) for k,c in enumerate(decl))
 lc,rc=ctx('l',lctx),ctx('r',rctx)
 ant=kand([None if s[i] is None else target in p['alphabet'][s[i]],lc,rc]) is True
 carry=MODES[mode];carried=(not carry[0] or lc) and (not carry[1] or rc)
 repair=s[i] is None if out is None else (None if s[i] is None else s[i]==out)
 q=kor([not carried,repair])
 keynames=['t']+(['l'+str(k+1) for k in range(len(lctx))] if carry[0] else [])+(['r'+str(k+1) for k in range(len(rctx))] if carry[1] else [])
 return (ant,q is not None,q is True),tuple(slots[k] for k in sorted(keynames))
def faiths(p):
 pairs=[(r[1],r[4]) for r in p['rules']]
 for sym,opts in p['options'].items():
  cls=sym if sym in p['alphabet'][sym] else min(p['alphabet'][sym])
  pairs += [(cls,x) for x in opts if x!=sym]
 return dict(sorted({('MAX_'+a if b is None else 'IDENT_'+a+'_'+b):(a,b) for a,b in pairs}.items()))
def generate(p,s):return itertools.product(*[p['options'].get(c,[c]) for c in s])
def surface(s):return ''.join(x for x in s if x is not None)
def coeff(p,orig,s,modes,subject=False):
 out={}
 for rule,mode in zip(p['rules'],modes):
  oldreads=[rule_read(p,orig,i,rule,mode) for i in range(len(orig))]
  marked={k for (a,d,g),k in oldreads if a and d and not g}
  old=new=0
  for i in range(len(s)):
   (c,d,g),key=rule_read(p,s,i,rule,mode);(a,ad,ag),_=oldreads[i]
   retained=key in marked if subject else a and ad and not ag
   old+=int(d and not g and retained);new+=int(d and not g and not retained and c)
  out[rule[0]]=[old,new]
 for name,(target,value) in faiths(p).items():
  out[name]=[sum(target in p['alphabet'][o] and (c is None if value is None else c==value) for o,c in zip(orig,s)),0]
 return dict(sorted(out.items()))
def records():
 for name,p in SPEC['patterns'].items():
  for modes in itertools.product(MODES,repeat=len(p['rules'])):
   rows=[]
   for inp,goal in p['mappings'].items():
    orig=toks(inp,p['alphabet']);rs=[]
    for s in generate(p,orig):rs.append({'candidate':list(s),'surface':surface(s),'baseline':coeff(p,orig,s,modes),'subject':coeff(p,orig,s,modes,True)})
    rows.append({'input':inp,'target':goal,'rows':rs})
   yield {'pattern':name,'modes':list(modes),'records':rows}
def main():
 independent=list(records())
 coefficients_path=certificate.write('interaction_regions_coefficients.json',independent)
 from phonological_requirements import interaction_typology as native
 from phonological_requirements.core import read
 from phonological_requirements.evaluate import activation,coefficients,marked_subjects,subject_tuple
 from phonological_requirements.frag_seq import build,candidates,surface as native_surface
 comparisons=readchecks=changes=counts=0
 for rec in independent:
  p=SPEC['patterns'][rec['pattern']];np=native.PATTERNS[rec['pattern']];modes=rec['modes'];sg,D=native.build_pattern(np,modes)
  for inp in rec['records']:
   ref=build(toks(inp['input'],p['alphabet']));acts=activation(sg,ref,D);subjects=marked_subjects(sg,ref,D)
   cs=list(candidates(ref,np['options']));assert len(cs)==len(inp['rows'])
   for row,c in zip(inp['rows'],cs):
    assert native_surface(c)==row['surface'];counts+=1
    for variant in ['baseline','subject']:
     got={k:list(v) for k,v in coefficients(sg,ref,c,D,acts,subjects=subjects if variant=='subject' else None).items()}
     assert got==row[variant],(rec['pattern'],modes,inp['input'],row,got);comparisons+=len(got)
    changes+=row['baseline']!=row['subject']
    for rule,mode in zip(p['rules'],modes):
     for i,node in enumerate(c.nodes('seg')):
      expected,key=rule_read(p,row['candidate'],i,rule,mode)
      assert read(sg,ref,c,D[rule[0]],node).triple()==expected,(rec['pattern'],modes,inp['input'],row['candidate'],rule,i,expected,read(sg,ref,c,D[rule[0]],node).triple())
      assert tuple(None if x is None else x.index for x in subject_tuple(sg,ref,c,D[rule[0]],node))==key
      readchecks+=1
 out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'patterns':len(SPEC['patterns']),'assignments':len(independent),'candidate_rows':counts,'coefficient_pairs':comparisons,'current_reader_and_subject_key_checks':readchecks,'subject_changed_rows':changes,'independent_rows_sha256':hashlib.sha256(coefficients_path.read_bytes()).hexdigest()}
 certificate.write('interaction_regions.json',out);print(json.dumps(out))
if __name__=='__main__':main()
