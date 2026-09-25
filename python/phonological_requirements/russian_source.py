from pathlib import Path
from collections import Counter,defaultdict
import datetime,hashlib,json,sys
from .certificate import write
import numpy as np

W=Path(sys.argv[1]).resolve()
rows=json.loads((W/"response_rows.json").read_text())
for r in rows:
    r["f"]=int(r["accept.faithful"]);r["d"]=int(r["accept.deletion"]);r["rating"]=int(r["nom.rating"])
    r["shape"]="CVC" if r["C"]=="2" else ("CVCC" if r["position"]=="1" else "CCVC")
    r["mono"]=r["prefix"]==""
    r["tr"]=r["type"] in ["TR","RTR","TTR"]
    r["rr"]=r["type"] in ["RR","TRR"]
    base=r["model_base"].split()
    v=max(i for i,x in enumerate(base) if x in ["e","o"])
    r["lateral"]=base[v-1] in ["l","lj"]

def summary(rr):
    return {"n":len(rr),"rating_mean":float(np.mean([r["rating"] for r in rr])),
            "faithful_acceptance":float(np.mean([r["f"] for r in rr])),
            "deletion_acceptance":float(np.mean([r["d"] for r in rr])),
            "joint_counts":dict(Counter(str(r["f"])+str(r["d"]) for r in rr))}
out={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
     "all":summary(rows),"participants":len({r["userCode"] for r in rows}),
     "clusters":len({r["cluster"] for r in rows}),
     "types":len({(r["shape"],r["type"],r["mono"],r["vowel"]) for r in rows}),
     "by_shape":{s:summary([r for r in rows if r["shape"]==s]) for s in ["CVC","CCVC","CVCC"]},
     "by_TR":{str(v):summary([r for r in rows if r["tr"]==v]) for v in [False,True]},
     "by_RR":{str(v):summary([r for r in rows if r["rr"]==v]) for v in [False,True]},
     "by_monoyllabicity":{str(v):summary([r for r in rows if r["mono"]==v]) for v in [False,True]},
     "by_vowel":{v:summary([r for r in rows if r["vowel"]==v]) for v in ["е","о"]},
     "lateral_vowel":{str(l)+v:summary([r for r in rows if r["lateral"]==l and r["vowel"]==v])
                      for l in [False,True] for v in ["е","о"]},
     "monosyllablic_column_disagrees_with_actual":sum((r["monosyllablic"]=="TRUE")!=r["mono"] for r in rows)}
checks=[]
def check(name,actual,published,digits):
    ok=round(actual,digits)==published
    checks.append({"name":name,"computed":actual,"printed":published,"digits":digits,"matches":ok})
for s,val in [("CVC",4.16),("CCVC",3.01),("CVCC",2.48)]:check(s+" rating",out["by_shape"][s]["rating_mean"],val,2)
for s,val in [("CVC",40),("CCVC",21),("CVCC",15)]:check(s+" deletion %",100*out["by_shape"][s]["deletion_acceptance"],val,0)
for s,val in [("CVC",91),("CCVC",90),("CVCC",88)]:check(s+" faithful %",100*out["by_shape"][s]["faithful_acceptance"],val,0)
check("overall deletion %",100*out["all"]["deletion_acceptance"],25,0)
check("overall faithful %",100*out["all"]["faithful_acceptance"],90,0)
for mono,val in [(True,22),(False,28)]:check("mono "+str(mono)+" deletion %",100*out["by_monoyllabicity"][str(mono)]["deletion_acceptance"],val,0)
for vowel,val in [("е",24),("о",27)]:check(vowel+" deletion %",100*out["by_vowel"][vowel]["deletion_acceptance"],val,0)
for tr,val in [(False,24),(True,27)]:check("TR "+str(tr)+" deletion %",100*out["by_TR"][str(tr)]["deletion_acceptance"],val,0)
for key,val in [("Trueе",14),("Trueо",25),("Falseе",24),("Falseо",28)]:
    check("lateral "+key+" deletion %",100*out["lateral_vowel"][key]["deletion_acceptance"],val,0)
out["published_rounding_checks"]=checks
out["scope"]="Raw descriptive reproduction only; no claim to reproduce the source's fitted mixed-effects Table 6."
write("russian_source.json",out,W)
print(json.dumps(out,ensure_ascii=False,indent=2))
