"""Exact, reproducible subtree certificates for the full H43 partition sum.
Every emitted result is subsequently proved by the Lean kernel. Python values
are proof inputs only; no result of this program is treated as a theorem.
"""
from functools import lru_cache
from pathlib import Path
from collections import Counter
import ast,json,re,time,sys
from gen_certs import partitions,shape

ROOT=Path.cwd()
OUT=ROOT/'Paper20'/'Certs'/'HilbertParts'
OUT.mkdir(parents=True,exist_ok=True)
@lru_cache(None)
def count(n,cap):
    if n==0:return 1
    return sum(count(n-a,a) for a in range(min(n,cap),0,-1))

def node_name(pre):return 'j_'+'_'.join(map(str,pre)) if pre else 'j_root'
def value_name(pre):return 'v_'+'_'.join(map(str,pre)) if pre else 'v_root'
def proof_name(pre):return 'correct_'+'_'.join(map(str,pre)) if pre else 'correct_root'
def vec(v):
    if not any(v):return 'List.replicate 904 0'
    start=next(i for i,x in enumerate(v) if x)
    nums='['+', '.join(map(str,v[start:]))+']'
    return f'List.replicate {start} 0 ++ '+nums if start else nums

def leaf_value(pre,rem,cap):
    H=[0]*904
    for tail in partitions(rem,cap):
        p=pre+tail
        hooks,nu,c,f=shape(p)
        E=903+2*c+nu
        if E<0:raise AssertionError(('negative E',p,E))
        if E>903:continue
        t=[1]+[0]*(903-E)
        for a in hooks:
            for j in range(a,len(t)):t[j]+=t[j-a]
        for j,x in enumerate(t):H[E+j]+=f*x
    return H

stats=Counter()
branch_stats=[]
start_time=time.monotonic()

def emit_node(pre,cap,rem,fuel,lines):
    name=node_name(pre);vn=value_name(pre);pn=proof_name(pre)
    # Reuse the already kernel-checked benchmark rather than doing it twice.
    reused=pre==(7,7,7)
    nu_max=sum(i*a for i,a in enumerate(pre))+len(pre)*rem+rem*(rem-1)//2
    min_shift=903+2*sum(a*(a-1)//2 for a in pre)-nu_max
    leaf=rem==0 or fuel==0 or count(rem,cap)<=30 or min_shift>903 or reused
    kids=[]
    if leaf:
        H=leaf_value(pre,rem,cap) if fuel else [0]*904
        stats['leaves']+=1
        stats['leaf_partitions']+=count(rem,cap) if fuel else 0
    else:
        H=[0]*904
        for a in range(min(cap,rem),0,-1):
            ch=pre+(a,)
            cv=emit_node(ch,a,rem-a,fuel-1,lines)
            kids.append(ch)
            H=[x+y for x,y in zip(H,cv)]
        stats['internal_nodes']+=1
    stats['nodes']+=1
    lit='['+', '.join(map(str,pre))+']'
    lines.append(f'def {name} : Job := ⟨{lit}, {cap}, {rem}, {fuel}⟩\n')
    if reused:
        lines.append(f'def {vn} : List ℕ := Paper20.Cert.HilbertParts.h777\n')
        lines.append(f'theorem {pn} : value {name} = {vn} := by\n  change Paper20.HilbertChunks.prefixTotal [7,7,7] = Paper20.Cert.HilbertParts.h777\n  exact Paper20.Cert.HilbertParts.h777_correct\n')
    else:
        lines.append(f'def {vn} : List ℕ := {vec(H)}\n')
        if leaf:
            lines.append(f'theorem {pn} : value {name} = {vn} := by decide\n')
        else:
            knames=', '.join(node_name(ch) for ch in kids)
            proofs=', '.join(proof_name(ch) for ch in kids)
            lines.append(f'''theorem {pn} : value {name} = {vn} := by
  rw [value_children {name} (by decide) (by decide)]
  have hc : children {name} = [{knames}] := by decide
  rw [hc]
  simp only [List.map_cons, List.map_nil, {proofs}]
  all_goals decide
''')
    return H

rootH=[0]*904
for a in range(43,0,-1):
    lines=['import Paper20.HilbertJobsProof\n']
    if a==7:lines+=['import Paper20.Certs.HilbertParts.Test777\n']
    lines+=['set_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.HilbertParts.Tree\nopen Paper20.HilbertJobs\n']
    before=dict(stats)
    H=emit_node((a,),a,43-a,43,lines)
    rootH=[x+y for x,y in zip(rootH,H)]
    lines+=['end Paper20.Cert.HilbertParts.Tree\n']
    file=OUT/f'Branch{a:02}.lean'
    file.write_text('\n'.join(lines))
    branch_stats.append(dict(first_part=a,nodes=stats['nodes']-before.get('nodes',0),leaves=stats['leaves']-before.get('leaves',0),bytes=file.stat().st_size))
    print(branch_stats[-1],flush=True)
source=(ROOT/'Paper20'/'Certs'/'H43.lean').read_text()
m=re.search(r'def h43List[^:]*: List Nat := (\[.*?\])',source,re.S)
if not m:m=re.search(r'def h43List[^=]*:= (\[.*?\])',source,re.S)
expected=ast.literal_eval(m.group(1))
assert len(expected)==904 and rootH==expected
record=dict(stats=stats,branches=branch_stats,seconds=time.monotonic()-start_time,root_matches_preserved_H43=True)
(ROOT/'work'/'hilbert-tree-generation.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['stats'],record['seconds'],'root matches preserved H43',flush=True)
