from pathlib import Path
from functools import lru_cache
from collections import Counter
from math import gcd,factorial
from fractions import Fraction as F
import json,time,sys
from native_q36 import aggregate,combine,partitions,L,scaled_r
ROOT=Path.cwd();OUT=ROOT/'Paper20'/'Certs'/'RContent36';OUT.mkdir(exist_ok=True)
CHUNK=650000
stats=Counter();records=[];started=time.monotonic()
@lru_cache(None)
def count(n,cap):return 1 if n==0 else sum(count(n-a,a) for a in range(min(n,cap),0,-1))
def nm(p):return '_'.join(map(str,p))
def jn(p):return 'j_'+nm(p)
def vn(p):return 'v_'+nm(p)
def pn(p):return 'correct_'+nm(p)
def state_literal(s):
 rows=[]
 for c,v in s:
  g=0
  for x in v:g=gcd(g,abs(x))
  if g>1:
   values='['+', '.join(map(str,(x//g for x in v)))+']'
   values=f'({values}).map (fun z : ℤ => {g}*z)'
  else:values='['+', '.join(map(str,v))+']'
  rows.append(f'({c}, {values})')
 return '['+',\n'.join(rows)+']'
def forall2(proofs):
 out='List.Forall₂.nil'
 for p in reversed(proofs):out=f'(List.Forall₂.cons {p} {out})'
 return out

def emit(pre,cap,rem,fuel,blocks):
 reused=pre==(36,)
 leaf=reused or rem==0 or fuel==0 or count(rem,cap)<=8
 kids=[]
 if leaf:
  s=aggregate([pre+t for t in partitions(rem,cap)]) if fuel else []
  stats['leaves']+=1;stats['partitions']+=count(rem,cap) if fuel else 0
 else:
  states=[]
  for a in range(min(cap,rem),0,-1):
   child=pre+(a,);states.append(emit(child,a,rem-a,fuel-1,blocks));kids.append(child)
  s=combine(states);stats['internal']+=1
 stats['nodes']+=1
 j,v,p=jn(pre),vn(pre),pn(pre)
 block=f'def {j} : Job := ⟨['+', '.join(map(str,pre))+f'], {cap}, {rem}, {fuel}⟩\n\n'
 if reused:
  block+=f'def {v} : State := Paper20.Cert.RContent36.v36\n\ntheorem {p} : Correct {j} {v} := Paper20.Cert.RContent36.v36_correct\n'
 else:
  block+=f'def {v} : State := '+state_literal(s)+'\n\n'
  if leaf:
   block+=f'theorem {p} : Correct {j} {v} := correct_leaf {j} {v} (by decide +kernel)\n'
  else:
   jobs=', '.join(jn(ch) for ch in kids);vals=', '.join(vn(ch) for ch in kids)
   block+=f'''theorem {p} : Correct {j} {v} := by
  have hc : children {j} = [{jobs}] := by decide +kernel
  have hv : List.Forall₂ Correct (children {j}) [{vals}] := by
    rw [hc]
    exact {forall2([pn(ch) for ch in kids])}
  have hp := correct_children {j} (by decide) (by decide) [{vals}] hv
  have he : combine [{vals}] = {v} := by decide +kernel
  rwa [he] at hp
'''
 blocks.append(block)
 return s

root_states=[]
for a in range(36,0,-1):
 before=dict(stats);blocks=[];s=emit((a,),a,36-a,36,blocks);root_states.append(s)
 chunks=[];buf=[];size=0
 for block in blocks:
  if buf and size+len(block)>CHUNK:chunks.append('\n'.join(buf));buf=[];size=0
  buf.append(block);size+=len(block)
 if buf:chunks.append('\n'.join(buf))
 modules=[]
 for idx,body in enumerate(chunks):
  name=f'B{a:02}C{idx:02}';module=f'Paper20.Certs.RContent36.{name}'
  imports=('import '+modules[-1]+'\n') if modules else 'import Paper20.RContent36\n'
  if a==36 and not modules:imports+='import Paper20.Certs.RContent36.Test36\n'
  text=imports+'''set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.RContent36.Tree
open Paper20.RContent36
open Paper20.HilbertJobs (Job parts children)

'''+body+'\nend Paper20.Cert.RContent36.Tree\n'
  (OUT/f'{name}.lean').write_text(text);modules.append(module)
 (OUT/f'Branch{a:02}.lean').write_text('import '+modules[-1]+'\n')
 rec=dict(first_part=a,nodes=stats['nodes']-before.get('nodes',0),leaves=stats['leaves']-before.get('leaves',0),chunks=len(chunks),bytes=sum(len(x) for x in chunks),rows=len(s))
 records.append(rec);print(rec,flush=True)
root=combine(root_states)
assert sum(v[0] for c,v in root)==factorial(36)
cert=json.loads((ROOT/'certs'/'q36.json').read_text());numerators={}
for h in (20,21,22):
 den=4**h*factorial(2*h)*L**h*factorial(h)
 out=[0]*23
 for c,rs in root:
  A=[1]
  for j in range(h+1):
   if j:
    t=2*j-1 if c%2 else 2*(j-1)
    nxt=[0]*(len(A)+1)
    for i,x in enumerate(A):nxt[i]+=x*(c*c-t*t);nxt[i+1]+=x*4*c*c
    A=nxt
   dj=4**j*factorial(2*j)*L**(h-j)*factorial(h-j)
   assert den%dj==0
   fac=(den//dj)*rs[h-j]
   for i,x in enumerate(A):out[i]+=x*fac
 expected=[F(a,b) for a,b in cert[f'Q{h}']]+[F(0)]*(23-(h+1))
 assert [F(x,den*factorial(36)) for x in out]==expected
 numerators[str(h)]=out
print('native complete grouped R, dimension sum and Q20/Q21/Q22 comparisons PASS',flush=True)
imports='\n'.join(f'import Paper20.Certs.RContent36.Branch{a:02}' for a in range(1,37))
vals=', '.join(vn((a,)) for a in range(36,0,-1));jobs=', '.join(jn((a,)) for a in range(36,0,-1))
alltext=imports+'''
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.RContent36.Tree
open Paper20.RContent36
open Paper20.HilbertJobs (Job parts children)

def rootState : State := '''+state_literal(root)+f'''

theorem root_correct : Correct Paper20.RContent36.root rootState := by
  have hc : children Paper20.RContent36.root = [{jobs}] := by decide +kernel
  have hv : List.Forall₂ Correct (children Paper20.RContent36.root) [{vals}] := by
    rw [hc]
    exact {forall2([pn((a,)) for a in range(36,0,-1)])}
  have hp := correct_children Paper20.RContent36.root (by decide) (by decide) [{vals}] hv
  have he : combine [{vals}] = rootState := by decide +kernel
  rwa [he] at hp

theorem root_keys_checked : rootState.all (fun p => p.1 ≤ 630) = true := by decide +kernel

theorem root_keys_bound : ∀ p ∈ rootState, p.1 ≤ 630 := by
  intro p hp
  have hc := List.all_eq_true.mp root_keys_checked p hp
  exact of_decide_eq_true hc

end Paper20.Cert.RContent36.Tree
'''
a=alltext.index('def rootState : State := ');b=alltext.index('\ntheorem root_correct',a)
c=alltext.index('\ntheorem root_keys_checked',b);d=alltext.index('\nend Paper20.Cert.RContent36.Tree',c)
rootdecl='\n'.join(f'def rootRow{i:03} : ℕ × List ℤ := ({k}, '+str(v)+')' for i,(k,v) in enumerate(root))+'\n\ndef rootState : State := ['+', '.join(f'rootRow{i:03}' for i in range(len(root)))+']\n';keydecl=alltext[c:d]
(OUT/'RootData.lean').write_text('import Paper20.RContent36\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.RContent36.Tree\nopen Paper20.RContent36\n\n'+rootdecl+keydecl+'\nend Paper20.Cert.RContent36.Tree\n')
alltext='import Paper20.Certs.RContent36.RootData\n'+alltext[:a]+alltext[b:c]+alltext[d:]
(OUT/'All.lean').write_text(alltext)
(ROOT/'work'/'r-content36-root.json').write_text(json.dumps(dict(scale=L,state=root,numerators=numerators))+'\n')
(ROOT/'work'/'r-content36-generation.json').write_text(json.dumps(dict(stats=dict(stats),branches=records,root_rows=len(root),seconds=time.monotonic()-started),indent=2)+'\n')
print(dict(stats=dict(stats),root_rows=len(root),seconds=time.monotonic()-started),flush=True)
