from pathlib import Path
import json,math
root=json.loads(Path('work/r-content36-root.json').read_text());L=root['scale'];state=root['state']
def row(c,rs,h):
 den=4**h*math.factorial(2*h)*L**h*math.factorial(h)
 out=[0]*(h+1);A=[1]
 for j in range(h+1):
  if j:
   t=2*j-1 if c%2 else 2*(j-1)
   nxt=[0]*(len(A)+1)
   for i,x in enumerate(A):nxt[i]+=x*(c*c-t*t);nxt[i+1]+=x*4*c*c
   A=nxt
  dj=4**j*math.factorial(2*j)*L**(h-j)*math.factorial(h-j)
  fac=den//dj*rs[h-j]
  for i,x in enumerate(A):out[i]+=x*fac
 return out
p=Path('Paper20/Certs/ContentQ36Rows');p.mkdir(exist_ok=True)
s='''import Paper20.RContentFastVector
import Paper20.Certs.RContent36.RootData
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.ContentQ36Rows.Test
open Paper20.RContent36 Paper20.Cert.RContent36.Tree
'''
for i in [0,1,2,392]:
 c,rs=state[i];v=row(c,rs,22)
 s+=f'def vector{i:03} : List ℤ := '+str(v)+'\n'
 s+=f'theorem checked{i:03} : fastRowVector rootRow{i:03} 22=vector{i:03} := by decide +kernel\n'
s+='end Paper20.Cert.ContentQ36Rows.Test\n';(p/'Test.lean').write_text(s)
