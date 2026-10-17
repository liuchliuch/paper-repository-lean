from fractions import Fraction as F
from functools import lru_cache
from math import lcm,factorial
from collections import Counter
from gen_certs import partitions,shape
L=4*lcm(*range(1,37))
def add(a,b):return [x+y for x,y in zip(a+[0]*len(b),b+[0]*len(a))][:max(len(a),len(b))]
def mul(a,b):return [sum(a[i]*b[k-i] for i in range(len(a)) if 0<=k-i<len(b)) for k in range(len(a)+len(b))]
D=[[1],[1],[1],[3,1],[2,1]]
for a in range(5,37):D.append(add(mul([2,1],D[a-2]),[-x for x in D[a-4]]))
G=[[]]
for a in range(1,37):
 g=[]
 for j in range(22):
  x=-(j+1)*F(D[a][j+1] if j+1<len(D[a]) else 0)
  x-=sum(F(D[a][t] if t<len(D[a]) else 0)*g[j-t] for t in range(1,j+1))
  g.append(x/D[a][0])
 vals=[v*L**(j+1) for j,v in enumerate(g)]
 assert all(v.denominator==1 for v in vals)
 G.append([v.numerator for v in vals])
@lru_cache(None)
def scaled_r(hooks):
 counts=Counter(hooks);even=sum(m for a,m in counts.items() if a%2==0)
 gamma=[0]+[sum(m*G[a][i-1] for a,m in counts.items())+(even//2)*(-1)**i*(L//4)**i for i in range(1,23)]
 out=[1]
 for m in range(1,23):
  out.append(sum(gamma[i]*out[m-i]*(factorial(m-1)//factorial(m-i)) for i in range(1,m+1)))
 return tuple(out)
def weighted(p):
 hooks,nu,c,f=shape(p)
 return abs(c),[f*f*x for x in scaled_r(tuple(hooks))]
def update(state,c,vec):
 for entry in state:
  if entry[0]==c:
   entry[1]=[x+y for x,y in zip(entry[1],vec)];return state
 state.append([c,list(vec)]);return state
def aggregate(pss):
 s=[]
 for p in pss:
  c,v=weighted(p);update(s,c,v)
 return s
def combine(states):
 out=[]
 for s in reversed(states):
  for c,v in s:update(out,c,v)
 return out
def lean_state(s):
 return '['+',\n'.join('('+str(c)+', ['+', '.join(map(str,v))+'])' for c,v in s)+']'
