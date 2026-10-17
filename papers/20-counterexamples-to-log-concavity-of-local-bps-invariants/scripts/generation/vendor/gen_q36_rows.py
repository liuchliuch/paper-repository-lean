from pathlib import Path
import json
exec(Path('scripts/generation/vendor/test_q36_rows.py').read_text().split("p=Path('Paper20/Certs/ContentQ36Rows')")[0])
OUT=Path('Paper20/Certs/ContentQ36Rows')
chunks=[]
for start in range(0,len(state),20):
 idx=start//20;name=f'C{idx:02}';previous='Paper20.Certs.ContentQ36Rows.Test' if idx==0 else f'Paper20.Certs.ContentQ36Rows.C{idx-1:02}'
 s=f'import {previous}\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.ContentQ36Rows\nopen Paper20.RContent36 Paper20.Cert.RContent36.Tree\n'
 for i in range(start,min(start+20,len(state))):
  c,rs=state[i]
  for h in [20,21,22]:
   v=row(c,rs,h);alias=h==22 and i in [0,1,2,392]
   literal=f'Test.vector{i:03}' if alias else str(v)
   s+=f'def vector{h}_{i:03} : List ℤ := {literal}\n'
   proof=f'Test.checked{i:03}' if alias else 'by decide +kernel'
   s+=f'theorem checked{h}_{i:03} : fastRowVector rootRow{i:03} {h}=vector{h}_{i:03} := {proof}\n'
 s+='end Paper20.Cert.ContentQ36Rows\n';(OUT/f'{name}.lean').write_text(s);chunks.append(name)
def forall2(names):
 out='List.Forall₂.nil'
 for name in reversed(names):out=f'(List.Forall₂.cons {name} {out})'
 return out
s=f'import Paper20.Certs.ContentQ36Rows.{chunks[-1]}\nimport Paper20.RContentRowEvaluation\nimport Paper20.Uniform36\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.ContentQ36Rows\nopen Paper20.RContent36 Paper20.Cert.RContent36.Tree\n'
for h,legacy in [(20,'AList'),(21,'BList'),(22,'CList')]:
 vals=', '.join(f'vector{h}_{i:03}' for i in range(len(state)));num=root['numerators'][str(h)]
 assert [sum(row(c,rs,h)[j] for c,rs in state) if j<=h else 0 for j in range(23)]==num
 s+=f'def vectors{h} : List (List ℤ) := [{vals}]\n'
 s+=f'theorem rows{h} : List.Forall₂ (fun p v => fastRowVector p {h}=v) rootState vectors{h} :=\n  '+forall2([f'checked{h}_{i:03}' for i in range(len(state))])+'\n'
 s+=f'def numerator{h} : List ℤ := '+str(num)+'\n'
 s+=f'theorem sum{h} : sumVectors vectors{h} id=numerator{h}.take ({h}+1) := by decide +kernel\n'
 s+=f'theorem evaluated{h} : evaluateFastVector rootState {h}=numerator{h}.take ({h}+1) := by\n  rw [evaluateFastVector_of_rows rootState {h} vectors{h} rows{h},sum{h}]\n'
 s+=f'''theorem truncated{h} : (List.range 23).all (fun i => decide
    ((numerator{h}.take ({h}+1)).getD i 0=numerator{h}.getD i 0)) = true := by decide +kernel

theorem scaled{h} : (List.range 23).all (fun i => decide
    ((numerator{h}.getD i 0 : ℚ) =
      (FastQ36.denominator {h}:ℚ)*((36:ℕ).factorial:ℚ)*
        ((1:ℚ)/Uniform36.Dqval)*(Uniform36.{legacy}.getD i 0:ℚ))) = true := by decide +kernel

theorem evaluated{h}_getD (i : ℕ) (hi : i < 23) :
    (evaluateFastVector rootState {h}).getD i 0 = numerator{h}.getD i 0 := by
  rw [evaluated{h}]
  exact of_decide_eq_true (List.all_eq_true.mp truncated{h} i (List.mem_range.mpr hi))

theorem scaled{h}_getD (i : ℕ) (hi : i < 23) :
    (numerator{h}.getD i 0 : ℚ) =
      (FastQ36.denominator {h}:ℚ)*((36:ℕ).factorial:ℚ)*
        ((1:ℚ)/Uniform36.Dqval)*(Uniform36.{legacy}.getD i 0:ℚ) :=
  of_decide_eq_true (List.all_eq_true.mp scaled{h} i (List.mem_range.mpr hi))
'''
s+='end Paper20.Cert.ContentQ36Rows\n';(OUT/'All.lean').write_text(s)
print('Generated',len(state),'rows x 3 orders in',len(chunks),'sequential chunks; native sums exactly match preserved numerators.')
