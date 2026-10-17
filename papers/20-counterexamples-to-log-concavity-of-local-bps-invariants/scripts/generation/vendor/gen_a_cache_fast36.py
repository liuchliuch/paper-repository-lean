from pathlib import Path
ROOT=Path.cwd();OUT=ROOT/'Paper20/Certs/ACacheFast36';OUT.mkdir(exist_ok=True)
(OUT/'Basic.lean').write_text('''import Paper20.IntegerPolynomial
namespace Paper20.Cert.ACacheFast36
open Paper20.IntegerPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def rowCheck (c : ℕ) (row : Array (List ℤ)) : Bool := decide (row.getD 0 []=[1]) &&
  (List.range 22).all (fun j => decide (row.getD (j+1) [] =
    mul (row.getD j []) (numeratorFactor ((c:ℤ)^2) (decide (c%2=0)) (j+1))))
end Paper20.Cert.ACacheFast36
''')
rows=[]
for c in range(631):
 arr=[[1]];a=[1]
 for j in range(1,23):
  t=2*j-1 if c%2 else 2*(j-1);b=[0]*(len(a)+1)
  for i,x in enumerate(a):b[i]+=x*(c*c-t*t);b[i+1]+=x*4*c*c
  a=b;arr.append(a)
 rows.append(arr)
chunks=[]
for lo in range(0,631,20):
 idx=len(chunks);name=f'C{idx:02}'
 dep='Paper20.Certs.ACacheFast36.Basic' if idx==0 else 'Paper20.Certs.ACacheFast36.'+chunks[-1]
 s=f'import {dep}\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.ACacheFast36\n'
 for c in range(lo,min(lo+20,631)):
  s+=f'\ndef row{c:03} : Array (List ℤ) := #['+', '.join('['+', '.join(map(str,v))+']' for v in rows[c])+']\n'
  s+=f'theorem checked{c:03} : rowCheck {c} row{c:03}=true := by decide +kernel\n'
 s+='\nend Paper20.Cert.ACacheFast36\n';(OUT/f'{name}.lean').write_text(s);chunks.append(name)
s=f'import Paper20.Certs.ACacheFast36.{chunks[-1]}\nset_option maxHeartbeats 0\nset_option maxRecDepth 200000\nnamespace Paper20.Cert.ACacheFast36\nopen Paper20.IntegerPolynomial\n'
s+='\ndef aData : Array (Array (List ℤ)) := #['+', '.join(f'row{c:03}' for c in range(631))+']\n'
s+='\ndef aCached (c j : ℕ) : List ℤ := (aData.getD c #[]).getD j []\n'
s+='\ntheorem row_checked (c : ℕ) (hc : c ≤ 630) : rowCheck c (aData.getD c #[])=true := by\n  interval_cases c\n'
for c in range(631):s+=f'  · exact checked{c:03}\n'
s+='''
theorem aCached_zero (c : ℕ) (hc : c ≤ 630) : aCached c 0=[1] := by
  exact of_decide_eq_true ((Bool.and_eq_true_iff.mp (row_checked c hc)).1)

theorem aCached_rec (c j : ℕ) (hc : c ≤ 630) (hj : j < 22) :
    aCached c (j+1) = mul (aCached c j)
      (numeratorFactor ((c:ℤ)^2) (decide (c%2=0)) (j+1)) := by
  have h := (Bool.and_eq_true_iff.mp (row_checked c hc)).2
  exact of_decide_eq_true (List.all_eq_true.mp h j (List.mem_range.mpr hj))

theorem aCached_correct (c j : ℕ) (hc : c ≤ 630) (hj : j ≤ 22) :
    numeratorA ((c:ℤ)^2) (decide (c%2=0)) j=aCached c j := by
  induction j with
  | zero => exact (aCached_zero c hc).symm
  | succ j ih => rw [numeratorA,ih (by omega),← aCached_rec c j hc (by omega)]

end Paper20.Cert.ACacheFast36
'''
(OUT/'All.lean').write_text(s)
print(dict(chunks=len(chunks),rows=len(rows),bytes=sum(p.stat().st_size for p in OUT.glob('*.lean'))))
