#!/usr/bin/env python3
"""Export the actual exploratory chain/cochain as kernel-computable Lean data.

No theorem is justified by this exporter. CertificateChecks proves numerical
claims by Lean's kernel reduction on the exported definitions, then uses
linear-combination lemmas to interpret them in Cubical.RawChain.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT=Path.cwd()
p=argparse.ArgumentParser()
p.add_argument('--source',default='generation-inputs/certificate.json')
p.add_argument('--chunk-size',type=int,default=64)
a=p.parse_args()
source=ROOT/a.source
data=json.loads(source.read_text())
perms=data['permutations']
def cube_key(cell,pi):
    labelled=[0]*4
    for token,label in zip(cell,perms[pi]):labelled[label]=token
    key=0
    for token in labelled:key=71*key+token
    return key
z=[(cube_key(c,pi),v) for c,terms in data['cycle_z'] for pi,v in terms]
phi=sorted((cube_key(c,pi),v) for c,values in data['detecting_cocycle_phi'] for pi,v in enumerate(values) if v)
assert len({k for k,v in phi})==len(phi)
assert len({k for k,v in z})==len(z)
sha=hashlib.sha256(source.read_bytes()).hexdigest()
header=f'''import Mathlib.Data.Int.Basic

/-! Explicit labelled chain and cochain data for Paper 23.
Exported from `{a.source}`, SHA-256 `{sha}`.
The input JSON is not a proof. Only kernel-checked theorems in
`CertificateChecks.lean` establish the identities stated there.
A permutation p assigns canonical coordinate i to particle label p[i].
Four cell tokens (vertices 0..31; edges 32..70) are packed in base 71.
-/
namespace Paper23.CertificateData

inductive LookupTree where
  | empty
  | node (key : ℕ) (value : ℤ) (left right : LookupTree)

noncomputable def lookup (t : LookupTree) (n : ℕ) : ℤ :=
  LookupTree.rec (motive := fun _ => ℕ → ℤ) (fun _ => 0)
    (fun key value _ _ left right k =>
      if k < key then left k else if k = key then value else right k) t n

'''
# Use named subtrees to keep each elaborated declaration bounded.
nodes=[]
def tree_expr(entries,depth=0):
    if not entries:return '.empty'
    mid=len(entries)//2
    key,value=entries[mid]
    left=tree_expr(entries[:mid],depth+1)
    right=tree_expr(entries[mid+1:],depth+1)
    expr=f'(.node {key} {value} {left} {right})'
    if depth in (0, 8):
        name=f'phiTree{len(nodes)}'
        nodes.append(f'noncomputable def {name} : LookupTree := {expr}\n')
        return name
    return expr
root=tree_expr(phi)
chunks=[z[i:i+a.chunk_size] for i in range(0,len(z),a.chunk_size)]
lines=[header,*nodes,f'\nnoncomputable def phiTable : LookupTree := {root}\n']
for i,chunk in enumerate(chunks):
    entries=', '.join(f'({k}, {v if v>=0 else f"({v})"})' for k,v in chunk)
    lines.append(f'noncomputable def zEntries{i} : List (ℕ × ℤ) := [{entries}]\n')
lines.append('noncomputable def zChunks : List (List (ℕ × ℤ)) := [\n  '+',\n  '.join(f'zEntries{i}' for i in range(len(chunks)))+'\n]\n')
lines.append(f'def sourceSHA256 : String := "{sha}"\n')
lines.append(f'def zLabelledTermCount : ℕ := {len(z)}\n')
lines.append(f'def phiLabelledSupportCount : ℕ := {len(phi)}\n')
lines.append('\nend Paper23.CertificateData\n')
(ROOT/'Paper23/CertificateData.lean').write_text(''.join(lines))
phi_dict=dict(phi)
meta={'source_sha256':sha,'z_terms':len(z),'phi_terms':len(phi),'chunks':len(chunks),'chunk_size':a.chunk_size,'integer_evaluation':sum(v*phi_dict.get(k,0) for k,v in z)}
(ROOT/'work/lean-certificate-export.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
checks_dir=ROOT/'Paper23/CertificateChecks'
checks_dir.mkdir(exist_ok=True)
part_size=32
part_count=(len(chunks)+part_size-1)//part_size
for part in range(part_count):
    lines=["import Paper23.CertificateEncoding\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Paper23.CertificateChecks\nopen Cubical CertificateData\n\n"]
    for i in range(part*part_size,min((part+1)*part_size,len(chunks))):
        value=sum(v*phi_dict.get(k,0) for k,v in chunks[i])
        lines.append(f'theorem evaluationChunk{i} : codeEvaluation zEntries{i} = ({value} : ℤ) := by decide +kernel\n')
        lines.append(f'theorem validChunk{i} : ∀ p ∈ zEntries{i}, validDegreeTwo p.1 := by decide +kernel\n')
    lines.append('\nend Paper23.CertificateChecks\n')
    (checks_dir/f'Part{part:02}.lean').write_text(''.join(lines))
checks=[*(f'import Paper23.CertificateChecks.Part{part:02}\n' for part in range(part_count)),"""
/-! Kernel-checked evaluation and validity of the explicit original-coordinate
chain. The proofs use `decide`, not native_decide. The list-to-Finsupp bridge
makes the conclusions statements about the original cubical chains.
The cycle, bounding and universal cocycle identities are not asserted here.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Paper23.CertificateChecks
open Cubical CertificateData

"""]
checks.append('theorem zEvaluation_eq_one : zEvaluation = 1 := by\n  simp only [zEvaluation, zChunks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,\n    '+',\n    '.join(f'evaluationChunk{i}' for i in range(len(chunks)))+']\n  decide\n')
checks.append("""
/-- The actual Finsupp chain is detected with value one modulo six. -/
theorem evaluation : phi z = 1 := by
  rw [phi_z_eq_evaluation, zEvaluation_eq_one]
  rfl

""")
proof=f"validChunk{len(chunks)-1}"
for i in range(len(chunks)-2,-1,-1):
    proof=f"(And.intro validChunk{i} {proof})"
checks.append("theorem zChunks_valid : zChunks.Forall (fun xs => ∀ p ∈ xs, validDegreeTwo p.1) := by\n  unfold zChunks\n  exact "+proof+"\n\n")
checks.append("""theorem z_mem_chains : z ∈ Chains 2 := by
  change (zChunks.map codeChain).sum ∈ Chains 2
  apply list_sum_mem
  intro c hc
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hc
  exact codeChain_mem xs ((List.forall_iff_forall_mem.mp zChunks_valid) xs hxs)
""")
checks.append("""
/-- The explicit chain in the actual ordered cubical degree-two group. -/
noncomputable def zChain : Chains 2 := ⟨z, z_mem_chains⟩

/-- The explicit detector restricted to that degree-two group. -/
noncomputable def phiChain : Chains 2 →ₗ[ℤ] ZMod 6 :=
  phi.comp (Chains 2).subtype

theorem ordered_evaluation : phiChain zChain = 1 := evaluation

theorem zChain_ne_zero : zChain ≠ 0 := by
  intro h
  have hh := ordered_evaluation
  rw [h, map_zero] at hh
  exact (by decide : (0 : ZMod 6) ≠ 1) hh
""")
checks.append('\nend Paper23.CertificateChecks\n')
(ROOT/'Paper23/CertificateChecks.lean').write_text(''.join(checks))
