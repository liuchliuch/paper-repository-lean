#!/usr/bin/env python3
"""Generate a staged Lean sparse-reflection proof of d z = 0.

Generated equalities are checked by `decide +kernel`; Python does not supply
proofs. This script writes under work/ by default, so an unfinished large
numerical proof is not silently included in the production library.
"""
from pathlib import Path
from collections import defaultdict
import argparse, json
root=Path.cwd()
p=argparse.ArgumentParser()
p.add_argument('--source',default='generation-inputs/certificate.json')
p.add_argument('--output-dir',default='work/lean-cycle-staging')
p.add_argument('--chunk-size',type=int,default=64)
a=p.parse_args()
data=json.loads((root/a.source).read_text())
out=root/a.output_dir;out.mkdir(parents=True,exist_ok=True)
perms=data['permutations']; edges=data['subdivided_graph']['oriented_edges']
def key(c):
    n=0
    for x in c:n=71*n+x
    return n
z=[]
for c,terms in data['cycle_z']:
    for pi,v in terms:
        raw=[0]*4
        for token,label in zip(c,perms[pi]):raw[label]=token
        z.append((raw,v))
def boundary(chunk):
    result=defaultdict(int)
    for c,a in chunk:
        for coordinate,token in enumerate(c):
            if token<32:continue
            sign=(-1)**sum(t>=32 and t<token for t in c)
            for endpoint,factor in zip(edges[token-32],[-1,1]):
                f=c.copy();f[coordinate]=endpoint
                result[key(f)]+=a*sign*factor
    return sorted((k,v) for k,v in result.items() if v)
def merge(x,y):
    d=defaultdict(int,x)
    for k,v in y:d[k]+=v
    return sorted((k,v) for k,v in d.items() if v)
def literal(xs):
    return '['+', '.join(f'({k}, {v if v>=0 else f"(Int.negSucc {-v-1})"})' for k,v in xs)+']'
def declare_list(name,xs):
    if len(xs)<=256:
        return f'noncomputable def {name} : List (ℕ × ℤ) := {literal(xs)}\n'
    pieces=[xs[i:i+256] for i in range(0,len(xs),256)]
    text=''.join(f'noncomputable def {name}Part{i} : List (ℕ × ℤ) := {literal(piece)}\n' for i,piece in enumerate(pieces))
    return text+f'noncomputable def {name} : List (ℕ × ℤ) := '+' ++ '.join(f'{name}Part{i}' for i in range(len(pieces)))+'\n'
chunks=[z[i:i+a.chunk_size] for i in range(0,len(z),a.chunk_size)]
leaves=[boundary(c) for c in chunks]
# Each module has bounded declarations and depends on the proven generic
# normalizer and on the actual source-validity theorems.
header='''import Paper23.CertificateSparse
import Paper23.CertificateChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Paper23.CertificateChecks
open Cubical CertificateData
attribute [local irreducible] codeChain
'''
node_sources=[]
for block in range((len(leaves)+15)//16):
    lines=[header]
    for i in range(block*16,min((block+1)*16,len(leaves))):
        name=f'cycleLeaf{i}'
        lines.append(declare_list(name,leaves[i]))
        lines.append(f'''theorem {name}_check :
    collapse 10 ((codeDifferential zEntries{i}).map (fun p => [p])) = [{name}] := by
  exact eq_of_beq (by decide +kernel)
 theorem {name}_chain : codeChain {name} = boundary (codeChain zEntries{i}) := by
  exact (normalization_sound 10 (codeDifferential zEntries{i}) {name} {name}_check).trans
    (codeChain_codeDifferential zEntries{i} (fun p hp => (validChunk{i} p hp).1.2))
''')
    lines.append('end Paper23.CertificateChecks\n')
    (out/f'Leaves{block:02}.lean').write_text(''.join(lines))
level=[(f'cycleLeaf{i}',xs,f'codeChain zEntries{i}') for i,xs in enumerate(leaves)]
level_index=0
while len(level)>1:
    level_index+=1
    dependencies = (''.join(f'import Paper23.CertificateCycle.Leaves{b:02}\n' for b in range((len(leaves)+15)//16)) if level_index == 1 else f'import Paper23.CertificateCycle.Level{level_index-1}\n')
    blocks=[]
    lines=[dependencies, header]
    nextlevel=[]
    for i in range(0,len(level),2):
        if i+1==len(level):nextlevel.append(level[i]);continue
        (ln,lx,ls),(rn,rx,rs)=level[i:i+2]
        name=f'cycleNode{level_index}_{i//2}'
        source=f'cycleSource{level_index}_{i//2}'
        result=merge(lx,rx)
        lines.append(declare_list(name,result))
        lines.append(f'noncomputable def {source} : RawChain := {ls} + {rs}\n')
        lines.append(f'''theorem {name}_check : merge {ln} {rn} = {name} := by
  exact eq_of_beq (by decide +kernel)
 theorem {name}_chain : codeChain {name} = boundary {source} := by
  rw [← {name}_check, codeChain_merge, {ln}_chain, {rn}_chain]
  exact (map_add boundary _ _).symm
''')
        nextlevel.append((name,result,source));node_sources.append(source)
        if len(blocks)==0 or len(blocks[-1])==16:
            blocks.append([])
        blocks[-1].append(''.join(lines[2:]));lines=[dependencies,header]
    for block,contents in enumerate(blocks):
        (out/f'Nodes{level_index}_{block:02}.lean').write_text(dependencies+header+''.join(contents)+'end Paper23.CertificateChecks\n')
    (out/f'Level{level_index}.lean').write_text(''.join(f'import Paper23.CertificateCycle.Nodes{level_index}_{b:02}\n' for b in range(len(blocks))))
    level=nextlevel
assert level[0][1]==[], 'Actual boundary was not zero'
name,_,source=level[0]
main=[f'import Paper23.CertificateCycle.Level{level_index}\n', header]
main.append(f'theorem cycleSource_eq_z : {source} = z := by\n  simp only [\n    '+',\n    '.join(node_sources)+',\n    z, zChunks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc, add_zero]\n')
main.append(f'theorem cycle : boundary z = 0 := by\n  rw [← cycleSource_eq_z, ← {name}_chain]\n  change codeChain [] = 0\n  exact codeChain_nil\n')
main.append('end Paper23.CertificateChecks\n')
(out/'CertificateCycle.lean').write_text(''.join(main))
summary={'leaves':len(leaves),'leaf_nonzero_terms':sum(map(len,leaves)),'merge_levels':level_index,'root':name,'root_source':source,'note':'Staged files have production module imports; install Leaves/Level under Paper23/CertificateCycle, main at Paper23/CertificateCycle.lean, then actually build. No cycle claim is justified until all kernel checks pass.'}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
