#!/usr/bin/env python3
"""Export ordinary-kernel sparse checks of the actual sixfold bounding chain.

The integer calculation supplies candidate normal forms, never proof terms.
Only the generated `decide +kernel` theorems and chain-soundness lemmas certify
these candidates. Source b is reordered by its labelled cube code, preserving
all coefficients. No group-ring elimination is rerun.
"""
from pathlib import Path
from collections import defaultdict
import argparse, hashlib, json
root=Path.cwd()
p=argparse.ArgumentParser()
p.add_argument('--source',default='generation-inputs/certificate.json')
p.add_argument('--probe',action='store_true')
p.add_argument('--probe-index',type=int,default=0)
p.add_argument('--chunk-size',type=int,default=64)
p.add_argument('--leaves-per-block',type=int,default=16)
p.add_argument('--nodes-per-block',type=int,default=16)
p.add_argument('--stage-bucket-tail',action='store_true',
    help='stage only levels 4 onward, preserving every existing lower-level source')
a=p.parse_args()
source=root/a.source; data=json.loads(source.read_text())
perms=data['permutations'];edges=data['subdivided_graph']['oriented_edges']
def key(c):
    n=0
    for x in c:n=71*n+x
    return n
def labelled(c,pi):
    raw=[0]*4
    for x,l in zip(c,perms[pi]):raw[l]=x
    return raw
canons=[key(c) for c,_ in data['bounding_chain_b']]
b=sorted((key(labelled(c,pi)),v,ci,labelled(c,pi))
    for ci,(c,terms) in enumerate(data['bounding_chain_b']) for pi,v in terms)
z=[(key(labelled(c,pi)),v) for c,terms in data['cycle_z'] for pi,v in terms]
zchunks=[z[i:i+64] for i in range(0,len(z),64)]
chunks=[b[i:i+a.chunk_size] for i in range(0,len(b),a.chunk_size)]
def boundary(chunk):
    result=defaultdict(int)
    for _,a,_,c in chunk:
        for coordinate,token in enumerate(c):
            if token<32:continue
            sign=(-1)**sum(32<=t<token for t in c)
            for endpoint,factor in zip(edges[token-32],[-1,1]):
                f=c.copy();f[coordinate]=endpoint
                result[key(f)]+=a*sign*factor
    return result
def normal(chunk,target):
    d=boundary(chunk)
    for k,v in target:d[k]-=6*v
    return sorted((k,v) for k,v in d.items() if v)
def merge(x,y):
    d=defaultdict(int,x)
    for k,v in y:d[k]+=v
    return sorted((k,v) for k,v in d.items() if v)
def literal(xs):
    return '['+', '.join(f'({k}, {v if v>=0 else f"(Int.negSucc {-v-1})"})' for k,v in xs)+']'
def list_def(lines,name,xs):
    if len(xs)<=256:
        lines.append(f'noncomputable def {name} : List (ℕ × ℤ) := {literal(xs)}\n')
    else:
        names=[]
        for j in range(0,len(xs),256):
            part=f'{name}Part{j//256}'
            names.append(part)
            lines.append(f'noncomputable def {part} : List (ℕ × ℤ) := {literal(xs[j:j+256])}\n')
        lines.append(f'noncomputable def {name} : List (ℕ × ℤ) := '+ ' ++ '.join(names)+'\n')
header='''import Paper23.BoundingSupport
import Paper23.CertificateChecks
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Paper23.Bounding
open Cubical CertificateData CertificateChecks
attribute [local irreducible] codeChain
'''
def leaf_text(i,chunk,probe=False):
    lines=[]
    prefix='probe' if probe else 'bounding'
    if probe:
        for ci in sorted({x[2] for x in chunk}):
            lines.append(f'theorem probeCanonical{ci} : ValidThree {canons[ci]} := by decide +kernel\n')
    name=f'{prefix}Leaf{i}';entries=f'{prefix}Entries{i}'
    list_def(lines,entries,[(k,v) for k,v,_,_ in chunk])
    lines.append(f'theorem {name}_valid : ∀ p ∈ {entries}, ValidThree p.1 := by\n  simp only [{entries}, List.forall_mem_cons]\n')
    proofs=[f'validThree_of_perm {k} {canons[ci]} (by decide +kernel) {"probeCanonical" if probe else "boundingCanonical"}{ci}' for k,v,ci,_ in chunk]
    lines.append('  exact ⟨'+',\n    '.join(proofs+['by simp'])+'⟩\n')
    lines.append(f'theorem {name}_mem : codeChain {entries} ∈ Chains 3 := codeChain_mem_three _ {name}_valid\n')
    target=zchunks[i] if i<len(zchunks) else []
    targetname=f'zEntries{i}' if target else '([] : List (ℕ × ℤ))'
    targetchain=f'codeChain zEntries{i}' if target else '(0 : RawChain)'
    result=normal(chunk,target)
    list_def(lines,name,result)
    lines.append(f'''theorem {name}_check :
    collapse 10 (((codeDifferential {entries}) ++ scaleEntries (-6) {targetname}).map
      (fun p => [p])) = [{name}] := by decide +kernel
 theorem {name}_chain : codeChain {name} =
    boundary (codeChain {entries}) + (-6 : ℤ) • {targetchain} := by
  simpa only [codeChain_nil] using (leaf_sound 10 {entries} {targetname} {name} {name}_valid {name}_check)
''')
    return ''.join(lines),result,name,f'codeChain {entries}',targetchain,f'{name}_mem'
if a.probe:
    text,*_=leaf_text(a.probe_index,chunks[a.probe_index],True)
    (root/'Paper23/BoundingProbe.lean').write_text(header+text+'end Paper23.Bounding\n')
    print(json.dumps({'probe_terms':len(chunks[a.probe_index]),'canonical_checks':len({x[2] for x in chunks[a.probe_index]})},indent=2))
    raise SystemExit
if a.stage_bucket_tail:
    # This conversion does not touch the cached flat prefix. The staged files
    # are installed only after its level-three build barrier has completed.
    stage=root/'work/bounding-bucket-tail'; stage.mkdir(parents=True,exist_ok=True)
    oldmeta=json.loads((root/'work/bounding-generation.json').read_text())
    assert oldmeta['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
    assert oldmeta['chunks']==len(chunks) and a.chunk_size==64 and a.leaves_per_block==16
    level=[]
    for i,chunk in enumerate(chunks):
        target=zchunks[i] if i<len(zchunks) else []
        level.append((f'boundingLeaf{i}',normal(chunk,target),f'codeChain boundingEntries{i}',
          f'codeChain zEntries{i}' if target else '(0 : RawChain)',f'boundingLeaf{i}_mem',
          f'Paper23.Bounding.Leaves{i//a.leaves_per_block:03}',False))
    source_nodes=[];target_nodes=[];mods_by_level=[];level_index=0;files={}
    bucket_header=header.replace('import Paper23.BoundingSupport',
      'import Paper23.BoundingBucketSupport').replace('set_option maxHeartbeats 0',
      'set_option maxHeartbeats 0\nset_option Elab.async false').replace(
      'irreducible] codeChain','irreducible] codeChain bucketChain')
    def bucket_def(lines,name,xs):
        buckets=[]
        for k,v in xs:
            label=k//5041
            if not buckets or buckets[-1][0]!=label:buckets.append((label,[]))
            buckets[-1][1].append((k,v))
        parts=[];part=[];weight=0
        for label,entries in buckets:
            if len(entries)>256:
                inner=f'{name}Bucket{label}'
                list_def(lines,inner,entries)
                value=inner;cost=1
            else:value=literal(entries);cost=len(entries)
            if part and weight+cost>256:
                partname=f'{name}Part{len(parts)}';parts.append(partname)
                lines.append(f'noncomputable def {partname} : BucketVector := ['+', '.join(part)+']\n')
                part=[];weight=0
            part.append(f'({label}, {value})');weight+=cost
        if part:
            partname=f'{name}Part{len(parts)}';parts.append(partname)
            lines.append(f'noncomputable def {partname} : BucketVector := ['+', '.join(part)+']\n')
        lines.append(f'noncomputable def {name} : BucketVector := '+(' ++ '.join(parts) if parts else '[]')+'\n')
    while len(level)>1:
        level_index+=1;nextlevel=[];mods=[]
        width=16 if level_index<=3 else {4:8,5:4,6:2}.get(level_index,1)
        for block in range(((len(level)//2)+width-1)//width):
            mod=f'Paper23.Bounding.Level{level_index}Part{block:03}';mods.append(mod)
            indices=range(block*width,min((block+1)*width,len(level)//2))
            required=sorted({level[2*ni+j][5] for ni in indices for j in (0,1)})
            lines=[''.join(f'import {m}\n' for m in required),bucket_header]
            for ni in indices:
                (ln,lx,ls,lt,lmem,lmod,lb),(rn,rx,rs,rt,rmem,rmod,rb)=level[2*ni:2*ni+2]
                name=f'boundingNode{level_index}_{ni}';src=f'boundingSource{level_index}_{ni}'
                result=merge(lx,rx)
                if level_index>=4:bucket_def(lines,name,result)
                lines.append(f'noncomputable def {src} : RawChain := {ls} + {rs}\n');source_nodes.append(src)
                if lt=='(0 : RawChain)' and rt=='(0 : RawChain)':target='(0 : RawChain)'
                else:
                    target=f'boundingTarget{level_index}_{ni}'
                    lines.append(f'noncomputable def {target} : RawChain := {lt} + {rt}\n');target_nodes.append(target)
                if level_index>=4:
                    le=ln if lb else f'(packBuckets {ln})';re=rn if rb else f'(packBuckets {rn})'
                    lh=f'{ln}_chain' if lb else f'(packed_node_sound {ln} ({ls}) ({lt}) {ln}_chain)'
                    rh=f'{rn}_chain' if rb else f'(packed_node_sound {rn} ({rs}) ({rt}) {rn}_chain)'
                    unfold=f'{src}, '+(f'{target}, ' if target!='(0 : RawChain)' else '')
                    lines.append(f'''theorem {name}_check : mergeBuckets {le} {re} = {name} := by
  exact eq_of_beq (by decide +kernel)
theorem {name}_chain : bucketChain {name} = boundary {src} + (-6 : ℤ) • {target} := by
  simpa only [{unfold}add_zero] using (bucket_node_sound {le} {re} {name}
    ({ls}) ({rs}) ({lt}) ({rt}) {lh} {rh} {name}_check)
theorem {name}_mem : {src} ∈ Chains 3 := (Chains 3).add_mem {lmem} {rmem}
''')
                nextlevel.append((name,result,src,target,f'{name}_mem',mod,level_index>=4))
            if level_index>=4:
                lines.append('end Paper23.Bounding\n');files[mod]=''.join(lines)
        if len(level)%2:nextlevel.append(level[-1])
        mods_by_level.append(mods);level=nextlevel
    name,result,src,target,mem,rootmod,_=level[0]
    assert result==[]
    main=[''.join(f'import {m}\n' for m in mods_by_level[-1]),bucket_header]
    main.append(f'noncomputable def b : RawChain := {src}\n')
    main.append(f'theorem b_mem_chains : b ∈ Chains 3 := {mem}\n')
    main.append(f'theorem boundingTarget_eq_z : {target} = z := by\n  simp only [\n    '+',\n    '.join(target_nodes)+',\n    z, zChunks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc, add_zero, zero_add]\n')
    main.append(f'''theorem bounding : boundary b = (6 : ℕ) • z := by
  have h := {name}_chain
  change bucketChain [] = boundary b + (-6 : ℤ) • {target} at h
  rw [bucketChain_nil, boundingTarget_eq_z] at h
  exact bounding_of_zero b z h

noncomputable def bChain : Chains 3 := ⟨b,b_mem_chains⟩
theorem ordered_bounding : differential 2 bChain = (6 : ℕ) • zChain := by
  apply Subtype.ext
  exact bounding
end Paper23.Bounding
''')
    files['Paper23.Bounding']=''.join(main)
    for mod,text in files.items():
        f=stage/(mod.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_text(text)
    oldmeta.update({'levels':mods_by_level,'bucket_from_level':4,'bucket_widths':{'4':8,'5':4,'6':2,'later':1}})
    (stage/'generation.json').write_text(json.dumps(oldmeta,indent=2)+'\n')
    (stage/'files.json').write_text(json.dumps(list(files),indent=2)+'\n')
    print(json.dumps({'staged_modules':len(files),'bucket_from_level':4,'source_sha256':oldmeta['source_sha256']},indent=2))
    raise SystemExit
out=root/'Paper23/Bounding';out.mkdir(exist_ok=True)
canon_mods=[]
for block in range((len(canons)+127)//128):
    mod=f'Paper23.Bounding.Canon{block:03}';canon_mods.append(mod)
    lines=[header]
    for ci in range(block*128,min((block+1)*128,len(canons))):
        lines.append(f'theorem boundingCanonical{ci} : ValidThree {canons[ci]} := by decide +kernel\n')
    lines.append('end Paper23.Bounding\n')
    (out/f'Canon{block:03}.lean').write_text(''.join(lines))
leaf_mods=[];level=[]
for block in range((len(chunks)+a.leaves_per_block-1)//a.leaves_per_block):
    mod=f'Paper23.Bounding.Leaves{block:03}';leaf_mods.append(mod)
    indices=range(block*a.leaves_per_block,min((block+1)*a.leaves_per_block,len(chunks)))
    required=sorted({x[2]//128 for i in indices for x in chunks[i]})
    lines=[''.join(f'import Paper23.Bounding.Canon{j:03}\n' for j in required),header]
    for i in indices:
        text,result,name,src,target,mem=leaf_text(i,chunks[i]);lines.append(text)
        level.append((name,result,src,target,mem,mod))
    lines.append('end Paper23.Bounding\n')
    (out/f'Leaves{block:03}.lean').write_text(''.join(lines))
mods_by_level=[];source_nodes=[];target_nodes=[];level_index=0
prev_mods=leaf_mods
while len(level)>1:
    level_index+=1;nextlevel=[];next_mods=[]
    for block in range(((len(level)//2)+a.nodes_per_block-1)//a.nodes_per_block):
        mod=f'Paper23.Bounding.Level{level_index}Part{block:03}';next_mods.append(mod)
        node_indices=range(block*a.nodes_per_block,min((block+1)*a.nodes_per_block,len(level)//2))
        required=sorted({level[2*ni+j][5] for ni in node_indices for j in (0,1)})
        lines=[''.join(f'import {m}\n' for m in required),header]
        for ni in range(block*a.nodes_per_block,min((block+1)*a.nodes_per_block,len(level)//2)):
            (ln,lx,ls,lt,lmem,lmod),(rn,rx,rs,rt,rmem,rmod)=level[2*ni:2*ni+2]
            name=f'boundingNode{level_index}_{ni}';src=f'boundingSource{level_index}_{ni}'
            result=merge(lx,rx);list_def(lines,name,result)
            lines.append(f'noncomputable def {src} : RawChain := {ls} + {rs}\n');source_nodes.append(src)
            if lt=='(0 : RawChain)' and rt=='(0 : RawChain)':target='(0 : RawChain)'
            else:
                target=f'boundingTarget{level_index}_{ni}'
                lines.append(f'noncomputable def {target} : RawChain := {lt} + {rt}\n');target_nodes.append(target)
            lines.append(f'''theorem {name}_check : merge {ln} {rn} = {name} := by decide +kernel
 theorem {name}_chain : codeChain {name} = boundary {src} + (-6 : ℤ) • {target} := by
  simpa only [{target + ", " if target != "(0 : RawChain)" else ""}add_zero] using (node_sound {ln} {rn} {name} ({ls}) ({rs}) ({lt}) ({rt}) {ln}_chain {rn}_chain {name}_check)
 theorem {name}_mem : {src} ∈ Chains 3 := (Chains 3).add_mem {lmem} {rmem}
''')
            nextlevel.append((name,result,src,target,f'{name}_mem',mod))
        lines.append('end Paper23.Bounding\n')
        (out/f'Level{level_index}Part{block:03}.lean').write_text(''.join(lines))
    if len(level)%2:nextlevel.append(level[-1])
    prev_mods=next_mods;mods_by_level.append(next_mods);level=nextlevel
name,result,src,target,mem,rootmod=level[0]
assert result==[], 'Candidate bounding identity failed'
main=[''.join(f'import {m}\n' for m in prev_mods),header]
main.append(f'noncomputable def b : RawChain := {src}\n')
main.append(f'theorem b_mem_chains : b ∈ Chains 3 := {mem}\n')
main.append(f'theorem boundingTarget_eq_z : {target} = z := by\n  simp only [\n    '+',\n    '.join(target_nodes)+',\n    z, zChunks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc, add_zero, zero_add]\n')
main.append(f'''theorem bounding : boundary b = (6 : ℕ) • z := by
  have h := {name}_chain
  change codeChain [] = boundary b + (-6 : ℤ) • {target} at h
  rw [codeChain_nil, boundingTarget_eq_z] at h
  exact bounding_of_zero b z h

noncomputable def bChain : Chains 3 := ⟨b,b_mem_chains⟩
theorem ordered_bounding : differential 2 bChain = (6 : ℕ) • zChain := by
  apply Subtype.ext
  exact bounding
end Paper23.Bounding
''')
(root/'Paper23/Bounding.lean').write_text(''.join(main))
summary={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_order':'ascending labelled base71 cube code','b_terms':len(b),'canonical_cubes':len(canons),'chunks':len(chunks),'leaf_modules':leaf_mods,'canon_modules':canon_mods,'levels':mods_by_level,'root_module':'Paper23.Bounding','root_normal_form':name,'max_leaf_terms':max(map(lambda c:len(normal(c,[])),chunks))}
(root/'work/bounding-generation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if not isinstance(v,list)},indent=2))
