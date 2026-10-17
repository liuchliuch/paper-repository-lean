#!/usr/bin/env python3
"""Export candidates for the kernel-checked projected transpose modulo six.

Python prepares sparse lists only. Every leaf and merge is checked by
`decide +kernel`, using the proved original-coordinate coface expansion.
The staged files are not a proof until they have actually compiled.
"""
from pathlib import Path
from collections import defaultdict
from itertools import groupby
import argparse
import hashlib
import json

ROOT = Path.cwd()
parser = argparse.ArgumentParser()
parser.add_argument('--source', default='generation-inputs/certificate.json')
parser.add_argument('--output-dir', default='work/lean-cocycle-staging')
parser.add_argument('--declarations-per-module', type=int, default=16)
parser.add_argument('--bucket-from-level', type=int, default=8,
                    help='Use proved bucket semantics for this level and later')
args = parser.parse_args()
source = ROOT / args.source
data = json.loads(source.read_text())
out = ROOT / args.output_dir
out.mkdir(parents=True, exist_ok=True)
perms = data['permutations']
edges = data['subdivided_graph']['oriented_edges']


def key(cube):
    result = 0
    for token in cube:
        result = 71 * result + token
    return result


def decode(n):
    return [n // 71**i % 71 for i in (3, 2, 1, 0)]


phi = []
for canonical, values in data['detecting_cocycle_phi']:
    for pi, coefficient in enumerate(values):
        if coefficient:
            cube = [0] * 4
            for token, label in zip(canonical, perms[pi]):
                cube[label] = token
            phi.append((key(cube), coefficient))
phi.sort()
assert len({k for k, _ in phi}) == len(phi)
incident = [[] for _ in range(32)]
for e, (u, v) in enumerate(edges):
    incident[u].append(e)
    incident[v].append(e)


def valid(cube):
    occupied = set()
    for token in cube:
        vertices = {token} if token < 32 else set(edges[token - 32])
        if occupied & vertices:
            return False
        occupied |= vertices
    return True


def cofaces(entries):
    result = defaultdict(int)
    for k, value in entries:
        cube = decode(k)
        for coordinate, vertex in enumerate(cube):
            if vertex >= 32:
                continue
            for e in incident[vertex]:
                expanded = cube.copy()
                expanded[coordinate] = 32 + e
                if not valid(expanded):
                    continue
                u, v = edges[e]
                incidence = int(v == vertex) - int(u == vertex)
                sign = (-1)**sum(32 <= token < 32 + e for token in cube)
                result[key(expanded)] += value * incidence * sign
    return sorted((k, v % 6) for k, v in result.items() if v % 6)


def merge(left, right):
    result = defaultdict(int, left)
    for k, value in right:
        result[k] += value
    return sorted((k, v % 6) for k, v in result.items() if v % 6)


def literal(entries):
    return '[' + ', '.join(f'({k}, {v})' for k, v in entries) + ']'


def declare_list(name, entries):
    if len(entries) <= 256:
        return f'noncomputable def {name} : List (ℕ × ℤ) := {literal(entries)}\n'
    pieces = [entries[i:i+256] for i in range(0, len(entries), 256)]
    result = ''.join(f'noncomputable def {name}Part{i} : List (ℕ × ℤ) := {literal(piece)}\n'
                     for i, piece in enumerate(pieces))
    return result + f'noncomputable def {name} : List (ℕ × ℤ) := ' + \
        ' ++ '.join(f'{name}Part{i}' for i in range(len(pieces))) + '\n'


def declare_buckets(name, entries):
    """Keep each data declaration small without a separate alias per bucket."""
    buckets = [(k, list(g)) for k, g in groupby(entries, lambda p: p[0] // 5041)]
    if not buckets:
        return f'noncomputable def {name} : BucketVector := []\n'
    blocks, block, size = [], [], 0
    for bucket in buckets:
        if block and size + len(bucket[1]) > 256:
            blocks.append(block)
            block, size = [], 0
        block.append(bucket)
        size += len(bucket[1])
    if block:
        blocks.append(block)
    text = ''.join(f'noncomputable def {name}Part{i} : BucketVector := {part}\n'
                   for i, part in enumerate(blocks))
    return text + f'noncomputable def {name} : BucketVector := ' + \
        ' ++ '.join(f'{name}Part{i}' for i in range(len(blocks))) + '\n'


# CertificateData names exactly the depth-eight subtrees, in inorder.
cuts = []
subtree_index = 0


def partition(entries, depth=0):
    global subtree_index
    if depth == 8:
        expression = f'phiTree{subtree_index}'
        subtree_index += 1
        cuts.append((expression, entries))
        return
    if not entries:
        return
    middle = len(entries) // 2
    k, value = entries[middle]
    partition(entries[:middle], depth + 1)
    cuts.append((f'(.node {k} {value} .empty .empty)', [(k, value)]))
    partition(entries[middle + 1:], depth + 1)


partition(phi)
assert subtree_index == 256 and len(cuts) == 511
header = '''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Paper23.CertificateChecks
open Cubical CertificateData
attribute [local irreducible] codeChain
'''
lines = ['import Paper23.CertificateTreeCuts\n', header]
for i, (expression, _) in enumerate(cuts):
    lines.append(f'noncomputable def phiCut{i} : LookupTree := {expression}\n')
lines.append('noncomputable def phiCuts : List LookupTree := [\n  ' +
             ',\n  '.join(f'phiCut{i}' for i in range(len(cuts))) + ']\n')
lines.append('theorem phiCuts_spec : phiCuts = cutTree 8 phiTable := by rfl\n')
lines.append('end Paper23.CertificateChecks\n')
(out / 'Data.lean').write_text(''.join(lines))
per_module = args.declarations_per_module
leaf_count = (len(cuts) + per_module - 1) // per_module
leaves = [cofaces(entries) for _, entries in cuts]
modules = ['Paper23.CertificateCocycle.Data']
for block in range(leaf_count):
    lines = ['import Paper23.CertificateCocycle.Data\n', header]
    for i in range(block * per_module, min((block + 1) * per_module, len(cuts))):
        name = f'cocycleLeaf{i}'
        lines.append(declare_list(name, leaves[i]))
        lines.append(f'''theorem {name}_check :
    modularCollapse 16 ((codeTreeCofaces phiCut{i}).map (fun p => [p])) = [{name}] := by
  exact eq_of_beq (by decide +kernel)
theorem {name}_chain : reduceChain (codeChain {name}) =
    reduceChain (restrictCubes 3 (coBoundary (codeChain (treeEntries phiCut{i})))) := by
  exact (modularNormalization_sound 16 (codeTreeCofaces phiCut{i}) {name} {name}_check).trans
    (congrArg reduceChain (codeTreeCofaces_sound phiCut{i}))
''')
    lines.append('end Paper23.CertificateChecks\n')
    (out / f'Leaves{block:02}.lean').write_text(''.join(lines))
    modules.append(f'Paper23.CertificateCocycle.Leaves{block:02}')

level = [(f'cocycleLeaf{i}', entries,
          f'codeChain (treeEntries phiCut{i})', f'Paper23.CertificateCocycle.Leaves{i // per_module:02}')
         for i, entries in enumerate(leaves)]
level_index = 0
source_nodes = []
while len(level) > 1:
    level_index += 1
    bucketed = level_index >= args.bucket_from_level
    if level_index == args.bucket_from_level:
        dependencies = sorted({item[3] for item in level})
        bridged = []
        previous_bridge = None
        for i, (old_name, entries, source_name, _) in enumerate(level):
            bridge_module = f'Paper23.CertificateCocycle.BucketBase{level_index-1}_{i}'
            imports = list(dependencies) + ['Paper23.CertificateBucketBridge']
            if previous_bridge:
                imports.append(previous_bridge)
            lines = [*(f'import {dep}\n' for dep in imports), header,
                     'set_option Elab.async false\n']
            name = f'cocycleBucketBase{level_index-1}_{i}'
            lines.append(declare_buckets(name, entries))
            lines.append(f'''theorem {name}_check : unpackBuckets {name} = {old_name} := by
  exact eq_of_beq (by decide +kernel)
theorem {name}_chain : reduceChain (bucketChain {name}) =
    reduceChain (restrictCubes 3 (coBoundary ({source_name}))) := by
  rw [bucketChain_of_unpack_eq _ _ {name}_check]
  exact {old_name}_chain
''')
            lines.append('end Paper23.CertificateChecks\n')
            (out / f'BucketBase{level_index-1}_{i}.lean').write_text(''.join(lines))
            modules.append(bridge_module)
            previous_bridge = bridge_module
            bridged.append((name, entries, source_name, bridge_module))
        level = bridged
    pairs = [(level[i], level[i+1]) for i in range(0, len(level)-1, 2)]
    next_level = []
    for block in range((len(pairs) + per_module - 1) // per_module):
        selected = pairs[block * per_module:(block + 1) * per_module]
        dependencies = sorted({item[3] for pair in selected for item in pair})
        lines = [*(f'import {dep}\n' for dep in dependencies), header,
                 'set_option Elab.async false\n' if bucketed else '']
        module = f'Paper23.CertificateCocycle.Level{level_index}_{block:02}'
        for j, ((ln, lx, ls, _), (rn, rx, rs, _)) in enumerate(selected):
            index = block * per_module + j
            name = f'cocycleNode{level_index}_{index}'
            source_name = f'cocycleSource{level_index}_{index}'
            entries = merge(lx, rx)
            lines.append((declare_buckets if bucketed else declare_list)(name, entries))
            lines.append(f'noncomputable def {source_name} : RawChain := {ls} + {rs}\n')
            chain_semantics = 'bucketChain' if bucketed else 'codeChain'
            merge_name = 'modularMergeBuckets' if bucketed else 'modularMerge'
            lines.append(f'''theorem {name}_check : {merge_name} {ln} {rn} = {name} := by
  exact eq_of_beq (by decide +kernel)
theorem {name}_chain : reduceChain ({chain_semantics} {name}) =
    reduceChain (restrictCubes 3 (coBoundary {source_name})) := by
  rw [← {name}_check, {merge_name}_sound, {ln}_chain, {rn}_chain]
  simp only [{source_name},map_add]
''')
            source_nodes.append(source_name)
            next_level.append((name, entries, source_name, module))
        lines.append('end Paper23.CertificateChecks\n')
        (out / f'Level{level_index}_{block:02}.lean').write_text(''.join(lines))
        modules.append(module)
    if len(level) % 2:
        next_level.append(level[-1])
    level = next_level

name, root_entries, root_source, dependency = level[0]
assert root_entries == [], 'Projected transpose is nonzero modulo six'
lines = [f'import {dependency}\n', header]
lines.append(f'''theorem cocycleSource_eq_phiVector : {root_source} = phiVector := by
  rw [phiVector_cut_sum 8, ← phiCuts_spec]
  simp only [phiCuts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ''' + ',\n    '.join(source_nodes) + ', add_assoc, add_zero]\n')
root_semantics = 'bucketChain' if level_index >= args.bucket_from_level else 'codeChain'
lines.append(f'''theorem projected_transpose_zero : reduceChain (restrictCubes 3 (coBoundary phiVector)) = 0 := by
  rw [← cocycleSource_eq_phiVector, ← {name}_chain]
  change reduceChain ({root_semantics} []) = 0
  simp

/-- The imported detector annihilates boundaries of every original three-chain. -/
theorem cocycle (x : RawChain) (hx : x ∈ Chains 3) : phi (boundary x) = 0 :=
  cocycle_of_modular_transpose projected_transpose_zero x hx

end Paper23.CertificateChecks
''')
(out / 'CertificateCocycle.lean').write_text(''.join(lines))
modules.append('Paper23.CertificateCocycle')
summary = {
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'phi_terms': len(phi), 'cuts': len(cuts),
    'leaf_nonzero_terms': sum(map(len, leaves)), 'merge_levels': level_index,
    'root': name, 'root_source': root_source, 'modules': modules,
    'note': 'Candidate data only; each listed module must actually compile with ordinary kernel proofs.'
}
(out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'modules'}, indent=2))
