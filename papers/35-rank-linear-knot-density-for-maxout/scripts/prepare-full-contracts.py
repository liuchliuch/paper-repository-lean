#!/usr/bin/env python3
"""Manual deferred materialization, followed by a separate reviewed SHA256 check."""
from pathlib import Path
import argparse, hashlib, json, subprocess
ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT/'Verification/preparation-inputs.json'
types_path = ROOT/'Verification/full-contract-types.json'
manifest_path = ROOT/'Verification/full-contracts-manifest.json'
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def stable():
    inputs = json.loads(BASELINE.read_text())['files']
    for name, expected in inputs.items():
        if not (ROOT/name).is_file() or digest(ROOT/name) != expected:
            raise SystemExit('Frozen preparation input changed: '+name)
    return inputs
def prepare():
    inputs = stable()
    if (ROOT/'Verification/FullDelivery').exists() or manifest_path.exists() or types_path.exists():
        raise SystemExit('Preparation outputs exist. Preserve/review them before explicitly removing them to regenerate.')
    lake = str(ROOT/'scripts/lake-local')
    subprocess.run([lake,'build','Paper35'],cwd=ROOT,check=True)
    subprocess.run([lake,'env','lean','Verification/GenerateFullContracts.lean'],cwd=ROOT,check=True)
    rows = json.loads(types_path.read_text())
    expected = json.loads((ROOT/'Verification/full-targets.json').read_text())
    if {x['name'] for x in rows} != set(expected):
        raise SystemExit('Export did not cover exactly the frozen named coverage inventory')
    permitted_non_theorems = {
      'Paper35.GaussianMarked.ClassicalCroftonLaw',
      'Paper35.GaussianMarked.ClassicalCroftonRegularityLaw'}
    non_theorems = {x['name'] for x in rows if not x['is_theorem']}
    if non_theorems != permitted_non_theorems:
        raise SystemExit('Unexpected non-theorem coverage targets: '+repr(non_theorems-permitted_non_theorems))
    proofs = [x for x in rows if x['is_theorem']]
    if not proofs:
        raise SystemExit('Empty proof contract inventory')
    universes = sorted({u for x in proofs for u in x['universes']})
    head = 'import Paper35\n\nopen scoped BigOperators ENNReal NNReal Topology\n'
    head += 'set_option maxRecDepth 32768\nset_option maxHeartbeats 0\n'
    if universes:
        head += 'universe '+' '.join(universes)+'\n'
    statements = head+'\nnamespace P35Full.Specification\n'
    names = []
    for i, x in enumerate(proofs):
        name = 'result_'+str(i).zfill(3)
        names.append('P35Full.Certificate.'+name)
        statements += '\n-- '+x['name']+'\ndef '+name+' : Prop :=\n  '+x['type']+'\n'
    statements += '\nend P35Full.Specification\n'
    dest = ROOT/'Verification/FullDelivery'
    dest.mkdir()
    (dest/'Statements.lean').write_text(statements)
    for module in ['Challenge', 'Solution', 'NegativePremise', 'NegativeAxiom']:
        text = 'import Verification.FullDelivery.Statements\n\nnamespace P35Full.Certificate\n'
        if module == 'NegativeAxiom':
            text += '\naxiom forbiddenAxiom : False\n'
        for i,x in enumerate(proofs):
            name = 'result_'+str(i).zfill(3)
            ty = 'P35Full.Specification.'+name
            if module == 'NegativePremise' and i == 0:
                ty = 'False → '+ty
            text += '\ntheorem '+name+' : '+ty+' := by\n'
            if module == 'Challenge':
                text += '  sorry\n'
            elif module == 'NegativeAxiom' and i == 0:
                text += '  exact False.elim forbiddenAxiom\n'
            elif module == 'NegativePremise' and i == 0:
                text += '  intro h\n  exact h.elim\n'
            else:
                text += '  exact @'+x['name']+'\n'
        (dest/(module+'.lean')).write_text(text+'\nend P35Full.Certificate\n')
    for filename,module in [('positive','Solution'),('negative-premise','NegativePremise'),('negative-axiom','NegativeAxiom')]:
        config = {'challenge_module':'Verification.FullDelivery.Challenge',
          'solution_module':'Verification.FullDelivery.'+module,'theorem_names':names if filename == 'positive' else names[:1],
          'permitted_axioms':['propext','Classical.choice','Quot.sound'],'enable_nanoda':False}
        (dest/(filename+'.json')).write_text(json.dumps(config,indent=2)+'\n')
    manifest = {'status':'generated_pending_independent_correspondence_review',
      'input_files':inputs, 'targets':expected, 'theorem_count':len(proofs), 'external_definitions':sorted(non_theorems),
      'types_sha256':digest(types_path),
      'files':{str(p.relative_to(ROOT)):digest(p) for p in sorted(dest.iterdir()) if p.is_file()}}
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
    stable()
    print('Generated fixed literal contracts. No independent review or verification pass is claimed.')
    print('Review every type against source anchors, external inputs, hypotheses and quantifiers.')
    print('After independent review: python3 scripts/prepare-full-contracts.py check-reviewed '+digest(manifest_path))
def reviewed(expected_hash):
    inputs = stable()
    if not manifest_path.is_file() or digest(manifest_path) != expected_hash:
        raise SystemExit('Reviewed contract-manifest SHA256 does not match')
    manifest = json.loads(manifest_path.read_text())
    if manifest['input_files'] != inputs:
        raise SystemExit('Generated contracts do not match frozen preparation inputs')
    if digest(types_path) != manifest['types_sha256']:
        raise SystemExit('Exported contract types changed after review')
    for name, expected in manifest['files'].items():
        if not (ROOT/name).is_file() or digest(ROOT/name) != expected:
            raise SystemExit('Generated fixture changed after review: '+name)
    print('Reviewed SHA256 matches unchanged inputs, types and fixtures.')
    print('This check verifies hashes; independent semantic review must already have occurred.')
parser=argparse.ArgumentParser(description=__doc__)
sub=parser.add_subparsers(dest='stage',required=True)
sub.add_parser('prepare',help='Manually build production, export types and materialize literal fixtures')
r=sub.add_parser('check-reviewed',help='Check the SHA256 only after independent semantic review')
r.add_argument('sha256')
args=parser.parse_args()
if args.stage == 'prepare':
    prepare()
else:
    reviewed(args.sha256)
