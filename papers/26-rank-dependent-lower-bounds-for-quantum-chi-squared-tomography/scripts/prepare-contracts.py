#!/usr/bin/env python3
"""Manual extraction and reviewed promotion of final explicit P26 contracts.

Extraction performs Lean work and is never an automatic release/static check.
Materialization requires a separately authored statement-correspondence review
bound to the exact extracted type bytes and production source tree. The old
supporting contracts are never promoted or relabelled as whole-paper coverage.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.lake/contract-review'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def source_tree():
    paths = [ROOT / 'Paper26.lean', ROOT / 'lean-toolchain',
             ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']
    paths += list((ROOT / 'Paper26').rglob('*.lean'))
    hashes = {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted(paths)}
    encoded = json.dumps(hashes, sort_keys=True, separators=(',', ':')).encode()
    return digest(encoded), hashes

def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('action', choices=['extract', 'materialize', 'check-reviewed'])
parser.add_argument('reviewed_sha256', nargs='?', help='Exact SHA-256 of the materialized final review manifest for check-reviewed')
parser.add_argument('--review-record', type=Path)
args = parser.parse_args()
if args.action == 'check-reviewed':
    if args.reviewed_sha256 is None or len(args.reviewed_sha256) != 64 or any(c not in '0123456789abcdef' for c in args.reviewed_sha256):
        raise SystemExit('check-reviewed requires an explicit lowercase 64-digit SHA-256.')
    manifest_path = ROOT / 'Verification/final-contract-review.json'
    if not manifest_path.is_file() or digest(manifest_path.read_bytes()) != args.reviewed_sha256:
        raise SystemExit('Exact reviewed manifest digest mismatch or missing review manifest.')
    reviewed = json.loads(manifest_path.read_text())
    current, _ = source_tree()
    if reviewed.get('source_tree_sha256') != current:
        raise SystemExit('Current production tree differs from the exact reviewed tree.')
    types_path = OUT / 'contract-types.json'
    if not types_path.is_file() or reviewed.get('types_sha256') != digest(types_path.read_bytes()):
        raise SystemExit('Exact reviewed type inventory is missing or changed.')
    if reviewed.get('statement_correspondence_reviewed') is not True:
        raise SystemExit('Source-statement correspondence review is incomplete.')
    if not isinstance(reviewed.get('reviewer'), str) or not reviewed['reviewer'].strip() or not isinstance(reviewed.get('review_notes'), str) or not reviewed['review_notes'].strip():
        raise SystemExit('A nonempty reviewer and substantive review notes are required.')
    expected_paths = {f'Verification/Final{name}.lean' for name in ['Challenge', 'Solution', 'NegativePremise', 'NegativeAxiom']}
    expected_paths |= {f'Verification/{name}' for name in ['final-comparator.json', 'final-negative-premise.json', 'final-negative-axiom.json']}
    generated = reviewed.get('generated_files_sha256')
    if not isinstance(generated, dict) or set(generated) != expected_paths:
        raise SystemExit('Review manifest must pin all and only the seven final generated modules/configs.')
    for relative, expected_hash in generated.items():
        generated_path = ROOT / relative
        if not generated_path.is_file() or digest(generated_path.read_bytes()) != expected_hash:
            raise SystemExit('Generated reviewed file is missing or changed: ' + relative)
    print('Exact reviewed final-contract manifest, source tree, type inventory and generated files match.')
    raise SystemExit(0)
if args.reviewed_sha256 is not None:
    raise SystemExit('A positional digest is only valid for check-reviewed.')
if args.action == 'extract':
    OUT.mkdir(parents=True, exist_ok=True)
    before, hashes = source_tree()
    subprocess.run([str(ROOT / 'scripts/lake-local'), 'env', 'lean',
                    'Verification/GenerateContracts.lean'], cwd=ROOT, check=True)
    after, _ = source_tree()
    if before != after:
        raise SystemExit('Production tree changed during extraction; discard the output.')
    rows_path = OUT / 'contract-types.json'
    rows = json.loads(rows_path.read_text())
    if not rows:
        raise SystemExit('No theorem types extracted.')
    record = {'source_tree_sha256': before, 'source_hashes': hashes,
              'types_sha256': digest(rows_path.read_bytes()), 'theorem_count': len(rows),
              'statement_correspondence_reviewed': False,
              'reviewer': '', 'review_notes': ''}
    write_json(OUT / 'extraction.json', record)
    print('Extracted explicit theorem types. Review original source-result correspondence,')
    print('hypotheses and scope, then author an approval JSON bound to extraction.json hashes.')
    print('No final contracts have been materialized or accepted.')
else:
    if args.review_record is None:
        raise SystemExit('materialize requires --review-record PATH to a completed review JSON.')
    record = json.loads(args.review_record.read_text())
    extracted = json.loads((OUT / 'extraction.json').read_text())
    current, _ = source_tree()
    types_path = OUT / 'contract-types.json'
    expected = digest(types_path.read_bytes())
    if current != extracted['source_tree_sha256']:
        raise SystemExit('Production sources differ from extraction; extract and review again.')
    if record.get('source_tree_sha256') != current or record.get('types_sha256') != expected:
        raise SystemExit('Review record is not bound to these exact production/type hashes.')
    if extracted['types_sha256'] != expected:
        raise SystemExit('Extracted type bytes changed; extract and review again.')
    if record.get('statement_correspondence_reviewed') is not True:
        raise SystemExit('A completed source-statement correspondence review is required.')
    if not record.get('reviewer', '').strip() or not record.get('review_notes', '').strip():
        raise SystemExit('Review record must identify the reviewer and substantive review notes.')
    rows = json.loads(types_path.read_text())
    if not rows or any('⋯' in row['type'] for row in rows):
        raise SystemExit('Empty or truncated explicit types.')
    header = ('import Paper26\n\n'
        '/-! Explicit final types promoted only after exact-hash correspondence review. -/\n'
        'open scoped BigOperators ENNReal NNReal Matrix ComplexOrder MatrixOrder\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 0\n\n'
        'local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=\n'
        '  inferInstanceAs (MeasurableSpace (m → n → ℂ))\n\n'
        'local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=\n'
        '  inferInstanceAs (BorelSpace (m → n → ℂ))\n\n')
    universes = sorted({u for row in rows for u in row['universes']})
    if universes:
        header += 'universe ' + ' '.join(universes) + '\n\n'
    header += 'namespace P26FinalContract\n\n'
    docs = {name: header for name in ['Challenge', 'Solution', 'NegativePremise', 'NegativeAxiom']}
    names = []
    for index, row in enumerate(rows):
        name = row['name'].removeprefix('Paper26.').replace('.', '_')
        ty = row['type']
        names.append('P26FinalContract.' + name)
        docs['Challenge'] += f'theorem {name} : {ty} := by\n  sorry\n\n'
        proof = f'theorem {name} : {ty} := by\n  exact {row["name"]}\n\n'
        docs['Solution'] += proof
        docs['NegativePremise'] += (f'theorem {name} : False → ({ty}) := by\n  intro h\n  exact h.elim\n\n' if index == 0 else proof)
        docs['NegativeAxiom'] += (f'axiom forbidden_final_component : {ty}\n\ntheorem {name} : {ty} := by\n  exact forbidden_final_component\n\n' if index == 0 else proof)
    for name, contents in docs.items():
        (ROOT / f'Verification/Final{name}.lean').write_text(contents + 'end P26FinalContract\n')
    for file, module in [('final-comparator.json', 'Solution'), ('final-negative-premise.json', 'NegativePremise'), ('final-negative-axiom.json', 'NegativeAxiom')]:
        write_json(ROOT / 'Verification' / file,
            {'challenge_module': 'Verification.FinalChallenge', 'solution_module': f'Verification.Final{module}',
             'theorem_names': names, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'enable_nanoda': False})
    approved = dict(record)
    approved['generated_files_sha256'] = {str(p.relative_to(ROOT)): digest(p.read_bytes())
        for p in sorted((ROOT / 'Verification').glob('Final*.lean'))}
    approved['generated_files_sha256'].update({str(p.relative_to(ROOT)): digest(p.read_bytes())
        for p in sorted((ROOT / 'Verification').glob('final-*.json'))})
    write_json(ROOT / 'Verification/final-contract-review.json', approved)
    print(f'Materialized {len(names)} exact reviewed final statements; no build/Comparator acceptance claimed.')
