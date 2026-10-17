"""Small isolated tests for dispatch boundaries; no Lean or certificate work."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from common import (classify_comparator, dependency_pins, inside, papers,
                    real_lake, snapshot, strip_comments)
from verify import execute, gated_suite, static_review
from add_paper import create_paper
from catalog import render
from verification_plan import plan

PHASES='''Building Verification.Challenge
Build completed successfully (3 jobs).
Exporting #[Contract.result] from Verification.Challenge
Building Verification.Solution
Build completed successfully (4 jobs).
Exporting #[Contract.result] from Verification.Solution
'''

def fixture(root: Path):
    project=root/'papers/01-example'
    project.mkdir(parents=True)
    for name,text in {'A.lean':'import Mathlib\nnamespace A\ntheorem result : True := True.intro\nend A\n',
                      'Verification/Challenge.lean':'import A\nnamespace Contract\ntheorem result : True := by sorry\nend Contract\n',
                      'Verification/Solution.lean':'import A\nnamespace Contract\ntheorem result : True := A.result\nend Contract\n',
                      'README.md':'# Example\n', 'EXTERNAL_DEPENDENCIES.md':'# No external paper inputs\n',
                      'lean-toolchain':'leanprover/lean4:v4.24.0\n',
                      'lakefile.toml':'name="A"\n[[lean_lib]]\nname="A"\n',
                      'scripts/lake-local':'#!/bin/sh\nexit 0\n'}.items():
        path=project/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    manifest={'packagesDir':'.lake/packages','packages':[{'name':'mathlib','type':'git','url':'https://github.com/leanprover-community/mathlib4.git','rev':'a'*40}]}
    (project/'lake-manifest.json').write_text(json.dumps(manifest))
    config={'challenge_module':'Verification.Challenge','solution_module':'Verification.Solution',
            'theorem_names':['Contract.result'],'permitted_axioms':['propext','Classical.choice','Quot.sound'],'enable_nanoda':False}
    (project/'Verification/comparator.json').write_text(json.dumps(config))
    meta={'paper_id':'01','title':'Example','source_url':'https://example.org/paper',
          'lean_toolchain':'leanprover/lean4:v4.24.0','production_roots':['A'],'build_targets':['A'],
          'primary_comparator':'main',
          'comparators':[{'id':'main','config':'Verification/comparator.json','expected_rejection':None,'scope':'One fixed result'}],
          'main_results':[{'source_result':'Theorem 1','declaration':'A.result','scope':'True'}],
          'external_dependencies':'EXTERNAL_DEPENDENCIES.md'}
    (project/'publication.json').write_text(json.dumps(meta))
    return project,meta

class ComparatorReceiptTests(unittest.TestCase):
    def test_positive_requires_official_phases_kernel_and_final_success(self):
        output=PHASES+'Running Lean default kernel on solution.\nLean default kernel accepts the solution\nYour solution is okay!\n'
        self.assertTrue(classify_comparator(0,output,['Contract.result']))
        self.assertFalse(classify_comparator(0,'Your solution is okay!',['Contract.result']))
        self.assertFalse(classify_comparator(1,output,['Contract.result']))

    def test_actual_type_and_axiom_rejections(self):
        self.assertTrue(classify_comparator(1,PHASES+"uncaught exception: Challenge and solution theorem statement do not match: 'Contract.result'\n",['Contract.result'],'type'))
        self.assertTrue(classify_comparator(1,PHASES+"uncaught exception: Illegal axiom detected: 'forbidden_axiom'\n",['Contract.result'],'axiom'))

    def test_echoed_rejection_in_failed_build_never_passes(self):
        for expected,message in [('type',"Challenge and solution theorem statement do not match: 'Contract.result'"),('axiom',"Illegal axiom detected: 'forbidden_axiom'")]:
            self.assertFalse(classify_comparator(1,'Building Verification.Solution\nerror: '+message+'\nuncaught exception: Child exited with 1\n',['Contract.result'],expected))
            self.assertFalse(classify_comparator(1,PHASES+'warning: '+message+'\nuncaught exception: Child exited with 1\n',['Contract.result'],expected))

    def test_missing_probe_is_never_a_verified_control(self):
        self.assertFalse(classify_comparator(1,PHASES+'unknown constant Contract.result\n',['Contract.result'],'missing'))

class PortableBoundaryTests(unittest.TestCase):
    def test_local_adapter_is_skipped_and_elan_symlink_name_preserved(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);adapter=root/'scripts/comparator-bin';adapter.mkdir(parents=True)
            (adapter/'lake').write_text('#!/bin/sh\n');(adapter/'lake').chmod(0o755)
            actual=root/'bin';actual.mkdir();(actual/'elan').write_text('#!/bin/sh\n');(actual/'elan').chmod(0o755);(actual/'lake').symlink_to('elan')
            result=real_lake({'PATH':str(adapter)+os.pathsep+str(actual)},root)
            self.assertEqual(result,str(actual/'lake'))
            with self.assertRaises(ValueError):real_lake({'PINKFOLD_LAKE':str(adapter/'lake')},root)
            with self.assertRaises(ValueError):real_lake({'PINKFOLD_LAKE':str(actual)},root)
            shim=root/'papers/01-example/scripts/lake-local';shim.parent.mkdir(parents=True);shim.write_text('#!/bin/sh\n');shim.chmod(0o755)
            with self.assertRaises(ValueError):real_lake({'PINKFOLD_LAKE':str(shim)},root)

    def test_relative_path_gate_rejects_escape_absolute_and_symlink(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);project=root/'project';project.mkdir();outside=root/'outside';outside.write_text('x');(project/'escape').symlink_to(outside)
            for value in ['../outside',str(project/'in.json'),'escape']:
                with self.assertRaises(ValueError):inside(project,value)

    def test_dependency_source_change_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_=fixture(Path(folder));(project/'.lake/packages/mathlib').mkdir(parents=True)
            with patch('common.subprocess.check_output',side_effect=['b'*40+'\n','']):
                with self.assertRaises(ValueError):dependency_pins(project,True)

    def test_nested_comments_and_quoted_markers_are_not_proof_holes(self):
        text='/- outer /- nested -/ end -/\ndef label := "sorry \\" axiom"\n-- admit\ntheorem result : True := True.intro\n'
        cleaned=strip_comments(text)
        self.assertEqual(len(cleaned),len(text))
        self.assertIn('theorem result',cleaned)
        self.assertNotIn('nested',cleaned)
        self.assertNotIn('sorry',cleaned)

    def test_character_and_raw_literals_do_not_hide_following_code(self):
        for literal in ["'\"'", r"'\"'", r'''r#"folder\"#''', r'''r##"sorry " quoted \"##''', r"'\u{2022}'"]:
            text='def label := '+literal+'\ntheorem result : True := by sorry\n'
            cleaned=strip_comments(text)
            self.assertEqual(len(cleaned),len(text))
            self.assertIn('theorem result : True := by sorry',cleaned,literal)

    def test_failed_first_build_still_writes_a_receipt(self):
        import argparse
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);project,meta=fixture(root)
            args=argparse.Namespace(check='build')
            observations=[{'mathlib':{'status':'not_downloaded','revision':'a'*40}},ValueError('Dependency checkout is missing: mathlib')]
            with patch('verify.ROOT',root), patch('verify.real_lake',return_value='/fake/lake'), patch('verify.dependency_pins',side_effect=observations), patch('verify.subprocess.run',return_value=subprocess.CompletedProcess(['lake'],1)):
                self.assertEqual(execute(project,meta,args),1)
            receipts=list((root/'.artifacts').rglob('result.json'))
            self.assertEqual(len(receipts),1)
            record=json.loads(receipts[0].read_text())
            self.assertEqual(record['exit_code'],1)
            self.assertFalse(record['stage_passed'])
            self.assertIn('Dependency checkout is missing',record['postcheck_errors'][0])

class StaticReviewTests(unittest.TestCase):
    def test_primary_configuration_must_be_registered(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder));meta['primary_comparator']='unknown'
            result=static_review(project,meta)
            self.assertFalse(result['static_review_passed'])
            self.assertIn('Primary Comparator configuration is missing',result['errors'])

    def test_static_review_invokes_no_compiler(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder))
            with patch('verify.subprocess.run',side_effect=AssertionError('Unexpected execution')):
                self.assertTrue(static_review(project,meta)['static_review_passed'])

    def test_malformed_official_config_and_empty_result_scope_fail(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder));meta['build_targets']=[];meta['main_results']=[]
            config=json.loads((project/'Verification/comparator.json').read_text());del config['permitted_axioms'];del config['enable_nanoda'];(project/'Verification/comparator.json').write_text(json.dumps(config))
            self.assertFalse(static_review(project,meta)['static_review_passed'])

    def test_metadata_schema_rejects_wrong_nested_types(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder));meta['main_results']=[{'source_result':'Theorem 1','declaration':[], 'scope':'True'}]
            result=static_review(project,meta)
            self.assertFalse(result['static_review_passed'])
            self.assertTrue(any('declaration must be string' in error for error in result['errors']))

    def test_build_targets_cannot_be_options_or_missing_modules(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder))
            for target in ['--help','','Missing.Library']:
                meta['build_targets']=[target]
                self.assertFalse(static_review(project,meta)['static_review_passed'],target)

    def test_unregistered_production_hole_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder));(project/'A.lean').write_text('theorem result : True := by sorry\n')
            self.assertFalse(static_review(project,meta)['static_review_passed'])
            meta['authorized_external_holes']=[{'module':'A','token':'sorry','line':1,'reference':'Published theorem','reason':'Explicit imported theorem, not an own result'}]
            self.assertTrue(static_review(project,meta)['static_review_passed'])

    def test_primary_https_home_path_is_not_a_local_machine_path(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta=fixture(Path(folder));(project/'README.md').write_text('[Primary](https://example.org/home/text/reference.pdf)\n')
            self.assertTrue(static_review(project,meta)['static_review_passed'])

class ReviewedGateTests(unittest.TestCase):
    def test_default_uses_final_primary_and_does_not_fall_back_to_supporting(self):
        import argparse
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);project,meta=fixture(root)
            meta['primary_comparator']='final'
            meta['comparators'].append({'id':'final','available':False,'planned_config':'final.json'})
            args=argparse.Namespace(check='comparator',suite=None,allow_diagnostic=False,reviewed_manifest_sha256=None)
            with patch('verify.ROOT',root), patch('verify.real_lake',return_value='/fake/lake'), patch('verify.dependency_pins',return_value={}), patch('verify.subprocess.run',side_effect=AssertionError('Unexpected execution')):
                with self.assertRaisesRegex(ValueError,'explicit --reviewed-manifest-sha256'):
                    execute(project,meta,args)

    def test_stale_boolean_and_wrong_digest_cannot_unlock(self):
        with tempfile.TemporaryDirectory() as folder:
            project=Path(folder);review=project/'review.json';review.write_text('{"statement_correspondence_reviewed":true}')
            suite={'id':'full','available':False,'reviewed_manifest':'review.json','planned_config':'final.json'}
            with self.assertRaises(ValueError):gated_suite(project,suite)
            suite['review_command']=['python3','check.py','{reviewed_sha256}']
            with patch('verify.subprocess.run') as run:
                with self.assertRaises(ValueError):gated_suite(project,suite,reviewed_hash='0'*64)
                run.assert_not_called()

    def test_exact_hash_runs_declared_guard_and_guard_failure_blocks(self):
        with tempfile.TemporaryDirectory() as folder:
            project=Path(folder);review=project/'review.json';review.write_text('{}');(project/'final.json').write_text('{}')
            expected=hashlib.sha256(review.read_bytes()).hexdigest();suite={'id':'full','available':False,'reviewed_manifest':'review.json','planned_config':'final.json','review_command':['python3','check.py','{reviewed_sha256}']}
            with patch('verify.subprocess.run') as run:
                result=gated_suite(project,suite,reviewed_hash=expected)
                self.assertEqual(result['config'],'final.json');run.assert_called_once_with(['python3','check.py',expected],cwd=project,check=True)
            with patch('verify.subprocess.run',side_effect=subprocess.CalledProcessError(1,['guard'])):
                with self.assertRaises(subprocess.CalledProcessError):gated_suite(project,suite,reviewed_hash=expected)

class ExtensionTests(unittest.TestCase):
    def test_adding_paper_is_discovered_without_a_global_dispatch_edit(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);fixture(root);templates=root/'templates/paper';templates.mkdir(parents=True)
            (templates/'README.md.in').write_text((ROOT/'templates/paper/README.md.in').read_text())
            new=create_paper(root,'New theorem','new-theorem','https://example.org/new')
            self.assertEqual(new.name,'02-new-theorem')
            self.assertEqual(len(papers(root)),2)
            data,_=render(root);self.assertEqual(json.loads(data)['paper_count'],2)
            meta=json.loads((new/'publication.json').read_text())
            self.assertEqual(meta['primary_comparator'],'main')
            self.assertFalse(static_review(new,meta)['static_review_passed'])

    def test_plan_is_read_only_and_keeps_review_and_diagnostic_gates(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder);project,meta=fixture(root)
            meta['directory']='untrusted-metadata-path'
            meta['comparators'] += [
                {'id':'future','availability':'pending_materialization','planned_config':'future.json','scope':'Unmaterialized final scope'},
                {'id':'probe','availability':'diagnostic_only','config':'probe.json','expected_rejection':'missing','scope':'Known missing target'}]
            (project/'publication.json').write_text(json.dumps(meta))
            before=snapshot(project)
            with patch('subprocess.run',side_effect=AssertionError('Unexpected execution')):
                result=plan(root,local=True)
            self.assertFalse(result['execution_started'])
            commands=result['papers'][0]['checks']
            self.assertIn('REVIEWED_SHA256',commands[2]['command'])
            self.assertTrue(commands[3]['diagnostic_only'])
            self.assertIn('--allow-diagnostic',commands[3]['command'])
            self.assertEqual(before,snapshot(project))
            catalog,_=render(root)
            self.assertEqual(json.loads(catalog)['papers'][0]['directory'],'papers/01-example')

if __name__=='__main__':unittest.main()
