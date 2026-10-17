"""Tiny generated-input fixtures; no scientific generator or Lean execution."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from generated import manifest, require_ready
from prepare import prepare
from verify import static_review
from test_tooling import fixture
from lake import main as lake_main

def generation_fixture(root, wrong_output=False):
    project,meta=fixture(root)
    expected='namespace B\ntheorem result : True := True.intro\nend B\n'
    emitted='wrong bytes\n' if wrong_output else expected
    script=project/'emit.py';script.write_text('from pathlib import Path\nPath("B.lean").write_text('+repr(emitted)+')\n')
    ledger={'schema_version':1,'generation_status':'not_run',
            'inputs':[{'path':'emit.py','sha256':hashlib.sha256(script.read_bytes()).hexdigest()}],
            'outputs':[{'path':'B.lean','sha256':hashlib.sha256(expected.encode()).hexdigest(),'bytes':len(expected.encode()),'module':'B','imports':[]}],
            'commands':[[sys.executable,'emit.py']]}
    (project/'generated-artifacts.json').write_text(json.dumps(ledger))
    (project/'A.lean').write_text('import B\n'+(project/'A.lean').read_text())
    return project,meta,ledger,expected

class PreparationTests(unittest.TestCase):
    def test_lake_global_options_cannot_bypass_preparation(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,_=generation_fixture(Path(folder))
            for arguments in [['build'],['-q','build']]:
                with patch('sys.argv',['lake.py','--project',str(project),'--',*arguments]), patch('lake.os.execv') as child:
                    with self.assertRaises(SystemExit):lake_main()
                    child.assert_not_called()
    def test_plan_does_not_run_a_command(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,_=generation_fixture(Path(folder))
            with patch('prepare.subprocess.run',side_effect=AssertionError('Unexpected execution')):
                result=prepare(project)
            self.assertFalse(result['execution_started'])
            self.assertEqual(result['outputs']['missing'],['B.lean'])

    def test_missing_registered_source_is_declared_and_build_is_blocked(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta,_,_=generation_fixture(Path(folder))
            result=static_review(project,meta)
            self.assertTrue(result['static_review_passed'],result['errors'])
            self.assertEqual(result['unmaterialized_production_modules'],['B'])
            self.assertEqual(result['generated_source_scan'],'deferred_until_materialization')
            with self.assertRaises(ValueError):require_ready(project)

    def test_exact_outputs_are_installed_and_later_reused(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,expected=generation_fixture(Path(folder))
            result=prepare(project,execute=True)
            self.assertEqual(result['generation_validation'],'all_outputs_match_frozen_hashes')
            self.assertEqual((project/'B.lean').read_text(),expected)
            require_ready(project)
            with patch('prepare.subprocess.run',side_effect=AssertionError('Unexpected regeneration')):
                self.assertEqual(prepare(project,execute=True)['generation_validation'],'existing_outputs_match_frozen_hashes')

    def test_mismatch_never_installs_and_preserves_failure_receipt(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,_=generation_fixture(Path(folder),wrong_output=True)
            with self.assertRaises(ValueError):prepare(project,execute=True)
            self.assertFalse((project/'B.lean').exists())
            receipts=list((project/'.lake/generation').glob('*/result.json'))
            self.assertEqual(len(receipts),1)
            self.assertEqual(json.loads(receipts[0].read_text())['generation_validation'],'failed')

    def test_changed_inputs_and_changed_outputs_are_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,_=generation_fixture(Path(folder))
            (project/'B.lean').write_text('local edits\n')
            with self.assertRaises(ValueError):prepare(project,execute=True)
            self.assertEqual((project/'B.lean').read_text(),'local edits\n')
            (project/'emit.py').write_text('changed\n')
            with self.assertRaises(ValueError):manifest(project)

    def test_unregistered_missing_import_still_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta,_,_=generation_fixture(Path(folder))
            (project/'A.lean').write_text('import A.Missing\n'+(project/'A.lean').read_text())
            self.assertFalse(static_review(project,meta)['static_review_passed'])

    def test_lean_output_cannot_omit_its_module_or_import_inventory(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta,ledger,_=generation_fixture(Path(folder))
            for key in ['module','imports']:
                invalid=json.loads(json.dumps(ledger));del invalid['outputs'][0][key]
                (project/'generated-artifacts.json').write_text(json.dumps(invalid))
                self.assertFalse(static_review(project,meta)['static_review_passed'])

    def test_present_output_import_inventory_must_match(self):
        with tempfile.TemporaryDirectory() as folder:
            project,meta,ledger,expected=generation_fixture(Path(folder))
            (project/'B.lean').write_text(expected)
            ledger['outputs'][0]['imports']=['Mathlib']
            (project/'generated-artifacts.json').write_text(json.dumps(ledger))
            self.assertFalse(static_review(project,meta)['static_review_passed'])

    def test_copy_corruption_cannot_install_or_return_success(self):
        import shutil
        with tempfile.TemporaryDirectory() as folder:
            project,_,_,_=generation_fixture(Path(folder))
            original=shutil.copyfile
            def corrupted(source,destination,*args,**kwargs):
                result=original(source,destination,*args,**kwargs)
                if str(destination).endswith('.preparing'):Path(destination).write_text('corrupted\n')
                return result
            with patch('prepare.shutil.copyfile',side_effect=corrupted):
                with self.assertRaises(ValueError):prepare(project,execute=True)
            self.assertFalse((project/'B.lean').exists())
            self.assertFalse((project/'B.lean.preparing').exists())

if __name__=='__main__':unittest.main()
