#!/usr/bin/env python3
"""Print a portable manual verification plan. Never downloads or executes tools."""
import argparse
import json
from common import ROOT, digest, papers, select_paper

def plan(root=ROOT, paper=None, local=False):
    selected = [select_paper(paper,root)] if paper is not None else papers(root)
    result = []
    for path, meta in selected:
        base = ['python3','scripts/verify.py','--paper',meta['paper_id']]
        checks = [{'stage':'build','command':base+['--check','build'],
                   'status':'not_run','scope':meta['build_targets']}]
        for suite in meta['comparators']:
            command = base+['--check','comparator','--suite',suite['id']]
            if local: command += ['--local']
            gated = bool(suite.get('reviewed_manifest') or suite.get('requires_preparation') or
                         suite.get('available') is False or suite.get('availability') == 'pending_materialization')
            diagnostic = suite.get('availability') == 'diagnostic_only'
            if gated: command += ['--reviewed-manifest-sha256','REVIEWED_SHA256']
            if diagnostic: command += ['--allow-diagnostic']
            checks.append({'stage':'comparator','suite':suite['id'],'command':command,
                           'status':'not_run','scope':suite['scope'],
                           'independent_review_required':gated,'diagnostic_only':diagnostic,
                           'expected_rejection':suite.get('expected_rejection')})
        result.append({'paper_id':meta['paper_id'],'paper_directory':path.relative_to(root).as_posix(),
                       'command_workdir':'.','lean_toolchain':meta['lean_toolchain'],
                       'metadata_sha256':digest(path/'publication.json'),
                       'generated_input_preparation':{'plan':['python3','scripts/prepare.py','--paper',meta['paper_id']],
                                                       'execute':['python3','scripts/prepare.py','--paper',meta['paper_id'],'--execute'],
                                                       'status':'generation_not_run'} if (path/'generated-artifacts.json').is_file() else None,
                       'manual_preparation':meta.get('preparation',[]),
                       'checks':checks})
    return {'plan_only':True,'execution_started':False,
            'instructions':'Run shared tool setup explicitly first. Commands use the repository root; preparation commands use the named paper directory. Replace REVIEWED_SHA256 only after independent correspondence review. Diagnostic probes never count as proof validation.',
            'papers':result}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper',help='Optional paper ID or directory; default lists all papers.')
    parser.add_argument('--local',action='store_true',help='Show explicit unsandboxed local Comparator commands for trusted sources.')
    args=parser.parse_args()
    print(json.dumps(plan(paper=args.paper,local=args.local),ensure_ascii=False,indent=2))

if __name__=='__main__':main()
