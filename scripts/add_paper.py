#!/usr/bin/env python3
"""Add an unverified paper scaffold with the same portable project structure."""
import argparse
import json
import re
from pathlib import Path
from common import ROOT, papers

def create_paper(root: Path, title: str, slug: str, source_url: str,
                 paper_id=None, namespace=None, toolchain='leanprover/lean4:v4.24.0') -> Path:
    existing = papers(root)
    if not title.strip() or any(character in title for character in ('\n','\r','/-','-/')):
        raise ValueError('title must be nonempty single-line text without Lean comment delimiters')
    if not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', slug):
        raise ValueError('slug must contain lowercase words separated by hyphens')
    paper_id = str(paper_id).zfill(2) if paper_id is not None else str(max([int(meta['paper_id']) for _,meta in existing], default=0)+1).zfill(2)
    if not re.fullmatch(r'[0-9]{2,}', paper_id): raise ValueError('paper_id must be numeric')
    if any(meta['paper_id']==paper_id for _,meta in existing): raise ValueError('Paper ID already exists')
    namespace = namespace or 'Paper'+paper_id
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*',namespace): raise ValueError('namespace must be one capitalized Lean identifier')
    if not source_url.startswith(('https://','http://')): raise ValueError('source_url must be an HTTP(S) URL')
    bases = [(path,meta) for path,meta in existing if meta['lean_toolchain']==toolchain]
    if not bases: raise ValueError('No existing pinned dependency template for this toolchain; add a reviewed toolchain profile first')
    base= bases[0][0]
    manifest=json.loads((base/'lake-manifest.json').read_text())
    mathlib=next(dep for dep in manifest['packages'] if dep['name'].lower()=='mathlib')
    path = root/'papers'/(paper_id+'-'+slug)
    path.mkdir(parents=True,exist_ok=False)
    (path/'scripts').mkdir()
    (path/'Verification').mkdir()
    (path/'lean-toolchain').write_text(toolchain+'\n')
    manifest['name']=namespace
    (path/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (path/'lakefile.toml').write_text(f'name = "{namespace}"\nversion = "0.1.0"\ndefaultTargets = ["{namespace}"]\n\n[[require]]\nname = "mathlib"\ngit = "{mathlib["url"]}"\nrev = "{mathlib["rev"]}"\n\n[[lean_lib]]\nname = "{namespace}"\n\n[[lean_lib]]\nname = "Verification"\n\n')
    (path/(namespace+'.lean')).write_text(f'/-! Production entry for {title}. Add actual proofs before declaring results. -/\nimport Mathlib\n\nnamespace {namespace}\n\nend {namespace}\n')
    shim=(base/'scripts/lake-local').read_text()
    (path/'scripts/lake-local').write_text(shim)
    (path/'scripts/lake-local').chmod(0o755)
    meta={'paper_id':paper_id,'title':title,'source_url':source_url,'lean_toolchain':toolchain,
          'production_roots':[namespace],'build_targets':[namespace],'primary_comparator':'main',
          'comparators':[],'main_results':[],'preparation':[],
          'external_dependencies':'EXTERNAL_DEPENDENCIES.md'}
    (path/'publication.json').write_text(json.dumps(meta,indent=2)+'\n')
    template=(root/'templates/paper/README.md.in').read_text()
    (path/'README.md').write_text(template.replace('{{TITLE}}',title).replace('{{ID}}',paper_id).replace('{{NAMESPACE}}',namespace).replace('{{SOURCE_URL}}',source_url))
    (path/'EXTERNAL_DEPENDENCIES.md').write_text('# External dependencies\n\nNo paper-specific dependency review has been completed. Register each external theorem, its precise hypotheses and quantifiers, source, use sites and missing formalization before claiming any result. General Mathlib imports are pinned by lake-manifest.json.\n')
    return path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--title',required=True)
    parser.add_argument('--slug',required=True)
    parser.add_argument('--source-url',required=True)
    parser.add_argument('--id',dest='paper_id')
    parser.add_argument('--namespace')
    parser.add_argument('--toolchain',default='leanprover/lean4:v4.24.0')
    args=parser.parse_args()
    try: path=create_paper(ROOT,**vars(args))
    except (OSError,ValueError,KeyError,StopIteration) as error: parser.error(str(error))
    print('Created paper project:',path)
    print('Fill the production sources, main_results and fixed Comparator suites, then run static verification and regenerate the catalog.')

if __name__=='__main__': main()
