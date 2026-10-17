#!/usr/bin/env python3
"""Update the paper index in README.md from the project metadata."""
import argparse
import json
from pathlib import Path
from common import ROOT, papers

def render(root=ROOT):
    entries = []
    for path, meta in papers(root):
        entries.append({**meta, 'directory':path.relative_to(root).as_posix()})
    data = json.dumps({'schema_version':1, 'paper_count':len(entries), 'papers':entries}, ensure_ascii=False, indent=2)+'\n'
    lines = ['| ID | Paper | Formalization |', '|---|---|---|']
    for entry in entries:
        title = entry['title'].replace('|', '/')
        lines.append(f"| {entry['paper_id']} | [{title}]({entry['source_url']}) | [Lean sources]({entry['directory']}/) |")
    return data, '\n'.join(lines)+'\n'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Fail if the README paper index is stale; do not write.')
    args=parser.parse_args()
    _, markdown = render()
    path=ROOT/'README.md'
    before=path.read_text()
    start='<!-- papers:start -->'
    end='<!-- papers:end -->'
    if before.count(start)!=1 or before.count(end)!=1:
        parser.error('README requires one paper-index marker pair')
    prefix, rest=before.split(start)
    _,suffix=rest.split(end)
    text=prefix+start+'\n\n'+markdown+'\n'+end+suffix
    if args.check:
        if before!=text:parser.error('Paper index is stale: run python3 scripts/catalog.py')
    else:path.write_text(text)
    print('README paper index checked.' if args.check else 'README paper index updated.')

if __name__=='__main__': main()
