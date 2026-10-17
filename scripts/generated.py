"""Declared reproducible build inputs; absence is not a proof verification pass."""
from pathlib import Path
import re
from common import digest, inside, module_path, read_json, imports

MANIFEST = 'generated-artifacts.json'

def manifest(project: Path):
    path = project/MANIFEST
    if not path.is_file():
        return None
    data = read_json(path)
    if data.get('schema_version') != 1:
        raise ValueError('Unsupported generated-artifacts schema')
    for section in ('inputs','outputs'):
        entries = data.get(section)
        if not isinstance(entries,list) or not entries:
            raise ValueError('Generated artifact manifest requires nonempty '+section)
        names = set()
        for entry in entries:
            name = entry.get('path')
            path = inside(project,name)
            if not name or str(Path(name))!=name or '..' in Path(name).parts or '\\' in name:
                raise ValueError('Generated paths must be normalized project-relative names: '+str(name))
            if not name or name in names or any(part in {'.git','.lake','.artifacts','__pycache__'} for part in Path(name).parts):
                raise ValueError('Duplicate/reserved generated artifact path: '+str(name))
            names.add(name)
            if not re.fullmatch(r'[0-9a-f]{64}',entry.get('sha256','')):
                raise ValueError('Generated artifact requires an exact SHA-256: '+name)
            if section == 'inputs':
                if not path.is_file() or digest(path) != entry['sha256']:
                    raise ValueError('Generator input differs from its frozen hash: '+name)
            else:
                if not isinstance(entry.get('bytes'),int) or entry['bytes'] < 0:
                    raise ValueError('Generated output requires a nonnegative byte count: '+name)
                if path.suffix=='.lean':
                    if not isinstance(entry.get('module'),str) or 'imports' not in entry:
                        raise ValueError('Every generated Lean output requires its module and captured imports: '+name)
                    if module_path(project,entry['module']) != path:
                        raise ValueError('Generated module/path mismatch: '+name)
                    if path.is_file() and imports(path.read_text()) != entry['imports']:
                        raise ValueError('Captured imports differ from present generated source: '+name)
                elif entry.get('module') is not None:
                    raise ValueError('Non-Lean generated outputs must not declare a Lean module: '+name)
                if not isinstance(entry.get('imports',[]),list) or not all(isinstance(x,str) for x in entry.get('imports',[])):
                    raise ValueError('Generated module imports must be a string list: '+name)
    if {x['path'] for x in data['inputs']} & {x['path'] for x in data['outputs']}:
        raise ValueError('Generator source inputs must not also be generated outputs')
    if not isinstance(data.get('commands'),list) or not data['commands']:
        raise ValueError('Missing explicit generation commands')
    for command in data['commands']:
        if not isinstance(command,list) or not command or not all(isinstance(x,str) and x for x in command):
            raise ValueError('Generation commands must be nonempty literal argument arrays')
    return data

def output_status(project: Path, data: dict) -> dict:
    missing, mismatched = [], []
    for entry in data['outputs']:
        path = inside(project,entry['path'])
        if not path.is_file():
            missing.append(entry['path'])
        elif path.stat().st_size != entry['bytes'] or digest(path) != entry['sha256']:
            mismatched.append(entry['path'])
    return {'ready':not missing and not mismatched,'output_count':len(data['outputs']),
            'missing':missing,'mismatched':mismatched,
            'expected_generated_bytes':sum(entry['bytes'] for entry in data['outputs'])}

def require_ready(project: Path):
    data = manifest(project)
    if data is None:
        return
    status = output_status(project,data)
    if not status['ready']:
        paper = read_json(project/'publication.json')['paper_id']
        raise ValueError(f'Generated inputs are not ready ({len(status["missing"])} missing, {len(status["mismatched"])} changed). Run python3 ../../scripts/prepare.py --paper {paper} --execute from this paper directory. Preparation can be expensive and must be requested explicitly.')
