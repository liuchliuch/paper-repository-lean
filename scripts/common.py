"""Portable repository discovery, metadata and verification primitives."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IGNORED = {".git", ".lake", ".artifacts", "__pycache__"}

def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def real_lake(environment=None, root: Path = ROOT) -> str:
    """Resolve Lake without ever selecting our Comparator forwarding shim."""
    environment = os.environ if environment is None else environment
    excluded = {(root/'scripts/comparator-bin/lake').resolve(),
                (root/'scripts/lake.py').resolve()}
    excluded.update(path.resolve() for path in (root/'papers').glob('*/scripts/lake-local'))
    override = environment.get('PINKFOLD_LAKE')
    if override:
        candidate = Path(override)
        if not candidate.is_absolute():
            raise ValueError('PINKFOLD_LAKE must be an absolute executable path')
        if not candidate.is_file() or candidate.resolve() in excluded or not os.access(candidate, os.X_OK):
            raise ValueError('PINKFOLD_LAKE is missing, nonexecutable, or points to an adapter')
        return str(candidate)
    for directory in environment.get('PATH', '').split(os.pathsep):
        candidate = Path(directory or '.')/'lake'
        if candidate.is_file() and os.access(candidate, os.X_OK) and candidate.resolve() not in excluded:
            # Preserve elan's `lake` symlink name; do not exec its resolved `elan` path.
            return str(candidate.absolute())
    raise ValueError('Lake was not found outside the repository adapters; install elan first')

def inside(root: Path, relative: str) -> Path:
    if not isinstance(relative, str) or Path(relative).is_absolute():
        raise ValueError(f'Expected a project-relative path: {relative}')
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes its project: {relative}")
    return path

def schema_errors(value, schema: dict, location='$') -> list[str]:
    """Validate the JSON Schema vocabulary used by publication.schema.json.

    This small dependency-free subset keeps the checked metadata contract in one file.
    URI format is an annotation, as in JSON Schema's default format behavior.
    """
    errors = []
    types = {'object':dict, 'array':list, 'string':str, 'boolean':bool,
             'integer':int, 'number':(int,float), 'null':type(None)}
    kind = schema.get('type')
    if kind and (not isinstance(value, types[kind]) or kind in {'integer','number'} and isinstance(value,bool)):
        return [location+' must be '+kind]
    if 'enum' in schema and value not in schema['enum']:
        errors.append(location+' is not an allowed value')
    if 'const' in schema and value != schema['const']:
        errors.append(location+' must equal '+str(schema['const']))
    if isinstance(value,dict):
        for name in schema.get('required',[]):
            if name not in value: errors.append(location+' is missing '+name)
        for name, item in schema.get('properties',{}).items():
            if name in value: errors.extend(schema_errors(value[name],item,location+'.'+name))
    if isinstance(value,list):
        if len(value)<schema.get('minItems',0): errors.append(location+' has too few items')
        if 'items' in schema:
            for index,item in enumerate(value):
                errors.extend(schema_errors(item,schema['items'],f'{location}[{index}]'))
    if isinstance(value,str):
        if len(value)<schema.get('minLength',0): errors.append(location+' is empty')
        if 'pattern' in schema and re.search(schema['pattern'],value) is None:
            errors.append(location+' does not match its required pattern')
    return errors

def papers(root: Path = ROOT) -> list[tuple[Path, dict]]:
    result = []
    for path in sorted((root / "papers").glob("*/publication.json")):
        result.append((path.parent, read_json(path)))
    ids = [meta.get("paper_id") for _, meta in result]
    if any(not isinstance(value, str) or not re.fullmatch(r'[0-9]{2,}', value) for value in ids):
        raise ValueError('paper_id must be a zero-padded numeric string with at least two digits')
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate paper_id in publication metadata")
    return result

def select_paper(value: str, root: Path = ROOT) -> tuple[Path, dict]:
    normalized = value.removeprefix("P").removeprefix("p")
    if normalized.isdigit():
        normalized = normalized.zfill(2)
    matches = [(path, meta) for path, meta in papers(root)
               if normalized in {meta["paper_id"], path.name}]
    if len(matches) != 1:
        raise ValueError(f"Expected one paper matching {value!r}; found {len(matches)}")
    return matches[0]

def source_files(project: Path):
    for base, dirs, files in os.walk(project):
        dirs[:] = sorted(name for name in dirs if name not in IGNORED)
        for name in sorted(files):
            yield Path(base) / name

def snapshot(project: Path) -> dict[str, str]:
    return {path.relative_to(project).as_posix(): digest(path)
            for path in source_files(project)}

def strip_comments(text: str) -> str:
    """Blank Lean comments and literals for lightweight source scans, preserving offsets.

    This is a source hygiene lexer, not Lean's parser or an axiom audit.
    """
    out, pos, length = [], 0, len(text)
    token_pattern = re.compile(r'''(?<![\w'])r(\#*)"|/-|--|"|'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])' ''', re.VERBOSE)
    def blank(fragment):
        return re.sub(r"[^\n]", " ", fragment)
    while pos < length:
        match = token_pattern.search(text, pos)
        if match is None:
            out.append(text[pos:]); break
        index, token = match.start(), match.group()
        out.append(text[pos:index])
        if token.startswith('r'):
            terminator = '"' + match.group(1)
            closing = text.find(terminator, match.end())
            end = length if closing < 0 else closing + len(terminator)
        elif token.startswith("'"):
            end = match.end()
        elif token == '--':
            end = text.find('\n', index)
            if end < 0: end = length
        elif token == '/-':
            depth, end = 1, index + 2
            while depth:
                opening, closing = text.find('/-', end), text.find('-/', end)
                if closing < 0:
                    end = length; break
                if 0 <= opening < closing:
                    depth += 1; end = opening + 2
                else:
                    depth -= 1; end = closing + 2
        else:
            end = index + 1
            while True:
                quote = text.find('"', end)
                if quote < 0:
                    end = length; break
                slash, cursor = 0, quote - 1
                while cursor >= index and text[cursor] == '\\':
                    slash += 1; cursor -= 1
                end = quote + 1
                if slash % 2 == 0: break
        out.append(blank(text[index:end])); pos = end
    return ''.join(out)

def imports(text: str) -> list[str]:
    found = []
    for line in strip_comments(text).splitlines():
        match = re.match(r"\s*(?:public\s+|private\s+|meta\s+)?import\s+(.+)$", line)
        if match:
            found.extend(match.group(1).split())
    return found

def module_path(project: Path, module: str) -> Path:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
        raise ValueError(f"Unsupported Lean module name: {module}")
    return inside(project, module.replace(".", "/") + ".lean")

def tool_profile(toolchain: str, root: Path = ROOT) -> tuple[Path, dict]:
    registry = read_json(root / "tools/comparator/toolchains.json")
    if toolchain not in registry["profiles"]:
        raise ValueError(f"No pinned Comparator profile for {toolchain}")
    profile = registry["profiles"][toolchain]
    return root / "tools/comparator" / profile["directory"], profile

def package_dir(profile: Path, name: str) -> Path:
    matches = [path for path in (profile / ".lake/packages").glob("*")
               if path.name.casefold() == name.casefold()]
    if len(matches) != 1:
        raise ValueError(f"Missing or ambiguous pinned tool package {name}; run setup_comparator.py explicitly")
    return matches[0]

def verify_tool_pins(profile: Path, settings: dict) -> dict:
    expected = {"Comparator": settings["comparator_revision"],
                "lean4export": settings["export_revision"],
                "Lean4Checker": settings["checker_revision"]}
    observations = {}
    for name, revision in expected.items():
        checkout = package_dir(profile, name)
        actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"], text=True)
        if actual != revision or dirty:
            raise ValueError(f"Pinned tool source differs: {name}")
        observations[name] = {"revision": actual, "tracked_sources_clean": True}
    return observations

def dependency_pins(project: Path, require_present=False) -> dict:
    """Read-only source observations, not a rebuild of dependency caches."""
    manifest = read_json(project/'lake-manifest.json')
    directory = inside(project, manifest.get('packagesDir', '.lake/packages'))
    observations = {}
    for entry in manifest.get('packages', []):
        if entry.get('type') != 'git':
            raise ValueError('Only commit-pinned Git dependencies are supported for verified release runs')
        checkout = directory/entry['name']
        if not checkout.exists():
            alternatives = [path for path in directory.glob('*') if path.name.casefold() == entry['name'].casefold()]
            checkout = alternatives[0] if len(alternatives) == 1 else checkout
        if not checkout.exists():
            if require_present: raise ValueError('Dependency checkout is missing: '+entry['name'])
            observations[entry['name']] = {'status':'not_downloaded', 'revision':entry['rev']}
            continue
        revision = subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git','-C',str(checkout),'status','--porcelain','--untracked-files=no'], text=True)
        if revision != entry['rev'] or dirty:
            raise ValueError('Dependency source differs from its committed pin: '+entry['name'])
        observations[entry['name']] = {'status':'pinned_clean', 'revision':revision}
    return observations

def classify_comparator(exit_code: int, output: str, names: list[str], expected=None) -> bool:
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    if not lines: return False
    stages = (sum(line.startswith('Building ') for line in lines) >= 2 and
              sum(line.startswith('Exporting ') for line in lines) >= 2 and
              sum(line.startswith('Build completed successfully') for line in lines) >= 2)
    if not stages: return False
    if expected is None:
        return exit_code == 0 and "Lean default kernel accepts the solution" in output and lines[-1] == "Your solution is okay!"
    if expected == "type":
        return exit_code != 0 and any(lines[-1] == "uncaught exception: Challenge and solution theorem statement do not match: '"+name+"'" for name in names)
    if expected == "axiom":
        return exit_code != 0 and bool(re.fullmatch(r"uncaught exception: Illegal axiom detected: '[^']+'", lines[-1]))
    # A missing declaration is a diagnostic failure, not a verified negative control.
    return False
