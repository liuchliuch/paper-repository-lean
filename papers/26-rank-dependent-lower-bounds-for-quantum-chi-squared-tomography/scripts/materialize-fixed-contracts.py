#!/usr/bin/env python3
"""Render frozen Comparator text from a literal independent challenge template.

This tool reads only the listed template and line-edit recipes. It does not read
production proofs, infer Lean types, run Lean, or perform mathematical checks.
Edits use one-based source line positions in the named base, preserving UTF-8
bytes and line endings. A dependent recipe may reuse another frozen output.
Every rendered byte sequence must match its immutable expected SHA-256.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def inside(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT) or path == ROOT:
        raise ValueError('Path escapes the project: ' + relative)
    return path

def render(recipe_path: Path) -> None:
    recipe = json.loads(recipe_path.read_text(encoding='utf-8'))
    if recipe.get('schema_version') != 1:
        raise ValueError('Unsupported fixed-text recipe schema')
    template = recipe['template']
    base = inside(template['path']).read_bytes()
    if digest(base) != template['sha256']:
        raise ValueError('Independent challenge template differs from its frozen hash')
    specs = {entry['path']: entry for entry in recipe['outputs']}
    if len(specs) != len(recipe['outputs']):
        raise ValueError('Duplicate recipe output')
    rendered: dict[str, bytes] = {}
    active: set[str] = set()

    def get(relative: str) -> bytes:
        if relative in rendered:
            return rendered[relative]
        if relative in active:
            raise ValueError('Cyclic fixed-text recipe')
        active.add(relative)
        entry = specs[relative]
        if entry.get('from_template') is True:
            source = base
        else:
            source = get(entry['from_output'])
        lines = source.decode('utf-8').splitlines(keepends=True)
        pieces: list[str] = []
        cursor = 0
        for edit in entry.get('edits', []):
            start = edit['start_line'] - 1
            count = edit['delete_lines']
            if not isinstance(start, int) or not isinstance(count, int) or start < cursor or count < 0 or start + count > len(lines):
                raise ValueError('Invalid or overlapping source line edit for ' + relative)
            inserted = edit['insert_lines']
            if not isinstance(inserted, list) or not all(isinstance(line, str) for line in inserted):
                raise ValueError('Line edits must contain literal strings')
            pieces.extend(lines[cursor:start])
            pieces.extend(inserted)
            cursor = start + count
        pieces.extend(lines[cursor:])
        data = ''.join(pieces).encode('utf-8')
        if digest(data) != entry['sha256'] or len(data) != entry['bytes']:
            raise ValueError('Rendered output differs from its frozen bytes: ' + relative)
        active.remove(relative)
        rendered[relative] = data
        return data

    for relative in specs:
        get(relative)
    # Validate every destination before writing any output.
    for relative, data in rendered.items():
        destination = inside(relative)
        if destination.exists() and (not destination.is_file() or destination.read_bytes() != data):
            raise ValueError('Refusing to overwrite changed generated output: ' + relative)
    for relative, data in rendered.items():
        destination = inside(relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    print('Materialized ' + str(len(rendered)) + ' exact frozen Comparator text outputs; no Lean checks performed.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('recipe', help='Project-relative literal fixed-text recipe JSON')
    args = parser.parse_args()
    render(inside(args.recipe))
