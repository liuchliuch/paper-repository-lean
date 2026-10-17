#!/usr/bin/env python3
"""One explicit paper, one verification stage. The default is static review."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

from common import (ROOT, ALLOWED_AXIOMS, classify_comparator, digest, imports,
                    inside, module_path, package_dir, papers, read_json,
                    select_paper, snapshot, source_files, strip_comments,
                    tool_profile, verify_tool_pins, real_lake, dependency_pins, schema_errors)
from generated import manifest as generated_manifest, output_status, require_ready

def static_review(project: Path, meta: dict) -> dict:
    errors = schema_errors(meta, read_json(ROOT/'schemas/publication.schema.json'))
    warnings = []
    if errors:
        return {'paper_id':meta.get('paper_id'), 'static_review_passed':False,
                'errors':errors, 'warnings':[], 'fresh_build':'not_run',
                'official_comparator':'not_run', 'kernel_replay':'not_run'}
    for field in ('paper_id', 'title', 'source_url', 'lean_toolchain',
                  'production_roots', 'build_targets', 'primary_comparator',
                  'comparators', 'main_results', 'external_dependencies'):
        if field not in meta: errors.append('Missing metadata field: '+field)
    for name in ('README.md', 'EXTERNAL_DEPENDENCIES.md', 'lean-toolchain', 'scripts/lake-local'):
        if not (project/name).is_file(): errors.append('Missing required file: '+name)
    for field in ('production_roots', 'build_targets', 'main_results'):
        if not isinstance(meta.get(field), list) or not meta[field]:
            errors.append('Metadata requires a nonempty array: '+field)
    if not isinstance(meta.get('comparators'), list):
        errors.append('comparators must be an array')
    else:
        ids = [suite.get('id') for suite in meta['comparators']]
        if len(ids) != len(set(ids)) or any(not isinstance(value, str) or not value for value in ids):
            errors.append('Comparator suite IDs must be nonempty and unique')
        if meta.get('primary_comparator') not in ids:
            errors.append('Primary Comparator configuration is missing')
    if (project/'lean-toolchain').is_file():
        if (project/'lean-toolchain').read_text().strip() != meta.get('lean_toolchain'):
            errors.append('Metadata/toolchain mismatch')
    if not any((project/name).is_file() for name in ('lakefile.toml', 'lakefile.lean')):
        errors.append('Missing Lake project configuration')
    if not (project/'lake-manifest.json').is_file():
        errors.append('Missing pinned Lake manifest')
    else:
        for dependency in read_json(project/'lake-manifest.json').get('packages', []):
            if dependency.get('type') == 'git' and not re.fullmatch(r'[0-9a-f]{40}', dependency.get('rev', '')):
                errors.append('Dependency is not pinned to a commit: '+dependency.get('name', '?'))
            if dependency.get('type') == 'path':
                dep_path = dependency.get('dir', dependency.get('path', ''))
                if Path(dep_path).is_absolute(): errors.append('Absolute Lake dependency: '+dep_path)
    lean_files = {path.relative_to(project).with_suffix('').as_posix().replace('/', '.'): path
                  for path in source_files(project) if path.suffix == '.lean'}
    generated, generated_modules, generated_status = None, {}, None
    try:
        generated = generated_manifest(project)
        if meta.get('generated_artifacts') and generated is None:
            errors.append('Metadata declares generated artifacts but their manifest is missing')
        if generated:
            generated_modules = {entry['module']:entry for entry in generated['outputs'] if entry.get('module')}
            if len(generated_modules)!=sum(bool(entry.get('module')) for entry in generated['outputs']):
                errors.append('Duplicate generated module declaration')
            generated_status = output_status(project,generated)
            if generated_status['mismatched']:
                errors.append('Generated outputs differ from frozen hashes: '+', '.join(generated_status['mismatched'][:5]))
    except (OSError,ValueError,KeyError,TypeError) as error:
        errors.append('Invalid generated artifact recipe: '+str(error))
    all_modules = set(lean_files) | set(generated_modules)
    module_imports = {module:imports(path.read_text()) for module,path in lean_files.items()}
    module_imports.update({module:entry.get('imports',[]) for module,entry in generated_modules.items() if module not in lean_files})
    declared_targets = set()
    if (project/'lakefile.toml').is_file():
        try:
            lake = tomllib.loads((project/'lakefile.toml').read_text())
            for kind in ('lean_lib','lean_exe'):
                declared_targets.update(item['name'] for item in lake.get(kind,[]) if isinstance(item,dict) and isinstance(item.get('name'),str))
        except tomllib.TOMLDecodeError as error:
            errors.append('Invalid Lake TOML: '+str(error))
    elif (project/'lakefile.lean').is_file():
        declared_targets.update(re.findall(r'\b(?:lean_lib|lean_exe)\s+([A-Za-z_][A-Za-z0-9_]*)',strip_comments((project/'lakefile.lean').read_text())))
    for target in meta['build_targets']:
        if target not in all_modules and target not in declared_targets:
            errors.append('Build target is not a retained module or declared library/executable: '+target)
    local_prefixes = {name.split('.')[0] for name in all_modules}
    for module, dependencies in module_imports.items():
        for dependency in dependencies:
            if dependency.split('.')[0] in local_prefixes and dependency not in all_modules:
                errors.append(f'{module} imports missing local module {dependency}')
    roots = meta.get('production_roots', [])
    if not roots: errors.append('No production entry roots')
    pending, closure = list(roots), set()
    while pending:
        module = pending.pop()
        if module in closure: continue
        closure.add(module)
        if module not in all_modules:
            errors.append('Missing production entry/module: '+module); continue
        pending.extend(name for name in module_imports[module] if name in all_modules)
    holes = []
    for module in sorted(closure):
        if module not in lean_files: continue
        for match in re.finditer(r'\b(sorry|admit|axiom)\b', strip_comments(lean_files[module].read_text())):
            holes.append({'module':module, 'token':match.group(),
                          'line':lean_files[module].read_text()[:match.start()].count('\n')+1})
    authorized = meta.get('authorized_external_holes', [])
    for hole in holes:
        matches = [item for item in authorized if all(item.get(key) == value for key, value in hole.items())
                   and item.get('reference') and item.get('reason')]
        if not matches: errors.append('Unregistered production proof/axiom marker: '+str(hole))
    suites = []
    for suite in meta.get('comparators', []):
        availability = suite.get('availability', 'available')
        expected = suite.get('expected_rejection')
        if expected not in (None, 'type', 'axiom') and not (expected == 'missing' and availability == 'diagnostic_only'):
            errors.append('Unsupported expected_rejection in '+str(suite.get('id')))
        if suite.get('available') is False or availability == 'pending_materialization':
            if not suite.get('preparation'):
                errors.append('Pending suite lacks preparation instructions: '+suite.get('id', '?'))
            suites.append({'id':suite.get('id'), 'availability':availability, 'targets':None})
            continue
        try:
            config_path = inside(project, suite['config'])
            config = read_json(config_path)
            for key, kind in [('challenge_module',str),('solution_module',str),('theorem_names',list),('permitted_axioms',list),('enable_nanoda',bool)]:
                if key not in config or not isinstance(config[key], kind):
                    errors.append(f'Comparator {suite["id"]} is missing/invalid: {key}')
            if config.get('challenge_module') == config.get('solution_module'):
                errors.append('Comparator endpoints must be distinct: '+suite['id'])
            names = config.get('theorem_names', [])
            if not names or not all(isinstance(name,str) and name for name in names) or len(names) != len(set(names)):
                errors.append('Empty/duplicate Comparator theorem list: '+suite['id'])
            if not set(config.get('permitted_axioms', [])) <= ALLOWED_AXIOMS:
                errors.append('Unreviewed Comparator axiom allowlist: '+suite['id'])
            for key in ('challenge_module', 'solution_module'):
                if not module_path(project, config[key]).is_file() and config[key] not in generated_modules:
                    errors.append('Missing Comparator module '+config[key]+' in '+suite['id'])
            if config.get('definition_names'):
                warnings.append('Definition-hole suite requires separate semantic review: '+suite['id'])
            suites.append({'id':suite['id'], 'availability':availability, 'targets':len(names),
                           'config_sha256':digest(config_path), 'scope':suite.get('scope')})
        except (OSError, ValueError, KeyError, TypeError) as error:
            errors.append(f'Invalid Comparator suite {suite.get("id")}: {error}')
    if not suites: warnings.append('No fixed Comparator suite yet; this paper cannot claim Comparator validation.')
    for path in source_files(project):
        if path.suffix in {'.lean', '.py', '.sh', '.md', '.json', '.toml', '.yml', '.yaml', '.in', '.cpp', '.hpp'}:
            text = path.read_text(encoding='utf-8')
            relative = path.relative_to(project).as_posix()
            if re.search(r'[\u3400-\u9fff]', text):
                errors.append('Non-English CJK text in release file: '+relative)
            portable_text = re.sub(r'https?://[^\s<>\"\']+', '', text)
            if re.search(r'/Users/|/home/[^/]+/|/root/', portable_text):
                errors.append('Host-specific path in release file: '+relative)
    return {'paper_id':meta.get('paper_id'), 'static_review_passed':not errors,
            'errors':errors, 'warnings':warnings, 'production_modules_in_entry_closure':len(closure),
            'retained_lean_modules':len(lean_files), 'production_proof_markers':holes,
            'generated_artifacts':generated_status,
            'unmaterialized_production_modules':sorted(module for module in closure if module not in lean_files),
            'generated_source_scan':'deferred_until_materialization' if any(module not in lean_files for module in closure) else 'complete_for_present_sources',
            'comparator_suites':suites,
            'fresh_build':'not_run', 'official_comparator':'not_run', 'kernel_replay':'not_run'}

def gated_suite(project: Path, suite: dict, allow_diagnostic=False, reviewed_hash=None) -> dict:
    gated = bool(suite.get('reviewed_manifest') or suite.get('requires_preparation') or
                 suite.get('available') is False or suite.get('availability') == 'pending_materialization')
    if suite.get('availability') == 'diagnostic_only' and not allow_diagnostic:
        raise ValueError('This is an intentionally incomplete diagnostic probe; use --allow-diagnostic explicitly.')
    if gated:
        if not reviewed_hash or not re.fullmatch(r'[0-9a-fA-F]{64}', reviewed_hash):
            raise ValueError('Prepared suites require an explicit --reviewed-manifest-sha256 after independent review')
        if not suite.get('reviewed_manifest') or not suite.get('review_command'):
            raise ValueError('Pending suite has no complete portable review gate: '+str(suite.get('preparation')))
        path = inside(project, suite['reviewed_manifest'])
        if not path.is_file() or digest(path) != reviewed_hash.lower():
            raise ValueError('Required review record does not match the independently reviewed SHA-256')
        command = suite['review_command']
        if not isinstance(command, list) or not all(isinstance(x, str) for x in command):
            raise ValueError('review_command must be a literal argument array')
        command = [x.replace('{reviewed_sha256}', reviewed_hash) for x in command]
        subprocess.run(command, cwd=project, check=True)
        effective = dict(suite)
        effective['config'] = suite.get('config', suite.get('planned_config'))
        if not effective['config'] or not inside(project, effective['config']).is_file():
            raise ValueError('Reviewed contract has not been materialized')
        return effective
    return dict(suite)

def execute(project: Path, meta: dict, args) -> int:
    require_ready(project)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    log_dir = ROOT/'.artifacts'/meta['paper_id']/stamp
    log_dir.mkdir(parents=True, exist_ok=False)
    before = snapshot(project)
    dependencies_before = dependency_pins(project, require_present=args.check == 'comparator')
    env = dict(os.environ)
    env['PINKFOLD_LAKE'] = real_lake(env)
    tools = None
    suite = None
    if args.check == 'build':
        command = ['./scripts/lake-local', 'build', *meta['build_targets']]
    else:
        selected_suite=args.suite or meta['primary_comparator']
        candidates = [suite for suite in meta['comparators'] if suite['id'] == selected_suite]
        if len(candidates) != 1:
            raise ValueError('Choose one --suite from: '+', '.join(suite['id'] for suite in meta['comparators']))
        suite = gated_suite(project, candidates[0], args.allow_diagnostic, args.reviewed_manifest_sha256)
        config_path = inside(project, suite['config'])
        config = read_json(config_path)
        if not config.get('theorem_names'):
            raise ValueError('Comparator has no fixed theorem targets')
        if not set(config.get('permitted_axioms', [])) <= ALLOWED_AXIOMS:
            raise ValueError('Comparator axiom allowlist is not permitted')
        profile, settings = tool_profile(meta['lean_toolchain'])
        tools = verify_tool_pins(profile, settings)
        comparator = package_dir(profile, 'Comparator')/'.lake/build/bin/comparator'
        exporter = package_dir(profile, 'lean4export')/'.lake/build/bin'
        if not comparator.is_file() or not (exporter/'lean4export').is_file():
            raise ValueError('Pinned official tools are not built; run setup_comparator.py explicitly.')
        paths = [str(ROOT/'scripts/comparator-bin'), str(exporter)]
        if args.local:
            paths.insert(0, str(ROOT/'scripts/local-bin'))
            print('MODE: explicit local execution; no OS sandbox.', flush=True)
        elif not shutil.which('landrun'):
            raise ValueError('landrun was not found. For trusted local sources only, explicitly add --local.')
        env['PATH'] = os.pathsep.join(paths+[env.get('PATH', '')])
        command = ['./scripts/lake-local', 'env', str(comparator), str(config_path)]
    log = log_dir/'run.log'
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
    postcheck_errors = []
    after, dependencies_after = None, None
    try:
        after = snapshot(project)
    except (OSError, ValueError) as error:
        postcheck_errors.append('Source snapshot failed: '+str(error))
    stable = before == after
    try:
        dependencies_after = dependency_pins(project, require_present=True)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        postcheck_errors.append('Dependency observation failed: '+str(error))
        stable = False
    # First-time builds may fetch missing pinned dependencies, but existing sources may not change.
    for name, observation in dependencies_before.items():
        if observation['status'] != 'not_downloaded' and (dependencies_after or {}).get(name) != observation:
            stable = False
    output = log.read_text(errors='replace')
    passed = result.returncode == 0 if args.check == 'build' else classify_comparator(
        result.returncode, output, config['theorem_names'], suite.get('expected_rejection'))
    diagnostic = suite is not None and suite.get('availability') == 'diagnostic_only'
    if tools is not None:
        try:
            stable = verify_tool_pins(profile, settings) == tools and stable
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            postcheck_errors.append('Tool observation failed: '+str(error))
            stable = False
    record = {'paper_id':meta['paper_id'], 'stage':args.check, 'command':command,
              'workdir':str(project), 'exit_code':result.returncode, 'sources_unchanged':stable,
              'stage_passed':passed and stable, 'diagnostic_only':diagnostic,
              'paper_accepted':False, 'source_hashes':before, 'tools':tools,
              'dependency_sources_before':dependencies_before,'dependency_sources_after':dependencies_after,
              'postcheck_errors':postcheck_errors,
              'suite':suite, 'log':str(log), 'mode':'local-build' if args.check == 'build' else 'local-unsandboxed' if args.local else 'official-sandbox',
              'note':'This receipt covers the selected command and fixed statements only.'}
    (log_dir/'result.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({key:record[key] for key in ('paper_id','stage','exit_code','sources_unchanged','stage_passed','diagnostic_only','log')}, indent=2))
    return 0 if passed and stable else 1

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper', help='Paper ID or directory name; omit for static checks of every paper.')
    parser.add_argument('--check', choices=['static', 'build', 'comparator'], default='static')
    parser.add_argument('--suite', help='Exact named Comparator suite from publication.json')
    parser.add_argument('--local', action='store_true', help='Explicit unsandboxed execution of trusted sources only.')
    parser.add_argument('--allow-diagnostic', action='store_true')
    parser.add_argument('--reviewed-manifest-sha256', help='Exact independent review-record digest for a prepared suite')
    args = parser.parse_args()
    if args.check != 'static' and not args.paper:
        parser.error('A non-static stage requires one explicit --paper; no automatic all-paper heavy run.')
    try:
        if args.check == 'static':
            selected = [select_paper(args.paper)] if args.paper else papers()
            if not selected: raise ValueError('No paper metadata found')
            reports = [static_review(project, meta) for project, meta in selected]
            print(json.dumps(reports, indent=2))
            return 0 if all(row['static_review_passed'] for row in reports) else 1
        project, meta = select_paper(args.paper)
        preflight = static_review(project,meta)
        if not preflight['static_review_passed']:
            raise ValueError('Static preflight failed: '+'; '.join(preflight['errors']))
        return execute(project, meta, args)
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f'Error: {error}', file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
