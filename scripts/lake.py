#!/usr/bin/env python3
"""Invoke the user's Lake installation in one explicit project directory."""
import argparse
import os
from pathlib import Path
from common import real_lake
from generated import require_ready

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('arguments', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    project = args.project.resolve()
    if not (project/'lean-toolchain').is_file():
        parser.error('Project has no pinned lean-toolchain')
    arguments = args.arguments
    if arguments[:1] == ['--']: arguments = arguments[1:]
    try:
        # Lake accepts global options before its command (for example -q build).
        if 'build' in arguments:
            require_ready(project)
        executable = real_lake()
    except ValueError as error:
        parser.error(str(error))
    os.chdir(project)
    os.execv(executable, [executable, *arguments])

if __name__ == '__main__':
    main()
