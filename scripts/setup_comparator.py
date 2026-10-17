#!/usr/bin/env python3
"""Build shared pinned official tools only after an explicit --execute."""
import argparse
from pathlib import Path
import subprocess
from common import ROOT, tool_profile, verify_tool_pins, real_lake

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', default='leanprover/lean4:v4.24.0')
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    profile, settings = tool_profile(args.toolchain)
    command = ['lake', 'build', 'comparator', 'lean4export']
    print('Toolchain:', args.toolchain)
    print('Working directory:', profile)
    print('Pinned Comparator:', settings['comparator_revision'])
    print('Command:', ' '.join(command))
    if not args.execute:
        print('PLAN ONLY: no dependency download or tool build started.')
        return
    before = (profile/'lake-manifest.json').read_bytes()
    command[0] = real_lake()
    subprocess.run(command, cwd=profile, check=True)
    if (profile/'lake-manifest.json').read_bytes() != before:
        raise SystemExit('Tool manifest changed during setup; review dependency changes before use.')
    print(verify_tool_pins(profile, settings))
    print('Pinned official tools are built. No paper was verified.')

if __name__ == '__main__':
    main()
