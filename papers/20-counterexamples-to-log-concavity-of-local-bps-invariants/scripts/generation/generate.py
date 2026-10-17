#!/usr/bin/env python3
"""Explicit preparation recipe for P20's generated certificate check sources.

Run through ../../scripts/prepare.py --paper 20 --execute. This script performs
large exact Python calculations; it never runs Lean, Lake or Comparator.
The shared dispatcher verifies all declared hashes before installing outputs.
"""
from pathlib import Path
import subprocess
import sys
from render_scaffolds import restore_scaffolds


def main():
    project = Path.cwd()
    (project / "work").mkdir(exist_ok=True)
    (project / "Paper20/Certs").mkdir(parents=True, exist_ok=True)
    vendor = project / "scripts/generation/vendor"
    # Every order is intentional. The root JSON is an intermediate candidate,
    # and is consumed by the row exporter; it is not a proof or an input pin.
    for name in ["gen_hilbert_tree.py", "gen_a_cache_fast36.py",
                 "gen_r_content36_tree.py", "split_r_content_states.py",
                 "test_q36_rows.py", "gen_q36_rows.py"]:
        print("Generating candidates:", name, flush=True)
        subprocess.run([sys.executable, str(vendor / name)], cwd=project, check=True)
    restore_scaffolds(project)
    print("Candidates rendered. Exact output hashes and all Lean checks remain separate.", flush=True)


if __name__ == "__main__":
    main()
