#!/usr/bin/env python3
"""Explicit P23 exporter recipe using a pinned compact original-coordinate witness.

Run through ../../scripts/prepare.py --paper 23 --execute. This expands exact
integer/mod-six candidates and never runs the costly group-ring constructor,
Lean, Lake or Comparator. The dispatcher hash-checks every output before install.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys
from render_scaffolds import restore_scaffolds


def main():
    project = Path.cwd()
    work = project / "work"
    work.mkdir(exist_ok=True)
    (project / "Paper23").mkdir(exist_ok=True)
    vendor = project / "scripts/generation/vendor"
    source = "generation-inputs/certificate.json"
    def run(name, *arguments):
        print("Exporting candidates:", name, flush=True)
        subprocess.run([sys.executable, str(vendor / name), "--source", source, *arguments],
                       cwd=project, check=True)
    run("export_lean_certificate.py", "--chunk-size", "64")
    run("export_lean_cycle.py", "--output-dir", "work/cycle", "--chunk-size", "64")
    target = project / "Paper23/CertificateCycle"
    target.mkdir(exist_ok=True)
    for candidate in sorted((work / "cycle").glob("*.lean")):
        if candidate.name != "CertificateCycle.lean":
            shutil.copyfile(candidate, target / candidate.name)
    run("export_lean_cocycle.py", "--output-dir", "work/cocycle",
        "--declarations-per-module", "16", "--bucket-from-level", "8")
    target = project / "Paper23/CertificateCocycle"
    target.mkdir(exist_ok=True)
    for candidate in sorted((work / "cocycle").glob("*.lean")):
        if candidate.name != "CertificateCocycle.lean":
            shutil.copyfile(candidate, target / candidate.name)
    # Preserve exactly the historical flat first three levels and bucket tail.
    # The stage switch reads the source/hash/count summary made by the first pass.
    run("export_lean_bounding.py", "--chunk-size", "64",
        "--leaves-per-block", "16", "--nodes-per-block", "16")
    run("export_lean_bounding.py", "--chunk-size", "64",
        "--leaves-per-block", "16", "--nodes-per-block", "16", "--stage-bucket-tail")
    stage = work / "bounding-bucket-tail"
    modules = json.loads((stage / "files.json").read_text())
    for module in modules:
        relative = Path(module.replace(".", "/") + ".lean")
        # The reviewed generic root remains ordinary source in the publication.
        if module != "Paper23.Bounding":
            destination = project / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(stage / relative, destination)
    restore_scaffolds(project)
    print("Candidates rendered. Exact output hashes and all Lean checks remain separate.", flush=True)


if __name__ == "__main__":
    main()
