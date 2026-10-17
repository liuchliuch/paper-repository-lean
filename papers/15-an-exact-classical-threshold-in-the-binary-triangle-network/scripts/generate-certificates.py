#!/usr/bin/env python3
"""Generate P15 certificate inputs in an otherwise empty staged project.

Run through the repository preparation dispatcher. This recipe invokes only a
C++ compiler, the resulting exact-arithmetic generators, and a Python emitter.
It never invokes Lean, Lake, Comparator, or a proof checker. The dispatcher
compares every declared output with generated-artifacts.json before installing
any output in the paper directory.
"""

from pathlib import Path
import os
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SOURCES = Path("scripts/certificate-sources")
DATA = Path("Paper15/CertificateData")
TOOLS = Path("work/certificate-tools")


def run(command):
    print("Running:", repr(command), flush=True)
    subprocess.run(command, cwd=ROOT, check=True)


def main():
    if Path.cwd().resolve() != ROOT:
        raise SystemExit("Run this recipe from the staged project root.")
    if sys.byteorder != "little":
        raise SystemExit("The frozen certificate recipe requires a little-endian host.")
    output_paths = [DATA / name for name in
                    ("forest.bin", "representatives.bin", "neighbours.bin")]
    output_paths += [DATA / f"Batch{i:04d}.lean" for i in range(533)]
    output_paths += [DATA / f"Orbit{i:04d}.lean" for i in range(512)]
    if any((ROOT / path).exists() for path in output_paths):
        raise SystemExit("Declared outputs already exist; use a fresh preparation staging directory.")

    # CXX is one executable, never a shell command. No ambient CXXFLAGS are used.
    compiler = os.environ.get("CXX", "c++")
    if shutil.which(compiler) is None:
        raise SystemExit("Set CXX to a C++17 compiler supporting __int128_t.")
    flags = ["-O3", "-std=c++17"]
    include = os.environ.get("BOOST_INCLUDEDIR")
    if include:
        include_path = Path(include).resolve()
        if not (include_path / "boost/multiprecision/cpp_int.hpp").is_file():
            raise SystemExit("BOOST_INCLUDEDIR must contain boost/multiprecision/cpp_int.hpp.")
        flags += ["-I", str(include_path)]

    for folder in [DATA, TOOLS, Path("work/certificates")]:
        (ROOT / folder).mkdir(parents=True, exist_ok=True)
    for name in ["triangle-certificates", "orbit-neighbours"]:
        run([compiler, *flags, str(SOURCES / f"{name}.cpp"),
             "-o", str(TOOLS / name)])
    run([str(TOOLS / "triangle-certificates")])
    for name in ["forest.bin", "representatives.bin"]:
        shutil.copyfile(ROOT / "work/certificates" / name, ROOT / DATA / name)
    run([str(TOOLS / "orbit-neighbours")])
    run([sys.executable, str(SOURCES / "emit-modules.py")])
    print("Generation completed. Exact output hashes must pass the dispatcher gate.")


if __name__ == "__main__":
    main()
