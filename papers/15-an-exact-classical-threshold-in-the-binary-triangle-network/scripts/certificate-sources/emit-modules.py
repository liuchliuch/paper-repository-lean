#!/usr/bin/env python3
"""Emit the frozen P15 chunk modules without running a proof checker.

The gap-batch algorithm is preserved from the original
work/generate_certificate_batches.py. Orbit batches 0..234 deliberately retain
the original OrbitCompile entry point; 235..511 use FastOrbitCompile. The old
runner wrote only missing modules, so that boundary is part of the frozen
source recipe. All files use UTF-8 and LF on every supported host.
"""

from pathlib import Path
import struct


DATA = Path("Paper15/CertificateData")
LEGACY_ORBIT_BATCHES = 235


def write(path, text):
    if path.exists():
        raise RuntimeError(f"Refusing to overwrite generated output: {path}")
    path.write_bytes(text.encode("utf-8"))


def main():
    payload = (DATA / "forest.bin").read_bytes()
    records = []
    pos = 0
    while pos < len(payload):
        word, nodes = struct.unpack_from("<IQ", payload, pos)
        pos += 12
        records.append((word, pos, nodes))
        pos += 3 * nodes
    if pos != len(payload) or len(records) != 61871:
        raise RuntimeError("Unexpected frozen forest framing or record count.")
    batches = []
    batch = []
    count = 0
    for record in records:
        if batch and (count + record[2] > 20000 or len(batch) >= 128):
            batches.append(batch)
            batch = []
            count = 0
        batch.append(record)
        count += record[2]
    if batch:
        batches.append(batch)
    if len(batches) != 533 or sum(r[2] for r in records) != 5103027:
        raise RuntimeError("Unexpected frozen gap-batch or node count.")

    for index, batch in enumerate(batches):
        name = f"Batch{index:04d}"
        lines = ["import Paper15.NaturalCompile", "set_option maxHeartbeats 0",
                 "set_option maxRecDepth 100000", "open Paper15.NaturalExact"]
        lines.extend(f"certify_nat_word% {word} {offset} {nodes}"
                     for word, offset, nodes in batch)
        lines.extend([
            f"namespace Paper15.NaturalExact.Batches.{name}",
            "noncomputable def entries : List (Nat × Trace) := [",
            ",\n".join(f"({word}, NaturalCertificates.w{word}.trace)"
                       for word, _, _ in batch),
            "]", "theorem checked : AllVerified entries := by", "  unfold entries",
            "  exact " + "".join(f"And.intro NaturalCertificates.w{word}.checked ("
                                for word, _, _ in batch)
            + "True.intro" + ")" * len(batch),
            f"end Paper15.NaturalExact.Batches.{name}",
        ])
        write(DATA / f"{name}.lean", "\n".join(lines) + "\n")

    for index in range(512):
        fast = index >= LEGACY_ORBIT_BATCHES
        module = "FastOrbitCompile" if fast else "OrbitCompile"
        command = "certify_fast_orbit_batch%" if fast else "certify_orbit_batch%"
        text = (f"import Paper15.{module}\nset_option maxHeartbeats 0\n"
                f"set_option maxRecDepth 100000\n{command} {index}\n")
        write(DATA / f"Orbit{index:04d}.lean", text)
    print("Emitted 533 gap chunks and 512 orbit chunks; no Lean evaluation was run.")


if __name__ == "__main__":
    main()
