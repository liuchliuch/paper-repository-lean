#!/usr/bin/env python3
"""Optional expensive from-scratch P23 scientific witness construction.

This is NOT part of the normal preparation recipe. It reruns the full sparse
integer/group-ring reduction and external identity checks, never Lean. Use an
explicit NEW output path. Its old-input SHA is checked after canonicalizing only
the construction metadata and JSON serialization; no successful rerun is claimed.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

EXPECTED = "15083e251df9fae235f6edde6ba2e8b4d64c2e23ac38940190a13e586188adf4"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("Refusing to overwrite an existing witness")
    path = Path(__file__).resolve().parent / "vendor/certificate.py"
    spec = importlib.util.spec_from_file_location("p23_certificate_producer", path)
    producer = importlib.util.module_from_spec(spec)
    import sys
    sys.modules[spec.name] = producer
    spec.loader.exec_module(producer)
    data = producer.construct(strict_source_counts=False)
    producer.check(data, strict_source_counts=False)
    # The original scientific seed predates the extra construction metadata.
    data["construction"] = {name: data["construction"][name]
                            for name in ["group_ring_unit_pivots", "integer_unit_pivots"]}
    payload = json.dumps(data).encode("utf-8")
    actual = hashlib.sha256(payload).hexdigest()
    if actual != EXPECTED:
        raise ValueError("Reconstructed seed does not match pinned old bytes: " + actual)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(payload)
    print("Exact old scientific seed recreated:", actual)


if __name__ == "__main__":
    main()
