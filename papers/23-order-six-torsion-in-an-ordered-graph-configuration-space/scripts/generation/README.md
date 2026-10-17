# Local generation recipe

This directory contains portable, pinned Python sources and readable Lean proof-scaffold templates. It does not contain a precomputed archive of the large expanded numeric tables. All scripts use the Python standard library. The normal entry point is the shared repository preparation dispatcher:

```sh
python3 ../../scripts/prepare.py --paper 23
python3 ../../scripts/prepare.py --paper 23 --execute
python3 ../../scripts/prepare.py --paper 23 --check
```

The first invocation only prints the plan. Execution is explicit and can be expensive. The dispatcher copies only the manifest's pinned inputs into an isolated staging project, runs the literal recipe command, and checks every declared output's exact SHA-256 and byte size before installation. This recipe never invokes Lean, Lake, Comparator, a build controller or a watcher. All subsequent kernel checks remain separate.

`generated-artifacts.json` fixes the output module paths, sizes, hashes and imports. `template-index.json` maps those paths to `.lean.in` templates. Each template preserves the current theorem statements, proof scaffolding and historical proof repairs while replacing expanded numeric definition bodies with named placeholders. `render_scaffolds.py` fills those placeholders from fresh exporter candidates and preserves the historical negative-integer spelling. A missing candidate, missing RHS or template/index mismatch is an error. The dispatcher rejects any final output byte mismatch.

The only completed generation-related checks are static packaging review, exact reconstruction of the existing outputs from their templates plus their existing RHSs, and Python AST parsing. **No generator has been executed end to end.** Reproducibility is a pending exact-hash check, and even a successful source hash check does not prove a certificate identity or close the paper's deferred verification status.

## P23 source graph

The recipe covers 1039 files (354,256,606 bytes): all child modules of `Paper23/Bounding`, `CertificateCycle`, `CertificateCocycle`, and `CertificateChecks`, plus `Paper23/CertificateData.lean`. Generic mathematical modules and the thin aggregate root proofs remain ordinary source.

The normal recipe uses `generation-inputs/certificate.json`, the exact 5,173,494-byte original-coordinate scientific witness with SHA-256 `15083e251df9fae235f6edde6ba2e8b4d64c2e23ac38940190a13e586188adf4`. It contains the alternative explicit cycle, bounding chain and detecting cocycle, graph incidence and particle permutations. This is a compact witness input; the hundreds of megabytes of intermediate sparse normal forms are recomputed.

The ordered exporter stages use chunk size 64, 16 declarations per cycle/cocycle module, and the cocycle bucket transition at level 8. The bounding exporter first constructs the flat candidate graph with 16 leaves/nodes per block, then stages the historical bucket tail from level 4 with widths 8, 4, 2, and then 1. The recipe installs candidate children into staging and restores the current proof-scaffold templates. It does not invoke the old stateful bucket installer. Current cycle irreducibility/check changes, cocycle first-leaf and bucket-bridge repairs, and structural-recursion definitions are preserved by the templates rather than discarded by a blind historical export.

## Optional full scientific-witness reconstruction

The complete stdlib integer/group-ring constructor is included as `vendor/certificate.py`. It is intentionally **not** run by the normal recipe. A separate explicit command can rerun the expensive reduction and external identity checks into a NEW file:

```sh
python3 scripts/generation/recreate_seed.py --output .lake/recreated-p23-certificate.json
```

The wrapper uses the alternative-witness mode, removes only the later construction metadata fields, preserves the original JSON serialization, and requires the exact old seed SHA before writing. The old seed and a later original-project certificate agree on every mathematical field and differ only in this metadata. No from-scratch rerun or exact-byte recreation is claimed. The constructor's own Python checks are not Lean proofs. No reduction checkpoint or opaque pickle is needed by the normal recipe, and no checkpoint is supplied in this publication source.

The numbered theorem is existential. The alternative witness's support counts, non-alternating form and residual dimensions remain distinct from the source's reported construction, exactly as disclosed in the paper README and external-dependency register.
