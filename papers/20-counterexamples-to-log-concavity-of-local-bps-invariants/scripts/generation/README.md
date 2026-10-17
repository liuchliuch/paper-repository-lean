# Local generation recipe

This directory contains portable, pinned Python sources and readable Lean proof-scaffold templates. It does not contain a precomputed archive of the large expanded numeric tables. All scripts use the Python standard library. The normal entry point is the shared repository preparation dispatcher:

```sh
python3 ../../scripts/prepare.py --paper 20
python3 ../../scripts/prepare.py --paper 20 --execute
python3 ../../scripts/prepare.py --paper 20 --check
```

The first invocation only prints the plan. Execution is explicit and can be expensive. The dispatcher copies only the manifest's pinned inputs into an isolated staging project, runs the literal recipe command, and checks every declared output's exact SHA-256 and byte size before installation. This recipe never invokes Lean, Lake, Comparator, a build controller or a watcher. All subsequent kernel checks remain separate.

`generated-artifacts.json` fixes the output module paths, sizes, hashes and imports. `template-index.json` maps those paths to `.lean.in` templates. Each template preserves the current theorem statements, proof scaffolding and historical proof repairs while replacing expanded numeric definition bodies with named placeholders. `render_scaffolds.py` fills those placeholders from fresh exporter candidates and preserves the historical negative-integer spelling. A missing candidate, missing RHS or template/index mismatch is an error. The dispatcher rejects any final output byte mismatch.

The only completed generation-related checks are static packaging review, exact reconstruction of the existing outputs from their templates plus their existing RHSs, and Python AST parsing. **No generator has been executed end to end.** Reproducibility is a pending exact-hash check, and even a successful source hash check does not prove a certificate identity or close the paper's deferred verification status.

## P20 source graph

The recipe covers 605 files (315,482,742 bytes) in `Paper20/Certs/RContent36`, `HilbertParts`, `ACacheFast36` and `ContentQ36Rows`. The small production bootstrap/aggregate modules `RContent36/Test36.lean`, `HilbertParts/Test777.lean` and `HilbertParts/All.lean` remain ordinary pinned source.

The ordered Python stages are:

1. `gen_hilbert_tree.py`: full rank-43 partition branches; it compares its resulting 904 coefficients with the small retained `H43.lean` vector and reuses the explicit Test777 proof name.
2. `gen_a_cache_fast36.py`: exact rank-36 numerator-factor row cache.
3. `gen_r_content36_tree.py`: rank-36 partition/content tree, RootData and root assembly; its exact expected Q20/Q21/Q22 values come from retained `certs/q36.json`. The program uses the stdlib helpers `native_q36.py` and `gen_certs.py`. Its root JSON is a generated staging intermediate, not a pinned opaque substitute for the tree.
4. `split_r_content_states.py`: the historical deterministic splitting of large states into row declarations.
5. `test_q36_rows.py` and `gen_q36_rows.py`: exact content-row vectors and aggregate checking source, using the staging root JSON.
6. `render_scaffolds.py`: restores the current reviewed proof scaffold around the regenerated numeric bodies.

The original generator sources were located in the original project's `work/` directory. Their ports use the staging working directory and portable helper locations. Historical build scripts and control machinery are excluded. The small expected H43/Q36 vectors are candidate data, not assumed mathematical equalities: the generated Lean check sources retain all proof obligations. No proof/certificate requirement was removed.
