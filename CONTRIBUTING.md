# Contributing

Each paper is an independent Lake project under `papers/<id>-<slug>/`. Use `python3 scripts/add_paper.py` to create the standard files, then implement the paper's results and update its `publication.json` metadata. Regenerate the index with `python3 scripts/catalog.py`.

## Paper documentation

Every paper README has the sections Results, Build, Assumptions, Verification and References. State the exact public Lean declarations, mathematical hypotheses and scope. Record external published theorems in EXTERNAL_DEPENDENCIES.md with their original statements, references and use sites. Prefer explicit parameters for unformalized external results. A paper-owned conclusion must not be assumed as an external premise.

Keep original namespaces, `lean-toolchain` and dependency commit locks. Metadata lists production roots, build targets, result declarations and one primary Comparator configuration. Additional fixed negative controls or supporting specifications may be retained where useful; their scopes must be precise.

## Fixed statements

Comparator challenges must be independent fixed statements. Never infer the challenge from the current solution type during a comparison. Include a genuine added-premise and illegal-axiom control. Prepared specifications require an independent statement-correspondence review bound to the exact source, exported-type and generated-fixture hashes; the dispatcher checks that reviewed digest before use.

Registered generated sources and binary inputs stay out of Git. Commit their generator, necessary compact seed or independent specification template, frozen output hashes and captured module imports. See [generated inputs](docs/generated-inputs.md).

## Checks

```sh
python3 scripts/verify.py --paper ID --check static
python3 -m unittest discover -s tests -v
python3 scripts/catalog.py
python3 scripts/catalog.py --check
```

A new template contains no claimed paper proof and deliberately fails the result/configuration requirements until implemented. Builds and Comparator runs are separate explicit steps documented in [verification](docs/verification.md).

## Repository hygiene

Use English prose and comments, project-relative paths, pinned dependencies and shared scripts. Keep caches, logs, build outputs, local-agent files, backups and registered generated outputs out of Git. Preserve mathematical source, precise assumptions, attribution and third-party notices. Do not introduce unregistered `sorry`, `admit` or axioms into production code; deliberate specification holes and negative controls belong outside the production entry closure.
