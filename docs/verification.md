# Verification

Each paper is a separate Lean project. Its `publication.json` identifies production entry modules, build targets, public results, external assumptions and the primary Comparator configuration. Run the shared commands from the repository root; the dispatcher invokes `./scripts/lake-local` inside the selected paper directory.

## Source checks and builds

```sh
python3 scripts/verify.py --paper 28 --check static
python3 scripts/verify.py --paper 28 --check build
```

The static check validates project structure, metadata, local imports, dependency pins, registered generated inputs and proof markers in the available production sources. It does not compile Lean or check a proof in the kernel. Without `--paper`, the static command checks all papers. Build and Comparator commands require one paper explicitly.

A build uses the committed `lean-toolchain` and `lake-manifest.json`. Dependencies may be downloaded on first use. For projects with generated inputs, first follow [generated inputs](generated-inputs.md); a build refuses missing or changed registered outputs and never starts a generator automatically. `PINKFOLD_LAKE`, if needed, must be an absolute path to the real Lake executable.

## Official Comparator

The shared tools use upstream [Lean Comparator](https://github.com/leanprover/comparator), lean4export and Lean4Checker. Exact revisions are recorded in [`toolchains.json`](../tools/comparator/toolchains.json) and the corresponding committed Lake manifests. Set up the tools explicitly:

```sh
python3 scripts/setup_comparator.py --execute
python3 scripts/verify.py --paper 28 --check comparator --local
```

The default profile is Lean 4.24.0. Paper 11 uses Lean 4.29.0-rc6; prepare its profile with:

```sh
python3 scripts/setup_comparator.py --toolchain leanprover/lean4:v4.29.0-rc6 --execute
```

The dispatcher selects the compatible profile automatically. `--local` explicitly runs trusted sources without an operating-system sandbox. Omit it to use upstream `landrun`, which must already be installed. Both modes retain statement comparison, allowed-axiom checks and the official exported-environment kernel replay. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

With no `--suite`, the dispatcher selects `primary_comparator` from the paper metadata. Use `--suite CONFIGURATION_ID` for a named supporting check or negative control. A supporting check covers only its fixed statements. Negative controls deliberately add a premise or use a forbidden axiom; only the corresponding official rejection counts as a successful control. Compilation, missing-target and exporter failures do not.

## Fixed statements and external assumptions

Comparator challenges are fixed independently of the current solution during comparison. Semantic correspondence still requires review of the paper statements, quantifiers, hypotheses and scope. A matching conditional theorem does not construct its external premises. Each paper's README and `EXTERNAL_DEPENDENCIES.md` describe that boundary.

Papers 26, 35 and 38 require preparation and independent review of their final statement specifications. Their README and metadata provide the paper-specific commands. After reviewing the exact source and statement hashes, pass the reviewed manifest digest:

```sh
python3 scripts/verify.py --paper 26 --check comparator --local \
  --reviewed-manifest-sha256 REVIEWED_SHA256
```

The dispatcher verifies the review manifest and generated-file hashes. Earlier component configurations remain available with their narrower scope; they cannot substitute for these final specifications.

## Reproducing checks

Print commands and preparation requirements without executing anything:

```sh
python3 scripts/verification_plan.py --paper 28 --local
python3 scripts/verification_plan.py --local
```

Each explicit build or Comparator run writes a timestamped log and `result.json` under the ignored `.artifacts/` directory. Receipts record the selected command, input hashes, tool pins, dependency observations and execution mode. Success concerns that command and its fixed inputs. Existing compiled caches are not independently authenticated; use a fresh checkout and cache when reproducing results from source.

Large certificate evaluations, complete dependency replays and expensive Comparator checks have not all been rerun for this distribution. Their absence is not a proof success. CI runs source checks, Python tests and index consistency checks only.
