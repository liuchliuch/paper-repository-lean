# Generated inputs

Large reproducible certificate data and repeated expanded verification files are generated locally instead of being committed to Git. Hand-written proofs, mathematical checkers, generators, independent statement templates, necessary compact seeds and frozen output specifications stay in the repository.

## Prepare one paper

Run from the repository root:

```sh
python3 scripts/prepare.py --paper 20
python3 scripts/prepare.py --paper 20 --execute
python3 scripts/prepare.py --paper 20 --check
python3 scripts/verify.py --paper 20 --check build
```

The first command prints the recipe, prerequisites and current readiness. `--execute` runs that recipe and may be expensive. `--check` checks existing output hashes without generating anything. Preparation and Lean compilation are separate explicit steps; build commands never generate missing inputs silently.

The projects with registered generated inputs are:

| Paper | Local outputs | Additional prerequisites |
|---|---|---|
| [15](../papers/15-an-exact-classical-threshold-in-the-binary-triangle-network/) | Exact finite certificates and their Lean proof modules | C++17 compiler with `__int128`, Boost headers and Python 3 |
| [20](../papers/20-counterexamples-to-log-concavity-of-local-bps-invariants/) | Numerical certificate and finite-check Lean modules | Python 3; see the paper recipe |
| [23](../papers/23-order-six-torsion-in-an-ordered-graph-configuration-space/) | Expanded certificate and finite-check Lean modules | Python 3 and the retained compact witness seed |
| [26](../papers/26-rank-dependent-lower-bounds-for-quantum-chi-squared-tomography/) | Repeated fixed Comparator modules | Python 3 |
| [31](../papers/31-dimension-free-small-gradients-in-ell-p-geometry/) | Repeated fixed Comparator modules | Python 3 |

The exact commands and prerequisites are in each project's `generated-artifacts.json`. Paper 23's default recipe expands its retained exact witness; it does not repeat the optional scientific witness search. Papers 26 and 31 reconstruct fixed text from independent literal templates and edit recipes, without inspecting current solution types. Paper 26's separate final-specification review remains required; see [verification](verification.md).

## Reproducibility

Each manifest records the generator inputs and SHA-256 hashes, literal command arguments, output paths, expected byte counts and output hashes. Generated Lean modules also record their module names and captured imports.

Preparation copies only registered inputs to a fresh ignored `.lake/generation/` directory. It runs the recipe there, verifies the complete staged output set, rechecks the inputs and manifest, and installs only matching outputs. It refuses to overwrite changed generated files. Failed attempts keep their logs and receipts in the staging directory.

Generation is trusted local program execution, without an operating-system sandbox. A matching output hash verifies reproduction of those bytes; Lean compilation and kernel verification remain separate checks. Hash mismatches require investigation and review of the changed mathematical inputs, rather than weakening the manifest.

## What Git contains

Registered generated outputs, `.lake/`, `.artifacts/`, compiled objects and local logs are ignored. Small irreducible scientific inputs remain when needed for reproducible construction; a certificate is not automatically dispensable merely because it is data.

Static checking validates retained generator inputs and the declared import graph. If generated production sources are absent, its report lists `unmaterialized_production_modules` and defers their source scan until materialization. It does not claim to have parsed absent Lean files, evaluated their certificates or checked them in the kernel.
