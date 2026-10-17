# External dependencies

The accepted scope excludes four external secondary results: full Corollary 5.1 cactus-to-secant containment through the global scheme-theoretic Segre embedding, product affine chart, O(1,...,1) trivialization and restriction identification (Stacks tags 01WD, 01MS, 03GL, 01XT); the external W-state exact CP-rank and sharp border-rank comparison; Nisan's ordered ABP minimal-prefix-width characterization; and the Bhargava–Tengse commutative set-multilinear ABP construction. Proved local chart/algebra statements and the paper's own Section 5.2 bounds remain in the production library. None of these exemptions is added as a production axiom. Paper/Challenge.lean contains 19 specification-only sorry placeholders, separate from the proved Paper/Proofs.lean. Toolchain compatibility is exceptional: Lean 4.29rc6, Mathlib f156f7abd91ac67adb22bf999e5a71ba22e22e41, Comparator 066c3bc9e966ccad9a633d780ae4de13cd0f27b6 and lean4export 048394e1afeeb52b0fa27bcf3f1ade2ff0f0ab6d. The shared root tools/comparator/lean-4.29-rc6 profile provides those compatible pins and its locked transitive manifest, including Lean4Checker b7398199245524275543dec6113229c9bb4902e5. The root dispatcher requires an explicit local execution opt-in. Original execution used the official default Lean kernel with nanoda disabled and local unsandboxed execution. No non-Lean certificate/data assets are needed.

Lean toolchain: `leanprover/lean4:v4.29.0-rc6`.

Locked package revisions:

- `plausible`: `e84e3e16aea6b72cc5d311ca1bb25caad417e162`.
- `LeanSearchClient`: `c5d5b8fe6e5158def25cd28eb94e4141ad97c843`.
- `importGraph`: `f207d9fcf0cef00ba79962a33ef156061914d9c7`.
- `proofwidgets`: `2e58165a9dcdca9837b666528f974299ee1a51cc`.
- `aesop`: `c3361708f266893de5d1769192b60d4b1831f2bb`.
- `Qq`: `221e8088e3a066b8676dc471ff10638cf1c10835`.
- `batteries`: `77a5160a74772214ef37caba2847cfe9ab600285`.
- `Cli`: `3de531c1135f5e3a01f3ac04830996fda476b28e`.
- `mathlib`: `f156f7abd91ac67adb22bf999e5a71ba22e22e41`.

Only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted by the positive official Comparator contracts unless a contract and the documented mathematical boundary explicitly say otherwise. An illegal axiom in a negative control is intentional and is never part of the production import.

Release verification status: static inspection only. No fresh build, certificate evaluation, full proof replay, or official Comparator run was performed for this export.
