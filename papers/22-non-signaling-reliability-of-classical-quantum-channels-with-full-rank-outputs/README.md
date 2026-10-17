# Non-signaling reliability of classical-quantum channels with full-rank outputs

[Source paper](https://liuchliuch.github.io/repository/non-signaling-reliability-of-classical-quantum-channels-with-full-rank-outputs/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Lemma 1 | `Paper22.Paper.lemma_1_effect_completion` | For M ≥ 2 and K = M+6, complete finite-dimensional effects while increasing each effect and setting their weighted average to I/M. |
| Theorem 1 | `Paper22.Paper.theorem_1_one_shot` | For every finite classical-quantum channel and M ≥ 2: ε_MC(M) ≤ ε_NS(M) ≤ ε_MC(M+6). |
| Theorem 2 | `Paper22.Paper.theorem_2_reliability` | Both extended-real reliability limits for every full-rank finite channel and 0 < R < C(W), relative to ExternalMetaConverseLimit. |
| Equation 26 | `Paper22.activationIdentity_proved` | The one-bit activation identity for actual channels, proved without an external activation premise. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 22 --check static
python3 ../../scripts/verify.py --paper 22 --check build
python3 ../../scripts/verify.py --paper 22 --check comparator --suite main
```

## Assumptions

Theorem 2 explicitly assumes the Oufkir–Tomamichel–Berta meta-converse exponent via `Paper22.ExternalMetaConverseLimit`. Its base-two specialization and use sites are stated in [External dependencies](EXTERNAL_DEPENDENCIES.md). The one-shot comparison, activation identity, full-rank estimates and message/rate transfers are internal proofs.

## Verification

The main reliability conclusion retains the external exponent parameter. It does not assert an unconditional proof of that published exponent. The rate is strictly positive and below Holevo capacity, and the outputs are full rank. General possibly-singular-channel endpoint continuity and optimization beyond this scope are not asserted.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/NSR-non_signaling_reliability_of_classical_quantum_channels_with_full_rank_outputs.pdf).
- [Oufkir–Tomamichel–Berta, Error exponent of activated non-signaling assisted classical-quantum channel coding](https://arxiv.org/abs/2410.01084).
