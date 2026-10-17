# Highness for isomorphism at Scott rank omega_1^CK

[Source paper](https://liuchliuch.github.io/repository/highness-for-isomorphism-at-scott-rank-omega-1-ck/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `Paper19.theorem_1` | For every computable input tree, including the empty tree: computable structures on ℕ in a fixed finite language, definable finite-tuple orbits, isomorphism exactly when a path exists, and uniform conversions in both directions. |
| Uniform construction | `Paper19.uniform_construction_all_inputs` | Fixed oracle programs construct the structures and convert solutions uniformly, without an extendibility oracle or ordinal bound as input. |
| Lemma 5 | `Paper19.lemma5_uniform` | Uniform path-to-isomorphism and isomorphism-to-path programs for the intermediate presentation. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 19 --check static
python3 ../../scripts/verify.py --paper 19 --check build
python3 ../../scripts/verify.py --paper 19 --check comparator --suite main
```

## Assumptions

The main construction and local orbit/rank analysis have no additional external theorem inputs. Corollary 7 and both exact-rank remark paragraphs require unavailable effective Scott-rank and hyperarithmetical results and are not formalized. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The Scott-rank upper bound is expressed through parameter-free computable infinitary definitions of every finite-tuple orbit. No general formal object for ω₁ᴄᴋ or complete Scott-rank library is asserted. `ComputablyPresented` uses finite recursive syntax and a computable well-founded-relation rank schema; the schema is chosen separately at each fixed level. The injection-tree auxiliary is narrower than the full degree-theoretic Corollary 7.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/HSR-highness_for_isomorphism_at_scott_rank_omega_1_ck.pdf).
- [Franklin–Rossegger–Turetsky, Structural complexity vs. computational complexity](https://arxiv.org/abs/2606.15196).
- [Knight–Millar, Computable structures of rank omega_1^CK](https://arxiv.org/abs/math/0508507).
