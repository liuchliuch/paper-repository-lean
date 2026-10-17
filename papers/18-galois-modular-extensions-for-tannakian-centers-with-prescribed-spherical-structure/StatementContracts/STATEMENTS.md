# Paper-facing statement contracts — P18

These statements mirror the paper's quantifiers and hypotheses and are the
independently readable specification used by the official Comparator.

## Theorem 1.1 (S1.Thmtheorem1)

Let `B` be a premodular fusion category with a specified spherical structure,
and suppose `Z_2(B) ≃ Rep(G)` as braided fusion categories, for a finite group
`G`. Then there exist a modular fusion category `M` and a fully faithful
braided spherical tensor functor `B ↪ M` such that `B'_M` is integral.

External input (Johnson–Freyd, arXiv:2601.23192, Proposition 2.3): existence of
a nondegenerate braided extension `B ↪ M0` with integral centralizer `B'_{M0}`.
Packaged as an explicit hypothesis of the Lean theorem, never as a custom axiom.

## Lemma 2.1 (Lacabanne) (S2.Thmtheorem1)

Let `C` be a nondegenerate braided fusion category with a pivotal structure `j`
and associated balancing `θ`. For `X ∈ Irr(C)`, put `d_X = dim_R^j(X)`,
`n_X = d_X d_{X*}`, `γ_X = d_X / d_{X*}`. The scalars `γ_X` define a tensor
automorphism of `id_C`. There is a unique `t ∈ Inv(C)` such that

- (2.1) `c_{X,t} c_{t,X} = γ_X id_{t⊗X}` for every simple `X`,
- (2.2) `θ_{t^{-1}} = 1`.

## Proposition 2.2 (S2.Thmtheorem2)

Let `A` be a premodular fusion category such that
`Z_2(A) = ⟨f⟩ ≃ Rep(ℤ/2)`, `dim_A(f) = -1`.
Then `A` admits a minimal modular extension preserving its specified spherical
structure. More precisely, every minimal nondegenerate braided extension of `A`
admits a spherical structure with this restriction.

## Lemma 3.1 (S3.Thmtheorem1)

The target of a dominant tensor functor from an integral fusion category is
integral. If a finite group `H` acts on a fusion category `C`, then `C^H` is
integral if and only if `C` is integral.

## Lemma A.1 (A1.Thmtheorem1)

Let `A` be a braided fusion category with `Z_2(A) ≃ Rep(ℤ/2)`. There is a
minimal nondegenerate braided extension of `A`. For any such extension
`ι : A ↪ N`, any braided tensor autoequivalence `F` of `N`, and any specified
tensor natural isomorphism `α : Fι ⇒ ι`, there is a tensor natural isomorphism
`β : F ⇒ id_N` such that `βι = α`.

Cohomological core: for `H = ℤ/2` and trivial `ℂ^×` coefficients,
`H^{2r}(H, ℂ^×) = ℂ^×/(ℂ^×)^2 = 0` for `r ≥ 1` (every complex number is a
square), so the degree-four obstruction vanishes and `H^2` is trivial.

## Appendix B (pointed obstruction)

`A = ℤ/4 × ℤ/4`, `q(a,b) = i^{ab}`, monodromy `m((a,b),(c,d)) = i^{ad+bc}`.
`f = (2,0)`, `B = ⟨f⟩'_T`. Specified structure modified by `χ(a,b)=i^b`.
Then `χ` is `+1` on `f` but does not extend to a spherical structure on `T`
(every `±1` character on `A` is trivial on `2A`, hence on `(0,2)`, whereas
`χ(0,2) = -1`). The character `χ̃(a,b)=i^b` on all of `A` gives a pivotal
extension with slope `χ̃^2 = (-1)^b = m(f,(a,b))`, nonspherical; the twist of
`f` remains `+1`.

## Authorized relative verification (2026-10-16)

The original unconditional contracts above remain unchanged in
`Verification/OriginalChallenge.lean`. The user authorized retaining precise
published external results as explicit hypotheses. The relative contract is
`Verification/RelativeChallenge.lean`; its solution imports no Verification
module or challenge. The two published existence inputs are registered in
`EXTERNAL_DEPENDENCIES.md`.

Theorem1.1 has the original actual `ModularExtension` output and the original
canonical universe bounds. It additionally takes the JF Proposition2.3 input
for the source, the same JF input at the sign-kernel presentation size, and
the ENO relative O4-realization input for the actual de-equivariant action
of the chosen initial extension's sphericalization. The latter input is
`CategoricalTheorem11.InitialObstructionInput`; its definition exposes only
the registered ENO realization proposition, not a minimal, pivotal, spherical
or final-extension conclusion.

A.1 and Proposition2.2 take the ENO input for the given actual C2-Tannakian
source. The project proves the C2 primitive, actual minimal output,
universal specified-boundary classification and prescribed spherical
structure. Positive extension is derived from the nonspherical JF input
using the internally proved literal JF Proposition2.4 and positive-pivotal
uniqueness.

The final Comparator configuration checks these four relative statements
alongside the original Lemma2.1, AppendixB, all four actual Lemma3.1 contracts,
and literal JF Proposition2.4. Its negative controls add a real extra premise
and use a real illegal axiom respectively. A separate original-unconditional
probe retains the external inputs in its candidate types and must be
rejected against the original statements. A relative pass never asserts a
Lean proof of either external existence theorem.
