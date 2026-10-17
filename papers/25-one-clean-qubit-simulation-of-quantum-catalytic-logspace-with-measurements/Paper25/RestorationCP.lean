import Paper25.RestorationChoi

/-! A semantic complete-positivity interface for Lemma 2. Positivity of the
channel tensored with the identity is used directly on a maximally entangled
positive operator; no Choi criterion is assumed as an external theorem. -/
noncomputable section
open scoped ComplexOrder ComplexConjugate
namespace Paper25

/-- Positivity with an input-sized reference implies the Choi positivity used
in Lemma 2. Complete positivity supplies this hypothesis for every reference. -/
theorem restorationChoi_posSemidef_of_reference_positive {W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ)
    (hpositive : ∀ X : Matrix (V × V) (V × V) ℂ,
      X.PosSemidef → (referenceExtension Ψ X).PosSemidef) :
    (restorationChoi Ψ).PosSemidef := by
  classical
  let Ω : Matrix (V × V) (V × V) ℂ :=
    Matrix.vecMulVec choiIdentityVector (star choiIdentityVector)
  have hΩ : Ω.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have heq : referenceExtension Ψ Ω = restorationChoi Ψ := by
    ext p q
    have hsection : (fun i j => Ω (i,p.2.2) (j,q.2.2)) =
        Matrix.single p.2.2 q.2.2 (1 : ℂ) := by
      ext i j
      simp only [Ω, Matrix.vecMulVec, choiIdentityVector, Pi.star_apply,
        Matrix.single, Matrix.of_apply]
      by_cases hi : i = p.2.2 <;> by_cases hj : j = q.2.2 <;>
        simp [hi,hj] <;> aesop
    change Ψ (fun i j => Ω (i,p.2.2) (j,q.2.2)) (p.1,p.2.1) (q.1,q.2.1) = _
    rw [hsection]
    rfl
  rw [← heq]
  exact hpositive Ω hΩ

/-- **Lemma 2 from semantic complete positivity.** Positivity of `Ψ ⊗ id`
and exact marginal restoration on every state imply a single work density
operator and product form on the full operator space. -/
theorem lemma_2_semantic_restoration {W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] (v₀ : V)
    (Ψ : Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ)
    (hpositive : ∀ X : Matrix (V × V) (V × V) ℂ,
      X.PosSemidef → (referenceExtension Ψ X).PosSemidef)
    (hrestore : ∀ ρ, IsDensity ρ → workPartialTrace (Ψ ρ) = ρ) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧ ∀ X, Ψ X = Matrix.kronecker η X :=
  lemma_2_from_marginal_restoration_generic v₀ Ψ
    (restorationChoi_posSemidef_of_reference_positive Ψ hpositive) hrestore

end Paper25
