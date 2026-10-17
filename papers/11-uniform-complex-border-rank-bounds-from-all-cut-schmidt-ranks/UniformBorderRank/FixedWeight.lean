import UniformBorderRank.BorderRank
import UniformBorderRank.FlatteningBounds

/-! The fixed-weight examples of Section 5.2, in the actual coefficient-array
model used for the main theorem. -/
noncomputable section
namespace UniformBorderRank

/-- The coefficient of weight `k` in the product of the given local pairs. -/
def fixedWeightTensor {N : ℕ} (d : Fin N → ℕ)
    (e₀ e₁ : ∀ i, Fin (d i) → ℂ) (k : ℕ) : Coeffs d :=
  prodCurveCoeff d e₀ e₁ k

/-- The finite-difference degeneration bounds the border rank uniformly in
N; no independence of the local vector pairs is required. -/
theorem borderRankLe_fixedWeightTensor {N : ℕ} (d : Fin N → ℕ) (hN : 0 < N)
    (e₀ e₁ : ∀ i, Fin (d i) → ℂ) (k : ℕ) :
    borderRankLe (fixedWeightTensor d e₀ e₁ k) (k + 1) :=
  borderRankLe_prodCurveCoeff d hN e₀ e₁ k

/-- The weight-zero tensor is the product of the first vector in every pair. -/
theorem isProduct_fixedWeightTensor_zero {N : ℕ} (d : Fin N → ℕ)
    (e₀ e₁ : ∀ i, Fin (d i) → ℂ) :
    isProduct (fixedWeightTensor d e₀ e₁ 0) := by
  refine ⟨e₀, ?_⟩
  intro u
  simp only [fixedWeightTensor, prodCurveCoeff_zero]

/-- Every actual flattening of a fixed-weight tensor has rank at most k+1. -/
theorem schmidtRank_fixedWeightTensor_le {N : ℕ} (d : Fin N → ℕ) (hN : 0 < N)
    (e₀ e₁ : ∀ i, Fin (d i) → ℂ) (k : ℕ) (S : Finset (Fin N)) :
    schmidtRank d (fixedWeightTensor d e₀ e₁ k) S ≤ k + 1 :=
  schmidtRank_le_of_borderRankLe (borderRankLe_fixedWeightTensor d hN e₀ e₁ k) S

theorem allCutLe_fixedWeightTensor {N : ℕ} (d : Fin N → ℕ) (hN : 0 < N)
    (e₀ e₁ : ∀ i, Fin (d i) → ℂ) (k : ℕ) :
    allCutLe d (fixedWeightTensor d e₀ e₁ k) (k + 1) := by
  intro S _ _
  exact schmidtRank_fixedWeightTensor_le d hN e₀ e₁ k S

end UniformBorderRank
