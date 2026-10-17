import Paper10.SSCFrame

noncomputable section
open Matrix
open scoped MatrixOrder
namespace Paper10
variable {q : ℕ}

/-- Every positive base point and symmetric direction occur in congruence coordinates.
Thus the universal factors R,K in SSC and SASC cover the full paper domain. -/
theorem congruence_coordinates_complete (X H : Matrix (Fin q) (Fin q) ℝ)
    (hX : X.PosDef) (hH : H.IsSymm) :
    ∃ R K : Matrix (Fin q) (Fin q) ℝ,
      IsUnit R ∧ K.IsSymm ∧ X = R * Rᴴ ∧ H = R * K * Rᴴ := by
  let R := CFC.sqrt X
  let K := R⁻¹ * H * R⁻¹
  have hR : R.PosDef := hX.posDef_sqrt
  have hRs : Rᴴ = R := hR.isHermitian.eq
  have hRi : (R⁻¹)ᵀ = R⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.inv.isHermitian.eq
  have hK : K.IsSymm := by
    show (R⁻¹ * H * R⁻¹)ᵀ = R⁻¹ * H * R⁻¹
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hRi, show Hᵀ = H from hH]
    simp only [Matrix.mul_assoc]
  have hx : R * Rᴴ = X := by
    rw [hRs]
    exact CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hu := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have h1 := Matrix.mul_nonsing_inv R hu
  have h2 := Matrix.nonsing_inv_mul R hu
  have hh : R * K * Rᴴ = H := by
    rw [hRs]
    dsimp [K]
    simp only [← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc H R⁻¹ R, h2, Matrix.mul_one]
  exact ⟨R, K, hR.isUnit, hK, hx.symm, hh.symm⟩

/-- Every symmetric direction has coordinates in every complete congruence frame.
This justifies allowing an arbitrary PSD coordinate precision matrix in the proposal. -/
theorem congruence_frame_complete {m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (hF : OrthonormalFrob F) (R H : Matrix (Fin q) (Fin q) ℝ) (hR : IsUnit R) (hH : H.IsSymm) :
    ∃ v : Fin m → ℝ, H = ∑ i, v i • (R * F i * Rᴴ) := by
  let K := R⁻¹ * H * (R⁻¹)ᴴ
  have hK : K.IsSymm := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_mul_mul_conjTranspose R⁻¹ (real_isHermitian hH)).eq
  obtain ⟨v, hv⟩ := hF.2.2 K hK
  refine ⟨v, ?_⟩
  have hr := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR)
  have hstar : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hr, Matrix.conjTranspose_one]
  have hh : R * K * Rᴴ = H := by
    dsimp [K]
    calc
      _ = (R * R⁻¹) * H * ((R⁻¹)ᴴ * Rᴴ) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hr, hstar, Matrix.one_mul, Matrix.mul_one]
  rw [← hh, hv]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end Paper10
