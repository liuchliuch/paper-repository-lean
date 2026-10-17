import Paper10.Remainder
import Paper10.Covariance

noncomputable section
open Matrix
namespace Paper10
variable {q : ℕ}

/-- The quartic event itself enforces the spectral neighborhood needed by the remainder. -/
theorem quartic_controls_spectrum (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h4 : t ^ 2 * Matrix.trace (A ^ 4) ≤ ε / 16) :
    ∀ i, |t * (real_isHermitian hA).eigenvalues i| ≤ 1 / 2 := by
  intro i
  let μ := (real_isHermitian hA).eigenvalues
  have hm : μ i ^ 4 ≤ Matrix.trace (A ^ 4) := by
    rw [trace_pow_spectral A hA 4]
    change μ i ^ 4 ≤ ∑ j, μ j ^ 4
    exact Finset.single_le_sum (f := fun j => μ j ^ 4) (fun j _ => by positivity) (Finset.mem_univ i)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hh : (t * μ i) ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ t ^ 2)
    have hmul2 := mul_le_mul_of_nonneg_left (hmul.trans h4) (sq_nonneg t)
    have heps : t ^ 2 * ε ≤ 1 :=
      (mul_le_mul_of_nonneg_right ht2 hε.le).trans (by simpa using hε1)
    nlinarith
  have hh' : |t * μ i| ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := by simpa only [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (t * μ i) ^ 4)] using hh
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)).mp hh'

/-- Positivity of the actual proposed normalized endpoint. -/
theorem normalized_endpoint_posDef (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    {t : ℝ} (hμ : ∀ i, |t * (real_isHermitian hA).eigenvalues i| ≤ 1 / 2) :
    ((1 : Matrix (Fin q) (Fin q) ℝ) + t • A).PosDef := by
  let U := (real_isHermitian hA).eigenvectorUnitary
  let μ := (real_isHermitian hA).eigenvalues
  have hAD : A = (U : Matrix _ _ ℝ) * Matrix.diagonal μ * (U : Matrix _ _ ℝ)ᴴ :=
    real_spectral_theorem A hA
  have hD : (Matrix.diagonal (fun i => 1 + t * μ i)).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    have hh := (abs_le.mp (hμ i)).1
    dsimp [μ]
    linarith
  have hU : IsUnit (U : Matrix (Fin q) (Fin q) ℝ) := (unitary.toUnits U).isUnit
  have hpos := hD.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hU.star)
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at hpos
  rw [orthogonal_conj_one_add_smul, ← hAD] at hpos
  exact hpos

/-- On the joint cubic/quartic event, feasibility and the two-sided remainder hold together. -/
theorem normalized_good_event (A : Matrix (Fin q) (Fin q) ℝ) (hA : A.IsSymm)
    {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h3 : t * |Matrix.trace (A ^ 3)| ≤ ε / 2)
    (h4 : t ^ 2 * Matrix.trace (A ^ 4) ≤ ε / 16) :
    ((1 : Matrix (Fin q) (Fin q) ℝ) + t • A).PosDef ∧ |Ft t A| ≤ 2 * ε := by
  have hμ := quartic_controls_spectrum A hA ht ht1 hε hε1 h4
  refine ⟨normalized_endpoint_posDef A hA hμ, ?_⟩
  have hh := lemma_3_1_matrix t A hA ht hμ
  linarith

end Paper10
