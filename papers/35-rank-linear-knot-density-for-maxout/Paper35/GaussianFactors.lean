import Paper35.GaussianSpectrum
import Paper35.Deep
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section
open Set Matrix
open scoped BigOperators

namespace Paper35.GaussianFactors
open Source Deep GaussianIndependent

variable {d q : ℕ}

def quadratic (C : Matrix (Fin d) (Fin d) ℝ) (v : Space d) : ℝ :=
  covarianceForm C (fun i => v i) (fun i => v i)

/-- Exactly the source Gaussian switch factor (8.17). -/
def D (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (σ : Fin q → ℝ) : ℝ :=
  sSup ((fun v : Space d => ∑ r, Paper35.gaussianRankCoefficient (K r) / σ r *
    Real.sqrt (quadratic (C r) v)) '' {v | ‖v‖ = 1})

/-- Exactly the source Gaussian length factor (8.18); `covarianceMax` has
already been identified with the largest PSD eigenvalue in GaussianSpectrum. -/
def A (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (covarianceMax (∑ r, gaussianLengthCorrection (K r) • C r))

lemma quadratic_eq_inner (C : Matrix (Fin d) (Fin d) ℝ) (v : Space d) :
    quadratic C v = inner ℝ v (covarianceOperator C v) := by
  simp only [quadratic, covarianceForm, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, covarianceOperator]
  exact dotProduct_comm _ _

lemma quadratic_nonneg (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (v : Space d) :
    0 ≤ quadratic C v := hC.2 _

lemma quadratic_unit_le_covarianceMax (C : Matrix (Fin d) (Fin d) ℝ)
    (v : Space d) (hv : ‖v‖=1) : quadratic C v ≤ covarianceMax C := by
  rw [quadratic_eq_inner]
  calc
    _ ≤ |inner ℝ v (covarianceOperator C v)| := le_abs_self _
    _ ≤ ‖v‖ * ‖covarianceOperator C v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖covarianceOperator C‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((covarianceOperator C).le_opNorm v) (norm_nonneg _)
    _ = _ := by simp [hv, covarianceMax]

lemma D_bddAbove (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin q → ℝ) (hσ : ∀ r, 0 < σ r) :
    BddAbove ((fun v : Space d => ∑ r, Paper35.gaussianRankCoefficient (K r) / σ r *
      Real.sqrt (quadratic (C r) v)) '' {v | ‖v‖=1}) := by
  refine ⟨∑ r, Paper35.gaussianRankCoefficient (K r) / σ r * Real.sqrt (covarianceMax (C r)), ?_⟩
  rintro x ⟨v,hv,rfl⟩
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (quadratic_unit_le_covarianceMax _ _ hv))
    (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ r).le)

theorem D_upper (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin q → ℝ) (hσ : ∀ r, 0 < σ r) :
    D K C σ ≤ ∑ r, Paper35.gaussianRankCoefficient (K r) / σ r * Real.sqrt (covarianceMax (C r)) := by
  by_cases hs : ({v : Space d | ‖v‖=1} : Set (Space d)).Nonempty
  · apply csSup_le (hs.image _)
    rintro x ⟨v,hv,rfl⟩
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (quadratic_unit_le_covarianceMax _ _ hv))
      (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ r).le)
  · rw [D, not_nonempty_iff_eq_empty.mp hs, image_empty, Real.sSup_empty]
    exact Finset.sum_nonneg (fun r _ => mul_nonneg
      (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ r).le) (Real.sqrt_nonneg _))

theorem D_lower (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin q → ℝ) (hC : ∀ r, (C r).PosSemidef) (hσ : ∀ r, 0 < σ r)
    (j : Fin q) (hj : 0 < covarianceMax (C j)) :
    Paper35.gaussianRankCoefficient (K j) / σ j * Real.sqrt (covarianceMax (C j)) ≤ D K C σ := by
  obtain ⟨v,hv,he⟩ := covarianceMax_eigenvector (C j) (hC j) hj
  have hquad : quadratic (C j) v = covarianceMax (C j) := by
    rw [quadratic_eq_inner, he, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    simp
  apply le_trans ?_ (le_csSup (D_bddAbove K C σ hσ) ⟨v,hv,rfl⟩)
  rw [← hquad]
  change _ ≤ ∑ r, Paper35.gaussianRankCoefficient (K r) / σ r * Real.sqrt (quadratic (C r) v)
  exact Finset.single_le_sum (f := fun r => Paper35.gaussianRankCoefficient (K r) / σ r *
    Real.sqrt (quadratic (C r) v)) (fun r _ => mul_nonneg
    (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ r).le) (Real.sqrt_nonneg _))
    (Finset.mem_univ j)

lemma D_nonneg (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin q → ℝ) (hσ : ∀ r, 0 < σ r) : 0 ≤ D K C σ := by
  by_cases hs : ({v : Space d | ‖v‖=1} : Set (Space d)).Nonempty
  · obtain ⟨v,hv⟩ := hs
    exact (Finset.sum_nonneg (fun r _ => mul_nonneg
      (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) (hσ r).le) (Real.sqrt_nonneg _))).trans
      (le_csSup (D_bddAbove K C σ hσ) ⟨v,hv,rfl⟩)
  · rw [D, not_nonempty_iff_eq_empty.mp hs, image_empty, Real.sSup_empty]

lemma covarianceOperator_sum (C : Fin q → Matrix (Fin d) (Fin d) ℝ) :
    covarianceOperator (∑ r, C r) = ∑ r, covarianceOperator (C r) := by
  ext v i
  simp [covarianceOperator, Matrix.toEuclideanLin_apply]

lemma covarianceOperator_smul (a : ℝ) (C : Matrix (Fin d) (Fin d) ℝ) :
    covarianceOperator (a • C) = a • covarianceOperator C := by
  ext v i
  simp [covarianceOperator, Matrix.toEuclideanLin_apply]

lemma covarianceMax_sum_upper (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (a : Fin q → ℝ) (ha : ∀ r, 0 ≤ a r) :
    covarianceMax (∑ r, a r • C r) ≤ ∑ r, a r * covarianceMax (C r) := by
  unfold covarianceMax
  rw [covarianceOperator_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  rw [covarianceOperator_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha r)]

lemma quadratic_sum (C : Fin q → Matrix (Fin d) (Fin d) ℝ) (a : Fin q → ℝ) (v : Space d) :
    quadratic (∑ r, a r • C r) v = ∑ r, a r * quadratic (C r) v := by
  simp [quadratic, covarianceForm, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul]

lemma covarianceMax_sum_lower (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ r, (C r).PosSemidef) (a : Fin q → ℝ) (ha : ∀ r, 0 ≤ a r)
    (j : Fin q) (hj : 0 < covarianceMax (C j)) :
    a j * covarianceMax (C j) ≤ covarianceMax (∑ r, a r • C r) := by
  obtain ⟨v,hv,he⟩ := covarianceMax_eigenvector (C j) (hC j) hj
  have hquad : quadratic (C j) v = covarianceMax (C j) := by
    rw [quadratic_eq_inner, he, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    simp
  apply le_trans ?_ (quadratic_unit_le_covarianceMax _ v hv)
  rw [quadratic_sum, ← hquad]
  exact Finset.single_le_sum (fun r _ => mul_nonneg (ha r) (quadratic_nonneg _ (hC r) v))
    (Finset.mem_univ j)

theorem A_upper (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ) :
    A K C ≤ Real.sqrt (∑ r, gaussianLengthCorrection (K r) * covarianceMax (C r)) :=
  Real.sqrt_le_sqrt (covarianceMax_sum_upper C (fun r => gaussianLengthCorrection (K r))
    (fun r => (by norm_num : (0 : ℝ) ≤ 1).trans (gaussianLengthCorrection_ge_one _)))

theorem A_lower (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ r, (C r).PosSemidef) (j : Fin q) (hj : 0 < covarianceMax (C j)) :
    Real.sqrt (gaussianLengthCorrection (K j) * covarianceMax (C j)) ≤ A K C :=
  Real.sqrt_le_sqrt (covarianceMax_sum_lower C hC (fun r => gaussianLengthCorrection (K r))
    (fun r => (by norm_num : (0 : ℝ) ≤ 1).trans (gaussianLengthCorrection_ge_one _)) j hj)

lemma A_nonneg (K : Fin q → ℕ) (C : Fin q → Matrix (Fin d) (Fin d) ℝ) : 0 ≤ A K C :=
  Real.sqrt_nonneg _

end Paper35.GaussianFactors
