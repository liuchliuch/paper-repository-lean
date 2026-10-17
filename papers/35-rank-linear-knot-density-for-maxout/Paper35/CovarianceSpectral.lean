import Paper35.Covariance
import Paper35.Heterogeneous
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Paper35.Source.WeightedModel
variable {d : ℕ}

/-- The actual tilted covariance, pulled back from the dual by the Riesz
isometry. This chooses no coordinate basis and retains the original covariance. -/
def covarianceForm (m : WeightedModel d) : Space d →L[ℝ] Space d →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (covarianceBilinDual m.tilted) (innerSL ℝ) (innerSL ℝ)

/-- Invariant spectral norm of the actual positive semidefinite covariance
form, equivalently the largest eigenvalue of its self-adjoint Riesz operator. -/
def covarianceSpectralNorm (m : WeightedModel d) : ℝ := ‖m.covarianceForm‖

lemma covarianceSpectralNorm_nonneg (m : WeightedModel d) : 0 ≤ m.covarianceSpectralNorm :=
  norm_nonneg m.covarianceForm

lemma projectedVariance_le_covarianceSpectralNorm (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u : Space d) :
    m.projectedVariance u ≤ m.covarianceSpectralNorm * ‖u‖^2 := by
  let C := m.covarianceForm
  have heq : m.projectedVariance u = C u u := by
    simp only [C, covarianceForm, ContinuousLinearMap.bilinearComp_apply]
    rw [projectedVariance_eq_variance, covarianceBilinDual_self_eq_variance hW]
    rfl
  rw [heq]
  calc
    _ ≤ ‖C u u‖ := le_abs_self _
    _ ≤ ‖C‖*‖u‖*‖u‖ := C.le_opNorm₂ _ _
    _ = _ := by change ‖C‖*‖u‖*‖u‖ = ‖C‖*‖u‖^2; ring

lemma projectedVariance_le_spectral_of_norm_le_one (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u : Space d) (hu : ‖u‖ ≤ 1) :
    m.projectedVariance u ≤ m.covarianceSpectralNorm := by
  apply (m.projectedVariance_le_covarianceSpectralNorm hW u).trans
  have hn : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  exact (mul_le_mul_of_nonneg_left hn (m.covarianceSpectralNorm_nonneg)).trans_eq (mul_one _)

/-- Actual expected path-averaged switch density. -/
def expectedDensity (m : WeightedModel d) (K : ℕ) (p : Probe d) : ℝ≥0∞ :=
  ∫⁻ θ, switchDensity (scores p θ) p.length ∂m.iid K

lemma expectedDensity_eq (m : WeightedModel d) (K : ℕ) (p : Probe d) :
    m.expectedDensity K p = m.expectedCount K p / ENNReal.ofReal p.length := by
  unfold expectedDensity expectedCount expectedSwitchCount switchDensity
  simp only [div_eq_mul_inv]
  exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr p.length_pos).ne')

/-- The full spectral consequence (2.8), expressed through the invariant
largest PSD covariance norm. The count estimate is the proved source
covariance theorem; integration, arclength-speed control and division are
proved here. In the constant-envelope case tilted=weights and average=B. -/
theorem expectedDensity_le_spectral (hcov : WeightedCovarianceClaim (d := d))
    (m : WeightedModel d) (hW : MemLp (fun w => w) 2 m.tilted)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤
      ((K : ℝ≥0∞)*m.average/ENNReal.ofReal (Real.sqrt 3)) *
        ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm) := by
  have hint : (∫⁻ s in Icc 0 p.length,
      ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s)))) ≤
      ENNReal.ofReal p.length * ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    calc
      _ ≤ ∫⁻ s in Ioo 0 p.length, ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro s hs
        exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt
          (m.projectedVariance_le_spectral_of_norm_le_one hW _ (Paper35.Heterogeneous.probe_speed_le_one p hs)))
      _ = _ := by simp [Real.volume_Ioo, mul_comm]
  have hb := (hcov m hW K hK p).trans (mul_le_mul_left' hint _)
  rw [m.expectedDensity_eq]
  calc
    _ ≤ (((K : ℝ≥0∞)*m.average/ENNReal.ofReal (Real.sqrt 3)) *
        (ENNReal.ofReal p.length * ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm))) /
          ENNReal.ofReal p.length := by
      simpa only [div_eq_mul_inv] using mul_le_mul_right' hb (ENNReal.ofReal p.length)⁻¹
    _ = _ := by
      rw [div_eq_mul_inv]
      have hL : ENNReal.ofReal p.length ≠ 0 := (ENNReal.ofReal_pos.mpr p.length_pos).ne'
      calc
        _ = (((K : ℝ≥0∞)*m.average/ENNReal.ofReal (Real.sqrt 3)) *
            ENNReal.ofReal (Real.sqrt m.covarianceSpectralNorm)) *
              (ENNReal.ofReal p.length * (ENNReal.ofReal p.length)⁻¹) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hL ENNReal.ofReal_ne_top, mul_one]

end Paper35.Source.WeightedModel
