import Paper35.CovarianceSpectral
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! The iid-coordinate specialization uses independence and a common variance;
no density of the weight law is needed for this upper bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Paper35.Source.WeightedModel
variable {d : ℕ}

/-- Every linear projection of independent finite-variance coordinates has
variance equal to the sum of its coordinate variances. -/
theorem variance_inner_of_independent_coordinates (μ : Measure (Space d))
    (hind : iIndepFun (fun (i : Fin d) (w : Space d) => w i) μ)
    (hW : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 μ)
    (u : Space d) :
    variance (fun w => inner ℝ u w) μ =
      ∑ i : Fin d, (u i)^2 * variance (fun w : Space d => w i) μ := by
  let X : Fin d → Space d → ℝ := fun i w => u i * w i
  have hX (i : Fin d) : MemLp (X i) 2 μ := (hW i).const_mul (u i)
  have hi : Set.Pairwise (↑(Finset.univ : Finset (Fin d)))
      (fun i j => IndepFun (X i) (X j) μ) := by
    intro i _ j _ hij
    exact (hind.indepFun hij).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have h := IndepFun.variance_sum (s := Finset.univ) (X := X) (fun i _ => hX i) hi
  have heq : (fun w : Space d => inner ℝ u w) = ∑ i : Fin d, X i := by
    funext w
    simp only [Finset.sum_apply, X, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, mul_comm]
  rw [heq, h]
  apply Finset.sum_congr rfl
  intro i _
  exact variance_mul (u i) (fun w : Space d => w i) μ

/-- Common coordinate variance gives exactly the isotropic covariance
quadratic form, independently of the coordinate means. -/
theorem variance_inner_of_common_variance (μ : Measure (Space d))
    (hind : iIndepFun (fun (i : Fin d) (w : Space d) => w i) μ)
    (hW : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 μ)
    (σ : ℝ) (hvar : ∀ i : Fin d, variance (fun w : Space d => w i) μ = σ^2)
    (u : Space d) : variance (fun w => inner ℝ u w) μ = σ^2 * ‖u‖^2 := by
  rw [variance_inner_of_independent_coordinates μ hind hW u]
  simp_rw [hvar]
  rw [← Finset.sum_mul]
  have hn : (∑ i : Fin d, (u i)^2) = ‖u‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two]
  rw [hn, mul_comm]

/-- A constant envelope restores the original weight law; independence and
common coordinate variance then identify the actual source covariance. -/
theorem projectedVariance_of_constant_independent_coordinates
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hind : iIndepFun (fun (i : Fin d) (w : Space d) => w i) m.weights)
    (hW : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 m.weights)
    (σ : ℝ) (hvar : ∀ i : Fin d, variance (fun w : Space d => w i) m.weights = σ^2)
    (u : Space d) : m.projectedVariance u = σ^2 * ‖u‖^2 := by
  rw [m.projectedVariance_eq_variance, m.tilted_eq_weights_of_constant B hb]
  exact variance_inner_of_common_variance m.weights hind hW σ hvar u

/-- Corollary 2.5 upper bound for every admissible iid-coordinate law, without
assuming a particular uniform construction or a density for the weights. -/
theorem expectedDensity_le_iid_coordinates
    (hcov : WeightedCovarianceClaim (d := d))
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hind : iIndepFun (fun (i : Fin d) (w : Space d) => w i) m.weights)
    (hW : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 m.weights)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hvar : ∀ i : Fin d, variance (fun w : Space d => w i) m.weights = σ^2)
    (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedDensity K p ≤
      ((K : ℝ≥0∞) * (B : ℝ≥0∞) / ENNReal.ofReal (Real.sqrt 3)) * ENNReal.ofReal σ := by
  have hvec : MemLp (fun w : Space d => w) 2 m.tilted := by
    rw [m.tilted_eq_weights_of_constant B hb]
    exact memLp_piLp_iff.mpr hW
  have hp (u : Space d) (hu : ‖u‖ ≤ 1) : m.projectedVariance u ≤ σ^2 := by
    rw [m.projectedVariance_of_constant_independent_coordinates B hb hind hW σ hvar]
    have hn : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
    exact (mul_le_mul_of_nonneg_left hn (sq_nonneg σ)).trans_eq (mul_one _)
  have hint : (∫⁻ s in Icc 0 p.length,
      ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s)))) ≤
        ENNReal.ofReal p.length * ENNReal.ofReal σ := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    calc
      _ ≤ ∫⁻ s in Ioo 0 p.length, ENNReal.ofReal σ := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro s hs
        apply ENNReal.ofReal_le_ofReal
        simpa only [Real.sqrt_sq hσ] using Real.sqrt_le_sqrt
          (hp (deriv p.curve s) (Paper35.Heterogeneous.probe_speed_le_one p hs))
      _ = _ := by simp [Real.volume_Ioo, mul_comm]
  have hc := (hcov m hvec K hK p).trans (mul_le_mul_left' hint _)
  rw [m.average_eq_of_constant B hb] at hc
  rw [m.expectedDensity_eq]
  calc
    _ ≤ (((K : ℝ≥0∞) * (B : ℝ≥0∞) / ENNReal.ofReal (Real.sqrt 3)) *
        (ENNReal.ofReal p.length * ENNReal.ofReal σ)) / ENNReal.ofReal p.length :=
      ENNReal.div_le_div_right hc _
    _ = _ := by
      rw [div_eq_mul_inv]
      have hL : ENNReal.ofReal p.length ≠ 0 := (ENNReal.ofReal_pos.mpr p.length_pos).ne'
      calc
        _ = (((K : ℝ≥0∞) * (B : ℝ≥0∞) / ENNReal.ofReal (Real.sqrt 3)) *
            ENNReal.ofReal σ) * (ENNReal.ofReal p.length * (ENNReal.ofReal p.length)⁻¹) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hL ENNReal.ofReal_ne_top, mul_one]

end Paper35.Source.WeightedModel
