import Paper28.NormFoldings
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Native comparisons between the actual Hilbert chord and round angle.
The local comparison has arbitrarily small multiplicative loss; it will be
combined with the proved differential bound before quotient descent. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Metric
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem angular_eq_two_arcsin_chord (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angular u v = 2 * Real.arcsin (‖u-v‖/2) := by
  have hd0 : 0 ≤ ‖u-v‖/2 := by positivity
  have hd1 : ‖u-v‖/2 ≤ 1 := by
    have h := norm_sub_le u v
    rw [hu,hv] at h
    linarith
  have hsq : ‖u-v‖^2 = 2-2*inner ℝ u v := by
    rw [norm_sub_sq_real,hu,hv]
    ring
  unfold angular
  apply Real.arccos_eq_of_eq_cos
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr hd0)
  · linarith [Real.arcsin_le_pi_div_two (‖u-v‖/2)]
  · rw [Real.cos_two_mul,Real.cos_arcsin,Real.sq_sqrt (by nlinarith : 0 ≤ 1-(‖u-v‖/2)^2)]
    nlinarith

theorem chord_le_angular (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u-v‖ ≤ angular u v := by
  rw [angular_eq_two_arcsin_chord u v hu hv]
  have hd0 : 0 ≤ ‖u-v‖/2 := by positivity
  have hd1 : ‖u-v‖/2 ≤ 1 := by
    have h := norm_sub_le u v
    rw [hu,hv] at h
    linarith
  have h := Real.sin_le (Real.arcsin_nonneg.mpr hd0)
  rw [Real.sin_arcsin (by linarith) hd1] at h
  linarith

theorem two_arcsin_half_hasStrictDerivAt :
    HasStrictDerivAt (fun d : ℝ => 2*Real.arcsin (d/2)) 1 0 := by
  have hhalf : HasStrictDerivAt (fun d : ℝ => d/2) (1/2) 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℝ)).div_const 2
  have ha : HasStrictDerivAt Real.arcsin 1 ((fun d : ℝ => d/2) 0) := by
    simpa using Real.hasStrictDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have h := (ha.comp 0 hhalf).const_mul 2
  simpa using h

/-- The ratio between angle and chord tends to one at the diagonal, proved
from the actual derivative of arcsine rather than assumed as metric data. -/
theorem exists_angular_le_mul_chord (k : ℝ) (hk : 1 < k) :
    ∃ r : ℝ, 0 < r ∧ ∀ u v : H, ‖u‖ = 1 → ‖v‖ = 1 → ‖u-v‖ < r →
      angular u v ≤ k*‖u-v‖ := by
  let K : NNReal := ⟨k,by linarith⟩
  let D : ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ)
  have hK : ‖D‖₊ < K := by
    simpa [D,K] using hk
  have hf : HasStrictFDerivAt (fun d : ℝ => 2*Real.arcsin (d/2)) D 0 :=
    two_arcsin_half_hasStrictDerivAt.hasStrictFDerivAt
  obtain ⟨s,hs,hLip⟩ := hf.exists_lipschitzOnWith_of_nnnorm_lt K hK
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r,hr,?_⟩
  intro u v hu hv hd
  have hdS : ‖u-v‖ ∈ s := hrs (by simpa [Real.dist_eq] using hd)
  have h0S : (0 : ℝ) ∈ s := hrs (by simpa using hr)
  have h := hLip.dist_le_mul ‖u-v‖ hdS 0 h0S
  rw [angular_eq_two_arcsin_chord u v hu hv]
  have hnonneg : 0 ≤ 2*Real.arcsin (‖u-v‖/2) :=
    mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by positivity))
  simpa only [zero_div,Real.arcsin_zero,mul_zero,Real.dist_eq,sub_zero,
    abs_of_nonneg hnonneg,abs_norm,K] using h

end Paper28
