import Paper14.SelfInduction
import Paper14.MeasureOmega
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! Paper S2.p7: near-identity convergence, with the actual one-sided filter. -/
open MeasureTheory Filter Topology Set
namespace Paper14

instance : IsProbabilityMeasure m where
  measure_univ := by
    simp only [m, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, volume_Omega]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

lemma ae_mem_Omega : ∀ᵐ x ∂m, x ∈ Omega := by
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Omega) 2

lemma measurable_phiR (r : ℝ) : Measurable (phiR r) := by
  unfold phiR phiJ
  fun_prop

lemma measurable_phiRInv (r : ℝ) : Measurable (phiRInv r) := by
  unfold phiRInv
  fun_prop

/-- At every point of the section the conjugacy converges from the left to `id`.
The floor is eventually zero because the point lies strictly above `a+b=1`. -/
theorem phiR_tendsto_pointwise {x : ℝ × ℝ} (hx : x ∈ Omega) :
    Tendsto (fun r : ℝ => phiR r x) (𝓝[<] (1 : ℝ)) (𝓝 x) := by
  have hpos : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hinv : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa using ((continuousAt_id.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
      nhdsWithin_le_nhds)
  have hsum : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r⁻¹ < x.1 + x.2 :=
    hinv.eventually (Iio_mem_nhds hx.2.2.2.2)
  have heq : (fun r : ℝ => phiR r x) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r => (r * x.1, r * x.2)) := by
    filter_upwards [hpos, self_mem_nhdsWithin, hsum] with r hr hr1 hs
    exact phiR_eq_smul_of_sum hr hr1 hx hs
  apply (tendsto_congr' heq).mpr
  have hc : Continuous (fun r : ℝ => (r * x.1, r * x.2)) := by fun_prop
  simpa using (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))

/-- Lemma 2: convergence in measure, deduced from the pointwise convergence
on the full-measure Farey triangle. -/
theorem phiR_tendstoInMeasure : Lemma2ConvergenceStatement := by
  intro ε hε
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro r hr
  have hseq : TendstoInMeasure m (fun n => phiR (r n)) atTop id := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (measurable_phiR (r n)).aestronglyMeasurable
    · filter_upwards [ae_mem_Omega] with x hx
      exact (phiR_tendsto_pointwise hx).comp hr
  exact hseq ε hε

end Paper14
