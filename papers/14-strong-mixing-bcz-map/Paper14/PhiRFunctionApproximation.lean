import Paper14.BCZExcessHypotheses
import Paper14.BoundedProductLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma mr_le_four {r : ℝ} (hr : (2 : ℝ)/3<r) (hr1 : r<1) : mr r ≤ (4 : ℝ≥0) • m := by
  have hr0 : 0<r := by linarith
  have hmass : (1/4 : ℝ≥0∞) ≤ m (Yr r) := by
    rw [m_Yr hr0 hr1]
    calc
      (1/4 : ℝ≥0∞) = ENNReal.ofReal (1/4 : ℝ) := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal (r^2) := ENNReal.ofReal_le_ofReal (by nlinarith : (1/4 : ℝ) ≤ r^2)
  have hc : (m (Yr r))⁻¹ ≤ (4 : ℝ≥0∞) := by
    have hh := ENNReal.inv_le_inv' hmass
    norm_num at hh
    exact hh
  rw [mr_eq_normalizedRestriction hr0 hr1,normalizedRestriction]
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact (mul_le_mul_left' (Measure.restrict_le_self A) _).trans
    (mul_le_mul_right' hc (m A))

lemma integral_phiR_le_four {r : ℝ} (hr : (2 : ℝ)/3<r) (hr1 : r<1)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) (hfi : Integrable f m) (hf0 : ∀ x,0≤f x) :
    (∫ x,f (phiR r x) ∂m) ≤ 4*∫ x,f x ∂m := by
  have hr0 : 0<r := by linarith
  have hm : Measure.map (phiR r) m=mr r := (measurePreserving_phiR r hr0 hr1).map_eq
  have hmap := integral_map (μ := m) (measurable_phiR r).aemeasurable hf.aestronglyMeasurable
  rw [hm] at hmap
  rw [← hmap]
  calc
    _ ≤ ∫ x,f x ∂((4 : ℝ≥0) • m) :=
      integral_mono_measure (mr_le_four hr hr1) (Eventually.of_forall hf0) (hfi.smul_measure ENNReal.coe_ne_top)
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

lemma bounded_continuous_phiR_error (g : (ℝ × ℝ) →ᵇ ℂ) {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => ∫ x,‖g (phiR (bczScale n α) x)-g x‖ ∂m) atTop (𝓝 0) := by
  have hbound (n : ℕ) (x : ℝ × ℝ) : ‖‖g (phiR (bczScale n α) x)-g x‖‖ ≤ 2*‖g‖ := by
    change ‖‖g (phiR (bczScale n α) x)-g x‖‖ ≤ 2*‖g‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [g.norm_coe_le_norm (phiR (bczScale n α) x),g.norm_coe_le_norm x])
  have hpoint : ∀ᵐ x ∂m,Tendsto (fun n : ℕ => ‖g (phiR (bczScale n α) x)-g x‖) atTop (𝓝 0) := by
    filter_upwards [ae_mem_Omega] with x hx
    have ht : Tendsto (fun n : ℕ => g (phiR (bczScale n α) x)) atTop (𝓝 (g x)) := g.continuous.continuousAt.tendsto.comp ((phiR_tendsto_pointwise hx).comp (bczScale_tendsto_left hα))
    simpa only [sub_self,norm_zero] using (ht.sub (tendsto_const_nhds (x := g x))).norm
  have ht := tendsto_integral_of_dominated_convergence (fun _ : ℝ × ℝ => 2*‖g‖)
    (fun n => (((g.continuous.measurable.comp (measurable_phiR (bczScale n α))).sub g.continuous.measurable).norm).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hbound n)) hpoint
  simpa only [integral_zero] using ht

/-- Pullback by the actual self-induction converges for every bounded measurable complex function. -/
theorem bounded_phiR_L1_error {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => ∫ x,‖f (phiR (bczScale n α) x)-f x‖ ∂m) atTop (𝓝 0) := by
  have hfi : Integrable f m := Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hb)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g,hg,_⟩ := hfi.exists_boundedContinuous_integral_sub_le (show 0<ε/20 by positivity)
  let e : ℝ × ℝ → ℝ := fun x => ‖f x-g x‖
  have he : Measurable e := (hf.sub g.continuous.measurable).norm
  have hei : Integrable e m := (hfi.sub (g.integrable m)).norm
  have hi (n : ℕ) : Integrable (fun x => e (phiR (bczScale n α) x)) m := by
    apply integrable_of_measurable_bound (he.comp (measurable_phiR _)) (1+‖g‖)
    intro x
    change ‖‖f (phiR (bczScale n α) x)-g (phiR (bczScale n α) x)‖‖ ≤ 1+‖g‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add (hb _) (g.norm_coe_le_norm _))
  have hgi (n : ℕ) : Integrable (fun x => ‖g (phiR (bczScale n α) x)-g x‖) m := by
    apply integrable_of_measurable_bound
      (((g.continuous.measurable.comp (measurable_phiR _)).sub g.continuous.measurable).norm) (2*‖g‖)
    intro x
    change ‖‖g (phiR (bczScale n α) x)-g x‖‖ ≤ 2*‖g‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [g.norm_coe_le_norm (phiR (bczScale n α) x),g.norm_coe_le_norm x])
  have hfn (n : ℕ) : Integrable (fun x => ‖f (phiR (bczScale n α) x)-f x‖) m := by
    apply integrable_of_measurable_bound (((hf.comp (measurable_phiR _)).sub hf).norm) 2
    intro x
    change ‖‖f (phiR (bczScale n α) x)-f x‖‖ ≤ 2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb (phiR (bczScale n α) x),hb x])
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp ((bounded_continuous_phiR_error g hα).eventually
    (Iio_mem_nhds (show (0 : ℝ)<ε/2 by positivity)))
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (bczScale_eventually hα)
  refine ⟨max N M,fun n hn => ?_⟩
  have hr := hM n ((le_max_right N M).trans hn)
  have hc := integral_phiR_le_four hr.1 hr.2 he hei (fun x => norm_nonneg _)
  have hupper : (∫ x,‖f (phiR (bczScale n α) x)-f x‖ ∂m) ≤
      (∫ x,e (phiR (bczScale n α) x) ∂m)+
      (∫ x,‖g (phiR (bczScale n α) x)-g x‖ ∂m)+(∫ x,e x ∂m) := by
    rw [← integral_add' (hi n) (hgi n),← integral_add' ((hi n).add (hgi n)) hei]
    apply integral_mono (hfn n) (((hi n).add (hgi n)).add hei)
    intro x
    change ‖f (phiR (bczScale n α) x)-f x‖ ≤ e (phiR (bczScale n α) x)+‖g (phiR (bczScale n α) x)-g x‖+e x
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (f (phiR (bczScale n α) x)) (g (phiR (bczScale n α) x)) (f x)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (g (phiR (bczScale n α) x)) (g x) (f x)
    dsimp [e]
    rw [norm_sub_rev (g x) (f x)] at h₂
    linarith
  have hsmall := hN n ((le_max_left N M).trans hn)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  change (∫ x,e x ∂m)≤ε/20 at hg
  linarith

/-- For the normalized eigenfunction, the actual pullback error also tends to zero in L2. -/
theorem bounded_phiR_L2_sq_error {f : ℝ × ℝ → ℂ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1)
    {α : ℝ} (hα : 0<α) :
    Tendsto (fun n : ℕ => ∫ x,‖f (phiR (bczScale n α) x)-f x‖^2 ∂m) atTop (𝓝 0) := by
  have hbound (n : ℕ) (x : ℝ × ℝ) : ‖f (phiR (bczScale n α) x)-f x‖≤2 :=
    (norm_sub_le _ _).trans (by nlinarith [hb (phiR (bczScale n α) x),hb x])
  have hmeas (n : ℕ) : Measurable (fun x => ‖f (phiR (bczScale n α) x)-f x‖) :=
    ((hf.comp (measurable_phiR _)).sub hf).norm
  have hI (n : ℕ) : Integrable (fun x => ‖f (phiR (bczScale n α) x)-f x‖) m := by
    apply integrable_of_measurable_bound (hmeas n) 2
    intro x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbound n x
  have hI2 (n : ℕ) : Integrable (fun x => ‖f (phiR (bczScale n α) x)-f x‖^2) m := by
    apply integrable_of_measurable_bound ((hmeas n).pow_const 2) 4
    intro x
    change ‖‖f (phiR (bczScale n α) x)-f x‖^2‖≤4
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hbound n x,norm_nonneg (f (phiR (bczScale n α) x)-f x)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => 2*(∫ x,‖f (phiR (bczScale n α) x)-f x‖ ∂m)) atTop (𝓝 0) by
      simpa using (bounded_phiR_L1_error hf hb hα).const_mul 2)
    (fun n => integral_nonneg (fun x => sq_nonneg _))
  intro n
  change (∫ x,‖f (phiR (bczScale n α) x)-f x‖^2 ∂m) ≤ 2*(∫ x,‖f (phiR (bczScale n α) x)-f x‖ ∂m)
  rw [← integral_const_mul]
  apply integral_mono (hI2 n) ((hI n).const_mul 2)
  intro x
  nlinarith [hbound n x,norm_nonneg (f (phiR (bczScale n α) x)-f x)]

end
end Paper14
