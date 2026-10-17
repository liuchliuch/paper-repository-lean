import Paper14.ReturnGeometry
import Paper14.RoofMean
import Paper14.MeasureBCZ
import Paper14.GraphMeasures
import Paper14.Background.Birkhoff

/-! Paper (4): the changing-section probability limit, from ergodicity. -/
open MeasureTheory Measure Filter Topology Set
namespace Paper14
noncomputable section

lemma measurable_tau : Measurable tau := by unfold tau; fun_prop

lemma measurable_H (n : ℕ) : Measurable (H n) := by
  unfold H
  exact Finset.measurable_sum _ (fun i _ => measurable_tau.comp (measurable_B.iterate i))

lemma measurable_Hr (r : ℝ) (n : ℕ) : Measurable (Hr r n) := by
  have hj : Measurable (fun p : ℕ × (ℝ × ℝ) => H p.1 p.2) :=
    measurable_from_prod_countable_right measurable_H
  exact hj.comp ((measurable_Rn measurable_B (measurableSet_Yr r) n).prodMk measurable_id)

/-- The usual fixed-section Birkhoff limit, with the actual roof integral. -/
theorem roof_birkhoff_ae (hB : Ergodic B m) :
    ∀ᵐ x ∂m, Tendsto (fun n : ℕ => H n x / n) atTop (𝓝 (Real.pi^2 / 3)) := by
  filter_upwards [Background.tendsto_birkhoffAverage_ae_integral hB integrable_tau] with x hx
  simpa only [birkhoffAverage,birkhoffSum,H,smul_eq_mul,div_eq_mul_inv,mul_comm,integral_tau] using hx

/-- The pullback of the changing-section roof converges in probability.
The only unproved BCZ input is ergodicity, stated explicitly. -/
theorem changing_roof_pullback (hB : Ergodic B m) (r : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop, 0 < r n ∧ r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) :
    TendstoInMeasure m (fun n x => Hr (r n) n (phiR (r n) x) / n) atTop
      (fun _ => Real.pi^2 / 3) := by
  have hscale : Tendsto (fun n : ℕ => (r n)⁻¹^2) atTop (𝓝 1) := by
    simpa using (hlim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).pow 2
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact ((measurable_Hr (r n) n).comp (measurable_phiR (r n))).div_const (n : ℝ) |>.aestronglyMeasurable
  · filter_upwards [ae_mem_Omega,roof_birkhoff_ae hB] with x hx hroof
    have heq : (fun n : ℕ => Hr (r n) n (phiR (r n) x) / n) =ᶠ[atTop]
        (fun n => (r n)⁻¹^2 * (H n x / n)) := by
      filter_upwards [hr] with n hn
      rw [phiR_time_scaling hn.1 hn.2 n x hx]
      ring
    apply (tendsto_congr' heq).mpr
    simpa only [one_mul] using hscale.mul hroof

/-- The source changing-section probability statement (4), with the moving
normalized measure `mr (r n)` rather than a surrogate under a fixed measure. -/
theorem changing_roof_probability (hB : Ergodic B m) (r : ℕ → ℝ)
    (hr : ∀ᶠ n : ℕ in atTop, 0 < r n ∧ r n < 1)
    (hlim : Tendsto r atTop (𝓝 1)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => mr (r n) {y | ε ≤ |Hr (r n) n y / n - Real.pi^2 / 3|})
      atTop (𝓝 0) := by
  have hp := tendstoInMeasure_iff_dist.mp (changing_roof_pullback hB r hr hlim) ε hε
  simp only [Real.dist_eq] at hp
  have heq : (fun n : ℕ => mr (r n) {y | ε ≤ |Hr (r n) n y / n - Real.pi^2 / 3|}) =ᶠ[atTop]
      (fun n => m {x | ε ≤ |Hr (r n) n (phiR (r n) x) / n - Real.pi^2 / 3|}) := by
    filter_upwards [hr] with n hn
    have hs : MeasurableSet {y | ε ≤ |Hr (r n) n y / n - Real.pi^2 / 3|} :=
      measurableSet_le measurable_const (continuous_abs.measurable.comp (((measurable_Hr (r n) n).div_const _).sub_const _))
    exact ((measurePreserving_phiR (r n) hn.1 hn.2).measure_preimage hs.nullMeasurableSet).symm
  exact (tendsto_congr' heq).mpr hp

end
end Paper14
