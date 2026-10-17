import Paper06.VanishingFamily
import Mathlib.Topology.Instances.EReal.Lemmas

open Real Filter Asymptotics
open scoped Topology

namespace Paper06

/-- The paper's floor sample size is a legitimate marginal at every n. -/
theorem asymptoticSampleSize_le (n : ℕ) : asymptoticSampleSize n ≤ n := by
  by_cases hn : n = 0
  · subst n
    norm_num [asymptoticSampleSize]
  · have hs := asymptoticSampleSize_sq_le (Nat.one_le_iff_ne_zero.mpr hn)
    nlinarith

/-- Even extension sizes are cofinal, so the even-size limit filter is nontrivial. -/
theorem even_extension_sizes_cofinal :
    Tendsto (fun m : ℕ => (⟨2 * m, m, by omega⟩ : {n : ℕ // Even n})) atTop
      (Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop) := by
  apply Filter.tendsto_comap_iff.mpr
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  change b ≤ 2 * n
  omega

theorem even_extension_filter_neBot :
    (Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop).NeBot :=
  even_extension_sizes_cofinal.neBot

/-- Actual optimal feasible error of the paper's matching family.  The
domain consists of the even extension sizes appearing in the source. -/
noncomputable def paperOptimalError (θ : ℝ) (n : {n : ℕ // Even n}) : EReal :=
  constrainedError (paperMatchingAdmissible θ n.val n.property).law
    (paperMatchingAdmissible θ n.val n.property).slice (asymptoticSampleSize n.val)
    (asymptoticSampleSize_le n.val)

/-- The original optimum itself tends to zero through even n; this is the
explicit connection of equation (18) with the scale limit in equation (17). -/
theorem paperOptimalError_tendsto_zero {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    Tendsto (paperOptimalError θ)
      (Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop) (𝓝 (0 : EReal)) := by
  let l := Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop
  have hn : Tendsto (Subtype.val : {n : ℕ // Even n} → ℕ) l atTop :=
    Filter.tendsto_comap
  have hscale : Tendsto
      (fun n : {n : ℕ // Even n} =>
        ((asymptoticScale (paperAlphabet θ) n.val / 2 : ℝ) : EReal)) l (𝓝 0) := by
    have hr := ((equation17 hθhalf).2.div_const (2 : ℝ)).comp hn
    simpa only [zero_div, EReal.coe_zero, Function.comp_def] using (EReal.tendsto_coe.mpr hr)
  have hnonneg : ∀ᶠ n : {n : ℕ // Even n} in l, 0 ≤ paperOptimalError θ n := by
    exact Filter.Eventually.of_forall (fun n => constrainedError_nonneg _ _ _ _)
  have hupp : ∀ᶠ n : {n : ℕ // Even n} in l, paperOptimalError θ n ≤
      ((asymptoticScale (paperAlphabet θ) n.val / 2 : ℝ) : EReal) := by
    filter_upwards [hn.eventually (equation18 hθ hθhalf)] with n hn'
    obtain ⟨hk, _, hmiddle, hupper⟩ := hn' n.property
    exact hmiddle.trans hupper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale hnonneg hupp

/-- The same actual-error zero limit in the ordinary order filter on even
extension sizes, so it can be quoted without a filter conversion. -/
theorem paperOptimalError_tendsto_zero_atTop {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    Tendsto (paperOptimalError θ) atTop (𝓝 (0 : EReal)) := by
  have hv : Tendsto (Subtype.val : {n : ℕ // Even n} → ℕ) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (⟨2 * b, b, by omega⟩ : {n : ℕ // Even n})] with n hn
    change 2 * b ≤ n.val at hn
    change b ≤ n.val
    omega
  have hi : Tendsto (id : {n : ℕ // Even n} → {n : ℕ // Even n}) atTop
      (Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop) :=
    Filter.tendsto_comap_iff.mpr hv
  exact (paperOptimalError_tendsto_zero hθ hθhalf).comp hi

/-- The concrete d_n=Theta(n^8) example in the introduction has actual
optimal feasible relative-entropy error tending to zero. -/
theorem concrete_optimal_error_tendsto_zero :
    Tendsto (paperOptimalError (1 / 4))
      (Filter.comap (Subtype.val : {n : ℕ // Even n} → ℕ) atTop) (𝓝 (0 : EReal)) :=
  paperOptimalError_tendsto_zero (by norm_num) (by norm_num)

end Paper06
