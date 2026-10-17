import Paper14.PrimitiveVoidProof
import Paper14.PrimitiveReturns
import Paper14.ChangingSectionBirkhoff
import Paper14.CompactSelfInduction
import Paper14.LimitComponentBounds

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

def bczScale (n : ℕ) (α : ℝ) : ℝ := 1-α/(n : ℝ)

lemma bczScale_tendsto (α : ℝ) : Tendsto (fun n => bczScale n α) atTop (𝓝 1) := by
  simpa only [bczScale,sub_zero] using tendsto_alpha_div_nat.const_sub 1

lemma bczScale_lt_one {α : ℝ} (hα : 0 < α) : ∀ᶠ n : ℕ in atTop, bczScale n α < 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [bczScale]
  linarith [div_pos hα hn0]

lemma bczScale_tendsto_left {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n => bczScale n α) atTop (𝓝[<] (1 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨bczScale_tendsto α,bczScale_lt_one hα⟩

lemma bczScale_eventually {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ)/3 < bczScale n α ∧ bczScale n α < 1 :=
  ((bczScale_tendsto α).eventually (Ioi_mem_nhds (by norm_num))).and (bczScale_lt_one hα)

lemma bczScale_section_mass_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n => m.real (Yr (bczScale n α))) atTop (𝓝 1) := by
  apply (tendsto_congr' ?_).mpr (scale_rho_tendsto_one hα)
  filter_upwards [bczScale_eventually hα] with n hn
  rw [Measure.real,m_Yr (by linarith [hn.1]) hn.2,ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

lemma bcz_excess_moment : ExcessMomentBound (fun n α => (bczScale n α)^2) := by
  intro α hα
  refine ⟨scale_rho_tendsto_one hα,?_⟩
  simpa only [bczScale,Real.rpow_two] using scale_moment_bound hα

lemma bcz_short_roof_tendsto_zero (hB : Ergodic B m) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => mr (bczScale n α) {y | Hr (bczScale n α) n y ≤ 3*(n : ℝ)}) atTop (𝓝 0) := by
  let δ : ℝ := Real.pi^2/3-3
  have hδ : 0 < δ := sub_pos.mpr pi_sq_div_three_gt_three
  have hmass := changing_roof_probability hB (fun n => bczScale n α)
    ((bczScale_eventually hα).mono (fun n hn => ⟨by linarith [hn.1],hn.2⟩))
    (bczScale_tendsto α) δ hδ
  have hle : ∀ᶠ n : ℕ in atTop,
      mr (bczScale n α) {y | Hr (bczScale n α) n y ≤ 3*(n : ℝ)} ≤
      mr (bczScale n α) {y | δ ≤ |Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3|} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply measure_mono
    intro y hy
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : Hr (bczScale n α) n y/(n : ℝ) ≤ 3 := (div_le_iff₀ hn0).mpr hy
    have hab := neg_le_abs (Hr (bczScale n α) n y/(n : ℝ)-Real.pi^2/3)
    dsimp only [mem_setOf_eq,δ]
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmass
    (Eventually.of_forall (fun _ => zero_le _)) hle

/-- The original zero-excess hypothesis (iii)/(46), from the fully proved
primitive void lemma and the actual changing-section Birkhoff limit.
The ergodicity input is explicit until the weak-mixing proposition closes. -/
theorem bcz_zeroExcessSmall (hB : Ergodic B m) :
    ZeroExcessSmall B m (fun n α => Yr (bczScale n α)) (fun n α => (bczScale n α)^2) := by
  intro ε hε
  obtain ⟨α0,hα0⟩ := Lemma5 (ε/4) (by positivity)
  refine ⟨max α0 0,?_⟩
  intro α hαbig
  have hα : 0 < α := lt_of_le_of_lt (le_max_right α0 0) hαbig
  obtain ⟨Nz,hNz⟩ := hα0 α (lt_of_le_of_lt (le_max_left α0 0) hαbig)
  have hz : ∀ᶠ n : ℕ in atTop, m {x | ZCount n α x = 0} ≤ ENNReal.ofReal (ε/4) :=
    (eventually_ge_atTop Nz).mono (fun n hn => hNz n hn)
  have hroof : ∀ᶠ n : ℕ in atTop, mr (bczScale n α) {y | Hr (bczScale n α) n y ≤ 3*(n : ℝ)} ≤ ENNReal.ofReal (ε/2) :=
    ((bcz_short_roof_tendsto_zero hB hα).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < ε/2)))).mono (fun _ h => h.le)
  have hrec := reciprocalSectionMass_tendsto m (fun n => Yr (bczScale n α)) (bczScale_section_mass_tendsto hα)
  have hr2 : ∀ᶠ n in atTop, reciprocalSectionMass m (Yr (bczScale n α)) ≤ 2 :=
    (hrec.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ≥0) < 2))).mono (fun _ h => h.le)
  apply Filter.eventually_atTop.mp
  filter_upwards [hz,hroof,hr2,bczScale_eventually hα,eventually_gt_atTop (0 : ℕ)] with n hzn hroofn hrecn hrn hn
  have hr0 : 0 < bczScale n α := by linarith [hrn.1]
  have hp : 0 < m (Yr (bczScale n α)) := by rw [m_Yr hr0 hrn.2]; exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr0)
  have hc2 : (m (Yr (bczScale n α)))⁻¹ ≤ (2 : ℝ≥0∞) := by
    rw [← reciprocalSectionMass_coe hp]
    exact ENNReal.coe_le_coe.mpr hrecn
  have hdom : mr (bczScale n α) ≤ (2 : ℝ≥0∞) • m := by
    rw [mr_eq_normalizedRestriction hr0 hrn.2,normalizedRestriction]
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply,smul_eq_mul]
    exact (mul_le_mul_left' (Measure.restrict_le_self A) _).trans (mul_le_mul_right' hc2 (m A))
  have hεn : α/(n : ℝ) < 1 := by dsimp [bczScale] at hr0; linarith
  rw [← mr_eq_normalizedRestriction hr0 hrn.2]
  have hset := zero_excess_subset_void_or_short_roof hn hεn hrn.1 hrn.2
  calc
    _ ≤ mr (bczScale n α) ({x | ZCount n α x = 0} ∪ {x | Hr (bczScale n α) n x ≤ 3*(n : ℝ)}) := measure_mono hset
    _ ≤ mr (bczScale n α) {x | ZCount n α x = 0}+mr (bczScale n α) {x | Hr (bczScale n α) n x ≤ 3*(n : ℝ)} := measure_union_le _ _
    _ ≤ (2 : ℝ≥0∞)*m {x | ZCount n α x = 0}+ENNReal.ofReal (ε/2) := by
      apply add_le_add _ hroofn
      simpa only [Measure.smul_apply,smul_eq_mul] using hdom {x | ZCount n α x = 0}
    _ ≤ (2 : ℝ≥0∞)*ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/2) := add_le_add_right (mul_le_mul_left' hzn 2) _
    _ = ENNReal.ofReal ε := by
      calc
        _ = ENNReal.ofReal (2*(ε/4))+ENNReal.ofReal (ε/2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
        _ = ENNReal.ofReal (2*(ε/4)+ε/2) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ = _ := congrArg ENNReal.ofReal (by ring)

end
end Paper14
