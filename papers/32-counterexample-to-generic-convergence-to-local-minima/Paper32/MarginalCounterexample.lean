import Paper32.NoiseConsequences
import Paper32.VariationalBridge

open Set Filter Topology MeasureTheory ProbabilityTheory
namespace Paper32

/-- The insufficiency assertion of Remark 4.3 has an actual one-step witness.
The marginal noise law is absolutely continuous and misses N; a pre-noise oracle
that observes that noise can still cancel it exactly using a true Clarke value.
Thus marginal nullity does not imply the required conditional-hit condition. -/
theorem marginal_nullity_does_not_imply_conditional_avoidance :
    ∃ μ : Measure Point, IsProbabilityMeasure μ ∧ μ ≪ volume ∧ μ singularArrangement=0 ∧
      ∀ᵐ ν ∂μ, |ν.1| ≤ 1/100 ∧ |ν.2| ≤ 1/100 ∧
        (-ν) ∈ clarkeSubdiff F 0 ∧
        (0-(1:ℝ) • ((-ν)+ν) : Point) ∈ singularArrangement := by
  let μ := uniformDiskLaw (1/100)
  have hprob : IsProbabilityMeasure μ := uniformDiskLaw_isProbability (by norm_num)
  have hac : μ ≪ volume := uniformDiskLaw_absolutelyContinuous _
  refine ⟨μ,hprob,hac,hac volume_singularArrangement,?_⟩
  have hmem : ∀ᵐ ν ∂μ, ν ∈ euclideanDisk (1/100) :=
    ae_cond_mem (measurableSet_euclideanDisk _)
  filter_upwards [hmem] with ν hν
  have hb := euclideanDisk_coordinate_bounds (by norm_num) hν
  refine ⟨hb.1,hb.2,?_,?_⟩
  · rw [clarke_F_zero,← clarke_g_zero]
    apply rectangle_subset_clarke_g_zero
    · simpa only [Prod.fst_neg,abs_neg] using hb.1.trans (by norm_num : (1/100:ℝ) ≤ 1)
    · simpa only [Prod.snd_neg,abs_neg] using hb.2.trans (by norm_num : (1/100:ℝ) ≤ 2)
  · simp [singularArrangement]

end Paper32
