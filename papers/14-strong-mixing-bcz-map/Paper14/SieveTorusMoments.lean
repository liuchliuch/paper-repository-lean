import Paper14.SieveResidueCount
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Set Function Finset Filter
open scoped ENNReal
namespace Paper14
noncomputable section

/-- Haar probability on the actual period-M circle. -/
def sieveCircleProb (M : ℕ) [Fact (0 < (M : ℝ))] : Measure (AddCircle (M : ℝ)) :=
  (ENNReal.ofReal (M : ℝ))⁻¹ • volume

instance sieveCircleProb_probability (M : ℕ) [hM : Fact (0 < (M : ℝ))] :
    IsProbabilityMeasure (sieveCircleProb M) := by
  constructor
  simp only [sieveCircleProb,Measure.smul_apply,smul_eq_mul,AddCircle.measure_univ]
  exact ENNReal.inv_mul_cancel (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hM.out)) ENNReal.ofReal_ne_top

instance sieveCircleProb_haar (M : ℕ) [hM : Fact (0 < (M : ℝ))] :
    (sieveCircleProb M).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hM.out)))

def sieveTorusSingle (M : ℕ) (q : ℕ) (ε : ℝ) :
    AddCircle (M : ℝ) × AddCircle (M : ℝ) → ℝ := fun z =>
  (sieveCircleSingle M (q : ℤ) ε ((q : ℤ) • z.1-z.2) : ℝ)

lemma measurable_sieveTorusSingle (M : ℕ) [Fact (0 < (M : ℝ))] (q : ℕ) (ε : ℝ) :
    Measurable (sieveTorusSingle M q ε) := by
  unfold sieveTorusSingle
  have harg : Measurable (fun z : AddCircle (M : ℝ) × AddCircle (M : ℝ) => (q : ℤ) • z.1-z.2) := by fun_prop
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    ((measurable_sieveCircleSingle M (q : ℤ) ε).comp harg)

lemma sieveTorusSingle_mem_Icc (M : ℕ) [Fact (0 < (M : ℝ))] (q : ℕ) (ε : ℝ) (z : AddCircle (M : ℝ) × AddCircle (M : ℝ)) :
    sieveTorusSingle M q ε z ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have h := sieveSingle_le_one M (q : ℤ) ε
    ((AddCircle.equivIco (M : ℝ) 0 ((q : ℤ) • z.1-z.2) : Ico 0 (0+(M : ℝ))) : ℝ)
  have heq := (AddCircle.equivIco (M : ℝ) 0).symm_apply_apply ((q : ℤ) • z.1-z.2)
  change (((AddCircle.equivIco (M : ℝ) 0 ((q : ℤ) • z.1-z.2) : Ico 0 (0+(M : ℝ))) : ℝ) : AddCircle (M : ℝ)) = _ at heq
  rw [← sieveCircleSingle_coe,heq] at h
  unfold sieveTorusSingle
  exact_mod_cast h

lemma sieveTorusSingle_memLp (M : ℕ) [Fact (0 < (M : ℝ))] (q : ℕ) (ε : ℝ) :
    MemLp (sieveTorusSingle M q ε) 2 ((sieveCircleProb M).prod (sieveCircleProb M)) :=
  memLp_of_bounded (Eventually.of_forall (sieveTorusSingle_mem_Icc M q ε))
    (measurable_sieveTorusSingle M q ε).aestronglyMeasurable 2

lemma integral_sieveCircleSingle {M : ℕ} [hMp : Fact (0 < (M : ℝ))]
    (hM : Squarefree M) (q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u, (sieveCircleSingle M (q : ℤ) ε u : ℝ) ∂sieveCircleProb M) = ε*varrho M q := by
  rw [sieveCircleProb,integral_smul_measure]
  have hperiod := AddCircle.integral_preimage (M : ℝ) 0
    (fun u => (sieveCircleSingle M (q : ℤ) ε u : ℝ))
  simp only [zero_add,sieveCircleSingle_coe] at hperiod
  rw [← hperiod,integral_sieveSingle_period_eq hM q hε0 hε1]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hMp.out.le,smul_eq_mul]
  field_simp [hMp.out.ne']

lemma integral_sieveTorusSingle {M : ℕ} [Fact (0 < (M : ℝ))]
    (hM : Squarefree M) (q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z, sieveTorusSingle M q ε z ∂(sieveCircleProb M).prod (sieveCircleProb M)) = ε*varrho M q := by
  have hmp := (measurePreserving_fst (μ := sieveCircleProb M) (ν := sieveCircleProb M)).comp
    (sieveTorus_measurePreserving (sieveCircleProb M) (q := (q : ℤ)) (q' := (q : ℤ)+1) (by omega))
  have hf : Measurable (fun u => (sieveCircleSingle M (q : ℤ) ε u : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (measurable_sieveCircleSingle M (q : ℤ) ε)
  have hh := integral_map (μ := (sieveCircleProb M).prod (sieveCircleProb M))
    hmp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmp.map_eq] at hh
  exact hh.symm.trans (integral_sieveCircleSingle hM q hε0 hε1)

lemma sieveTorusSingle_independent (M : ℕ) [Fact (0 < (M : ℝ))]
    {q q' : ℕ} (hqq : q ≠ q') (ε : ℝ) :
    IndepFun (sieveTorusSingle M q ε) (sieveTorusSingle M q' ε)
      ((sieveCircleProb M).prod (sieveCircleProb M)) := by
  exact (sieve_indicators_independent M (sieveCircleProb M)
    (q := (q : ℤ)) (q' := (q' : ℤ)) (by exact_mod_cast hqq) ε).comp
      (measurable_of_countable (fun n : ℕ => (n : ℝ))) (measurable_of_countable (fun n : ℕ => (n : ℝ)))

/-- The actual torus sum corresponding to G_M. -/
def sieveTorusCount (M Q : ℕ) (ε : ℝ) :=
  ∑ q ∈ Finset.range Q, sieveTorusSingle M (q+1) ε

/-- Actual expectation in (16), for the original finite-sieve indicators. -/
theorem integral_sieveTorusCount {M : ℕ} [Fact (0 < (M : ℝ))]
    (hM : Squarefree M) (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ z, sieveTorusCount M Q ε z ∂(sieveCircleProb M).prod (sieveCircleProb M)) = betaN M Q ε := by
  simp only [sieveTorusCount,Finset.sum_apply]
  rw [integral_finset_sum]
  · simp_rw [integral_sieveTorusSingle hM _ hε0 hε1]
    exact (Finset.mul_sum ..).symm
  · intro q hq
    exact (sieveTorusSingle_memLp M (q+1) ε).integrable (by norm_num)

/-- Actual variance bound in (16), proved from Haar pairwise independence
and the fact that the original single-q variables lie between zero and one. -/
theorem variance_sieveTorusCount {M : ℕ} [Fact (0 < (M : ℝ))]
    (hM : Squarefree M) (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    variance (sieveTorusCount M Q ε) ((sieveCircleProb M).prod (sieveCircleProb M)) ≤ betaN M Q ε := by
  rw [sieveTorusCount,IndepFun.variance_sum]
  · rw [betaN,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hv := variance_le_expectation_sq (sieveTorusSingle_memLp M (q+1) ε).aestronglyMeasurable
    apply hv.trans
    rw [← integral_sieveTorusSingle hM (q+1) hε0 hε1]
    apply integral_mono (sieveTorusSingle_memLp M (q+1) ε).integrable_sq
      ((sieveTorusSingle_memLp M (q+1) ε).integrable (by norm_num))
    intro z
    obtain ⟨hz0,hz1⟩ := sieveTorusSingle_mem_Icc M (q+1) ε z
    change (sieveTorusSingle M (q+1) ε z)^2 ≤ sieveTorusSingle M (q+1) ε z
    nlinarith
  · intro q hq
    exact sieveTorusSingle_memLp M (q+1) ε
  · intro q hq q' hq' hne
    exact sieveTorusSingle_independent M (by omega) ε

end
end Paper14
