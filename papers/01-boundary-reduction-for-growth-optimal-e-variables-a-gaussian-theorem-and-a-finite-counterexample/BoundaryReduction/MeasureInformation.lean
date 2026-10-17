import BoundaryReduction.ExtendedLog
import BoundaryReduction.FiniteKL

open Real Set MeasureTheory InformationTheory BigOperators
open scoped Classical ENNReal NNReal
namespace BoundaryReduction.MeasureGrow

variable {α ι : Type*} [MeasurableSpace α]

/-- The maximin growth rate, using the actual extended logarithmic expectation. -/
noncomputable def growth (P₀ : Measure α) (P : ι → Measure α) : EReal :=
  ⨆ S : MeasureEVar P₀, ⨅ i : ι, logExpectation (P i) S.value

/-- A finite convex combination of members of a statistical family. -/
structure FiniteMixture (P : ι → Measure α) where
  index : Type
  finite : Fintype index
  weights : @BoundaryReduction.FinProb index finite
  parameter : index → ι

attribute [instance] FiniteMixture.finite

noncomputable def FiniteMixture.measure {P : ι → Measure α} (F : FiniteMixture P) : Measure α :=
  ∑ i, ENNReal.ofReal (F.weights.w i) • P (F.parameter i)

instance {P : ι → Measure α} [∀ i, IsProbabilityMeasure (P i)] (F : FiniteMixture P) :
    IsProbabilityMeasure F.measure where
  measure_univ := by
    simp only [FiniteMixture.measure, Measure.finset_sum_apply, MeasurableSet.univ,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => F.weights.nonneg i), F.weights.sum_eq_one]
    norm_num

noncomputable def information (P₀ : Measure α) (P : ι → Measure α) : ℝ≥0∞ :=
  sInf {x | ∃ F : FiniteMixture P, x = klDiv F.measure P₀}

lemma exists_le_average {κ : Type*} [Fintype κ] (w : BoundaryReduction.FinProb κ)
    (f : κ → ℝ) : ∃ i, f i ≤ ∑ j, w.w j*f j := by
  by_contra hh
  have hf : ∀ i, (∑ j, w.w j*f j) < f i := by simpa using hh
  have hp : ∃ i, 0 < w.w i := by
    by_contra hn
    push_neg at hn
    have hz : ∀ i, w.w i = 0 := fun i => le_antisymm (by simpa using hn i) (w.nonneg i)
    have hs := w.sum_eq_one
    simp [hz] at hs
  obtain ⟨i,hi⟩ := hp
  have hsum := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hf j).le (w.nonneg j))
    ⟨i,Finset.mem_univ _,mul_lt_mul_of_pos_left (hf i) hi⟩
  rw [← Finset.sum_mul, w.sum_eq_one, one_mul] at hsum
  exact (lt_irrefl _ hsum)

/-- Finite-mixture form of the general information upper bound. The only
statistical hypothesis is finiteness of the actual component and mixture KL. -/
theorem worst_logExpectation_le_mixture {P₀ : Measure α} [IsProbabilityMeasure P₀]
    {P : ι → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    (S : MeasureEVar P₀) (F : FiniteMixture P)
    (hcomponent : ∀ i, klDiv (P i) P₀ ≠ ∞) (hF : klDiv F.measure P₀ ≠ ∞) :
    (⨅ i : ι, logExpectation (P i) S.value) ≤ (↑(klDiv F.measure P₀) : EReal) := by
  by_cases hg : ∀ i : F.index, (∀ᵐ x ∂P (F.parameter i), S.value x ≠ 0) ∧
      Integrable (fun x => log (S.value x)) (P (F.parameter i))
  · have hi (i : F.index) : Integrable (fun x => log (S.value x))
        (ENNReal.ofReal (F.weights.w i) • P (F.parameter i)) :=
      (hg i).2.smul_measure ENNReal.ofReal_ne_top
    have hlog : Integrable (fun x => log (S.value x)) F.measure :=
      integrable_finset_sum_measure.mpr (fun i _ => hi i)
    have hz : ∀ᵐ x ∂F.measure, S.value x ≠ 0 := by
      have hset : MeasurableSet {x | S.value x = 0} := S.measurable (measurableSet_singleton 0)
      have hzcomp (i : F.index) : P (F.parameter i) {x | S.value x = 0} = 0 := by
        simpa only [ae_iff, not_not] using (hg i).1
      rw [ae_iff]
      simp only [not_not]
      simp [FiniteMixture.measure, Measure.finset_sum_apply, hzcomp]
    have havg : (∫ x, log (S.value x) ∂F.measure) =
        ∑ i, F.weights.w i*(∫ x, log (S.value x) ∂P (F.parameter i)) := by
      rw [FiniteMixture.measure, integral_finset_sum_measure (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_smul_measure, ENNReal.toReal_ofReal (F.weights.nonneg i)]
      rfl
    obtain ⟨i,hiavg⟩ := exists_le_average F.weights (fun i => ∫ x, log (S.value x) ∂P (F.parameter i))
    have hbound := evar_integral_log_bound S hF hz hlog
    rw [havg] at hbound
    apply le_trans (iInf_le _ (F.parameter i))
    rw [logExpectation_eq_integral (hg i).1 (hg i).2, ← EReal.coe_ennreal_toReal hF]
    exact_mod_cast hiavg.trans hbound
  · obtain ⟨i,hi⟩ := not_forall.mp hg
    apply le_trans (iInf_le _ (F.parameter i))
    rw [logExpectation_eq_bot S.measurable
      (integrable_posLog S.measurable S.nonneg S.integrable (hcomponent (F.parameter i))) hi]
    exact bot_le

lemma le_information_of_le_mixtures {P₀ : Measure α} {P : ι → Measure α} {x : EReal}
    (h : ∀ F : FiniteMixture P, x ≤ (↑(klDiv F.measure P₀) : EReal)) :
    x ≤ (↑(information P₀ P) : EReal) := by
  by_cases hx : x ≤ 0
  · exact hx.trans (EReal.coe_ennreal_nonneg _)
  · have hn : 0 ≤ x := (lt_of_not_ge hx).le
    have hxmem : x ∈ Set.range ((↑) : ℝ≥0∞ → EReal) := by
      rw [EReal.range_coe_ennreal]
      exact hn
    obtain ⟨a,rfl⟩ := hxmem
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    apply le_sInf
    rintro a ⟨F,rfl⟩
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp (h F)

/-- Measure-theoretic information upper bound for every family whose finite
mixtures have finite relative entropy. Zero e-variables are included. -/
theorem growth_le_information {P₀ : Measure α} [IsProbabilityMeasure P₀]
    {P : ι → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    (hcomponent : ∀ i, klDiv (P i) P₀ ≠ ∞)
    (hfinite : ∀ F : FiniteMixture P, klDiv F.measure P₀ ≠ ∞) :
    growth P₀ P ≤ (↑(information P₀ P) : EReal) := by
  apply iSup_le
  intro S
  apply le_information_of_le_mixtures
  intro F
  exact worst_logExpectation_le_mixture S F hcomponent (hfinite F)

end BoundaryReduction.MeasureGrow
