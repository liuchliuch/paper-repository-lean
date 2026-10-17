import Paper26.MetricAmplification
import Mathlib.Probability.Moments.SubGaussian

/-! Independent-batch amplification in Proposition 5.5, using mathlib's
proved Hoeffding lemma and sum tail bound. No concentration inequality is
assumed as an external input. -/
noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable

namespace Paper26.IndependentAmplification
open MetricAmplification
variable {α Ω : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  [BorelSpace α] [SecondCountableTopology α] [MeasurableSpace Ω]
  {l : ℕ} [NeZero l] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Failure indicator of one actual output. -/
def failure (R : α) (u : ℝ) (x : α) : ℝ := if u < dist x R then 1 else 0

theorem measurable_failure (R : α) (u : ℝ) : Measurable (failure R u) := by
  unfold failure
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_id.dist measurable_const))
    measurable_const measurable_const

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
theorem failure_mem_Icc (R : α) (u : ℝ) (x : α) : failure R u x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold failure
  split <;> norm_num

omit [IsProbabilityMeasure μ] in
theorem failure_integral (X : Ω → α) (hX : Measurable X) (R : α) (u : ℝ) :
    (∫ ω, failure R u (X ω) ∂μ) = μ.real {ω | u < dist (X ω) R} := by
  have hs : MeasurableSet {ω | u < dist (X ω) R} :=
    measurableSet_lt measurable_const (hX.dist measurable_const)
  have heq : (fun ω => failure R u (X ω)) =
      Set.indicator {ω | u < dist (X ω) R} (fun _ => (1 : ℝ)) := by
    ext ω
    simp [failure, Set.indicator]
  rw [heq]
  exact integral_indicator_one hs

omit [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] in
/-- A failed selection forces at least half of the batch indicators to fail. -/
theorem half_le_failures (X : Fin l → α) (R : α) (u : ℝ)
    (hbad : 3 * u < dist (select X u) R) :
    (l : ℝ) / 2 ≤ ∑ i : Fin l, failure R u (X i) := by
  have hn : ¬ l < 2 * (good X R u).card := by
    intro h
    exact (not_lt_of_ge (selection_error X R u h)) hbad
  have hcount : (∑ i : Fin l, failure R u (X i)) =
      ((Finset.univ.filter fun i : Fin l => u < dist (X i) R).card : ℝ) := by
    simp [failure]
  have htotal : (good X R u).card +
      (Finset.univ.filter fun i : Fin l => u < dist (X i) R).card = l := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.univ) (fun i : Fin l => dist (X i) R ≤ u)
    simpa [good, not_le] using h
  rw [hcount]
  have hnR : 2 * ((good X R u).card : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.le_of_not_gt hn
  have htR : ((good X R u).card : ℝ) +
      ((Finset.univ.filter fun i : Fin l => u < dist (X i) R).card : ℝ) = l := by
    exact_mod_cast htotal
  linarith

/-- With independent batches and individual failure at most `1/4`, the
actual selected output has failure probability at most `exp(-l/8)`. -/
theorem failure_probability_le (X : Fin l → Ω → α)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (R : α) (u : ℝ)
    (hbatch : ∀ i, μ.real {ω | u < dist (X i ω) R} ≤ 1 / 4) :
    μ.real {ω | 3 * u < dist (select (fun i => X i ω) u) R} ≤
      Real.exp (-(l : ℝ) / 8) := by
  let F : Fin l → Ω → ℝ := fun i ω => failure R u (X i ω)
  let p : Fin l → ℝ := fun i => ∫ ω, F i ω ∂μ
  let Z : Fin l → Ω → ℝ := fun i ω => F i ω - p i
  have hF (i : Fin l) : Measurable (F i) := (measurable_failure R u).comp (hX i)
  have hp (i : Fin l) : p i ≤ 1 / 4 := by
    simpa only [p, F, failure_integral (X i) (hX i) R u] using hbatch i
  have hindZ : iIndepFun Z μ := by
    exact hind.comp (fun i x => failure R u x - p i)
      (fun i => (measurable_failure R u).sub_const _)
  have hsub (i : Fin l) : HasSubgaussianMGF (Z i) (1 / 4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := F i) (a := (0 : ℝ)) (b := 1) (hF i).aemeasurable
      (ae_of_all _ fun ω => failure_mem_Icc R u (X i ω))
    convert h using 1
    norm_num [Z, p]
  have hpSum : (∑ i : Fin l, p i) ≤ (l : ℝ) / 4 := by
    calc
      _ ≤ ∑ _i : Fin l, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => hp i
      _ = _ := by simp; ring
  have hsubset : {ω | 3 * u < dist (select (fun i => X i ω) u) R} ⊆
      {ω | (l : ℝ) / 4 ≤ ∑ i : Fin l, Z i ω} := by
    intro ω hω
    have hhalf := half_le_failures (fun i => X i ω) R u hω
    have heq : (∑ i : Fin l, Z i ω) =
        (∑ i : Fin l, F i ω) - ∑ i : Fin l, p i := by simp only [Z, Finset.sum_sub_distrib]
    change (l : ℝ) / 4 ≤ ∑ i : Fin l, Z i ω
    rw [heq]
    change (l : ℝ) / 4 ≤ (∑ i : Fin l, failure R u (X i ω)) - ∑ i : Fin l, p i
    linarith
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindZ
    (s := Finset.univ) (c := fun _ : Fin l => (1 / 4 : ℝ≥0))
    (fun i _ => hsub i) (ε := (l : ℝ) / 4) (by positivity)
  have hl : (l : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne l

  calc
    _ ≤ μ.real {ω | (l : ℝ) / 4 ≤ ∑ i : Fin l, Z i ω} := measureReal_mono hsubset
    _ ≤ _ := by
      convert htail using 1
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
      ring

/-- An explicit batch count gives the requested confidence. -/
theorem failure_probability_le_beta (X : Fin l → Ω → α)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (R : α) (u β : ℝ)
    (hbatch : ∀ i, μ.real {ω | u < dist (X i ω) R} ≤ 1 / 4)
    (hβ : 0 < β) (hl : 8 * Real.log (1 / β) ≤ (l : ℝ)) :
    μ.real {ω | 3 * u < dist (select (fun i => X i ω) u) R} ≤ β := by
  apply (failure_probability_le X hX hind R u hbatch).trans
  rw [← Real.exp_log hβ]
  apply Real.exp_le_exp.2
  rw [Real.log_div (by norm_num) hβ.ne', Real.log_one] at hl
  linarith

end Paper26.IndependentAmplification
