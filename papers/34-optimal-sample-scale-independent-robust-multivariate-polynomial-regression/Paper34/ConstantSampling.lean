import Paper34.StandardConcentration
import Paper34.AppendixSpaces
import Paper34.GoodGrid
import Paper34.SourceComplexity

/-!
# Appendix A.1: constant regression under independent corruptions

The estimator is the actual native degree-zero polynomial returned by
`AppendixSpaces.constantEstimator`, using a median of the observed indexed
labels. Locations and their law play no role in its error analysis. The only
probabilistic theorem input is the already declared general
`BernoulliSubsetHoeffdingInput`, applied to the deterministic full index set.
No good-majority or recovery probability is an input.
-/

namespace Paper34.ConstantSampling

noncomputable section

open Set MeasureTheory

/-- All uncorrupted indexed observations, preserving multiplicities. -/
def goodIndices {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) : Finset (Fin M) :=
  Finset.univ.filter (fun i => S.O i ω = false)

/-- The actual event that fewer than half of the entire batch are corrupted. -/
def majorityEvent {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : Set Ω :=
  {ω | 2 * boolCount (fun i => S.O i ω) Finset.univ < (M : ℝ)}

theorem measurableSet_majorityEvent
    {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : MeasurableSet (majorityEvent S) := by
  have ho : Measurable (fun ω i => S.O i ω) := measurable_pi_lambda _ S.measurable_O
  have hc : Measurable (fun ω => boolCount (fun i => S.O i ω) Finset.univ) :=
    (measurable_of_finite (fun b : Fin M → Bool => boolCount b Finset.univ)).comp ho
  exact measurableSet_lt (measurable_const.mul hc) measurable_const

theorem majorityEvent_good_card
    {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {ω : Ω} (hω : ω ∈ majorityEvent S) :
    M < 2 * (goodIndices S ω).card := by
  classical
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin M))) (fun i => S.O i ω = true)
  have hneg : (Finset.univ.filter (fun i => ¬ S.O i ω = true)) = goodIndices S ω := by
    ext i
    simp only [goodIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    cases S.O i ω <;> simp
  rw [hneg, Finset.card_univ, Fintype.card_fin] at hpartition
  change 2 * (((Finset.univ.filter (fun i => S.O i ω = true)).card : ℕ) : ℝ) < (M : ℝ) at hω
  have hbad : 2 * (Finset.univ.filter (fun i => S.O i ω = true)).card < M := by
    exact_mod_cast hω
  omega

/-- The real majority-failure event is bounded using the original independent
Bernoulli hypotheses and individual rate bounds in the sampling model. -/
theorem majority_failure_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hM : 0 < M) (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) :
    P.real (majorityEvent S)ᶜ ≤ Real.exp (-2 * (alpha rho - rho) ^ 2 * (M : ℝ)) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have ha : alpha rho < 1 / 2 := by unfold alpha; linarith
  have hsub : (majorityEvent S)ᶜ ⊆
      {ω | alpha rho * ((Finset.univ : Finset (Fin M)).card : ℝ) <
        boolCount (fun i => S.O i ω) Finset.univ} := by
    intro ω hω
    have hbad : (M : ℝ) ≤ 2 * boolCount (fun i => S.O i ω) Finset.univ :=
      le_of_not_gt hω
    change alpha rho * ((Finset.univ : Finset (Fin M)).card : ℝ) < _
    simp only [Finset.card_univ, Fintype.card_fin]
    have hstrict := mul_lt_mul_of_pos_right ha hm
    nlinarith
  have ht := hHoeffding S.O S.measurable_O S.independent_O rho (alpha rho)
    hr0 (by unfold alpha; linarith) S.outlier_rate Finset.univ
  simpa only [Finset.card_univ, Fintype.card_fin] using (measureReal_mono hsub).trans ht

/-- The prescribed threshold implies a nonempty batch, with no degree assumption. -/
theorem constant_samples_positive {M : ℕ} {rho delta : ℝ}
    (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ)) : 0 < M := by
  have hgap : 0 < 1 - 2 * rho := by linarith
  have hC : 0 < gridConcentrationConstant rho := by unfold gridConcentrationConstant; positivity
  have harg : 1 < (2 : ℝ) / delta := (lt_div_iff₀ hdelta).2 (by linarith)
  have hraw := mul_pos hC (Real.log_pos harg)
  exact_mod_cast hraw.trans_le hM

/-- Source Appendix A.1's explicit majority probability from the same
`16/(1-2*rho)^2` threshold; no location concentration is used. -/
theorem majority_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ)) :
    1 - delta ≤ P.real (majorityEvent S) := by
  have hMpos := constant_samples_positive hr hdelta hdelta1 hM
  have ht := majority_failure_tail S hHoeffding hMpos hr0 hr
  have hexponent := (grid_sample_bound_exponents (K := 1) (M := M) (pmin := 1) (p := 1)
    (by norm_num) hr0 hr hdelta hdelta1 (by norm_num) le_rfl (by simpa using hM)).2
  have hsmall : Real.exp (-2 * (alpha rho - rho) ^ 2 * (M : ℝ)) ≤
      Real.exp (-(alpha rho - rho) ^ 2 * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg (alpha rho - rho)) (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hbound : Real.exp (-(alpha rho - rho) ^ 2 * (M : ℝ)) ≤
      Real.exp (-Real.log (2 / delta)) := by
    simpa only [Nat.cast_one, mul_one, inv_one] using hexponent
  have he : Real.exp (-Real.log (2 / delta)) = delta / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 / delta), inv_div]
  have htail : P.real (majorityEvent S)ᶜ ≤ delta := by
    have hh := ht.trans (hsmall.trans hbound)
    rw [he] at hh
    linarith
  have hpartition := measureReal_add_measureReal_compl (μ := P) (measurableSet_majorityEvent S)
  have hu : P.real Set.univ = 1 := by simp
  linarith

/-- On the actual majority event the native median constant estimator has
the sharp sigma error, for all permissible labels and arbitrary locations. -/
theorem constant_estimator_error_on_majority
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n M : ℕ} {rho sigma : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hM : 0 < M) (p : PolynomialSpace n 0)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω - polyEval p (S.X i ω)| ≤ sigma)
    {ω : Ω} (hω : ω ∈ majorityEvent S) :
    supNorm (AppendixSpaces.constantEstimator n M hM (fun i => Y i ω) - p) ≤ sigma := by
  apply AppendixSpaces.degree_zero_minimizer_error hM (fun i => S.X i ω) (fun i => Y i ω)
    p _ (goodIndices S ω) (majorityEvent_good_card S hω)
  · intro i hi
    exact hnoise ω i (Finset.mem_filter.mp hi).2
  · exact AppendixSpaces.constantEstimator_minimizes hM (fun i => S.X i ω) (fun i => Y i ω)

/-- The degree-zero statistical guarantee is independent of `hd ≥ 1`, of
the design law, and of the location values. Labels may be adversarial and
nonmeasurable, as in the main source statistical formulation. -/
theorem appendix_A_1_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho sigma delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ))
    (p : PolynomialSpace n 0) (_hs : 0 ≤ sigma)
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω - polyEval p (S.X i ω)| ≤ sigma) :
    1 - delta ≤ P.real {ω | supNorm
      (AppendixSpaces.constantEstimator n M (constant_samples_positive hr hdelta hdelta1 hM)
        (fun i => Y i ω) - p) ≤ sigma} := by
  refine (majority_probability S (StandardConcentration.bernoulliSubsetHoeffdingInput P _) hr0 hr hdelta hdelta1 hM).trans
    (measureReal_mono ?_ (measure_ne_top P _))
  intro ω hω
  exact constant_estimator_error_on_majority S Y _ p hnoise hω

/-- At zero noise the very same observed-median estimator is the true native
constant polynomial, with the same success probability and sample threshold. -/
theorem appendix_A_1_exact_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho delta : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hr0 : 0 ≤ rho) (hr : rho < 1 / 2) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hM : gridConcentrationConstant rho * Real.log (2 / delta) ≤ (M : ℝ))
    (p : PolynomialSpace n 0)
    (hnoise : ∀ ω i, S.O i ω = false → Y i ω = polyEval p (S.X i ω)) :
    1 - delta ≤ P.real {ω |
      AppendixSpaces.constantEstimator n M (constant_samples_positive hr hdelta hdelta1 hM)
        (fun i => Y i ω) = p} := by
  have hprob := appendix_A_1_probability S Y hr0 hr hdelta hdelta1 hM p
    (sigma := 0) le_rfl (fun ω i hi => by simp [hnoise ω i hi])
  apply hprob.trans (measureReal_mono _)
  intro ω hω
  change supNorm (_ - p) ≤ 0 at hω
  rw [← norm_eq_supNorm] at hω
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hω (norm_nonneg _)))

/-- A prescribed integer batch size for the constant estimator. -/
def constantSampleCount (rho delta : ℝ) : ℕ :=
  Nat.ceil (gridConcentrationConstant rho * Real.log (2 / delta))

theorem constantSampleCount_threshold (rho delta : ℝ) :
    gridConcentrationConstant rho * Real.log (2 / delta) ≤
      (constantSampleCount rho delta : ℝ) := Nat.le_ceil _

theorem constantSampleCount_pos {rho delta : ℝ} (hr : rho < 1 / 2)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) : 0 < constantSampleCount rho delta :=
  constant_samples_positive hr hdelta hdelta1 (constantSampleCount_threshold rho delta)

/-- The appendix's `O_rho(log(1/delta))` rate in a uniform pointwise form.
The usual small-failure regime `delta ≤ 1/2` avoids the zero logarithm at
`delta=1`; the probability theorem itself covers every `0 < delta ≤ 1`. -/
theorem constant_sample_uniform_rate (rho : ℝ) (hr : rho < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      (constantSampleCount rho delta : ℝ) ≤ C * Real.log (1 / delta) := by
  have hgap : 0 < 1 - 2 * rho := by linarith
  have hC : 0 < gridConcentrationConstant rho := by unfold gridConcentrationConstant; positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨2 * gridConcentrationConstant rho + 1 / Real.log 2, by positivity, ?_⟩
  intro delta hdelta hdelta2
  have harg : 2 ≤ (1 : ℝ) / delta := (le_div_iff₀ hdelta).2 (by linarith)
  have hL : Real.log 2 ≤ Real.log (1 / delta) := Real.log_le_log (by norm_num) harg
  have hL0 : 0 ≤ Real.log (1 / delta) := hlog2.le.trans hL
  have hlog : Real.log (2 / delta) = Real.log 2 + Real.log (1 / delta) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hdelta.ne',
      Real.log_div one_ne_zero hdelta.ne', Real.log_one]
    ring
  have hlog0 : 0 ≤ Real.log (2 / delta) := by rw [hlog]; positivity
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hC.le hlog0)).le
  have hraw : gridConcentrationConstant rho * Real.log (2 / delta) ≤
      2 * gridConcentrationConstant rho * Real.log (1 / delta) := by
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_left hL hC.le]
  have hunit : 1 ≤ (1 / Real.log 2) * Real.log (1 / delta) := by
    have hh : 1 ≤ Real.log (1 / delta) / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hL)
    convert hh using 1 <;> ring
  change (Nat.ceil (gridConcentrationConstant rho * Real.log (2 / delta)) : ℝ) ≤ _
  nlinarith

end

end Paper34.ConstantSampling
