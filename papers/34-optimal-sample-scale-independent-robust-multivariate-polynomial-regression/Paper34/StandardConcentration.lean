import Paper34.GoodGrid
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Instantiate the source Hoeffding interface from pinned mathlib

The fixed mathlib version already proves Hoeffding's bounded-variable lemma
and the independent-sum sub-Gaussian tail. This file derives the existing
`BernoulliSubsetHoeffdingInput` from those checked theorems. In particular,
the deterministic subset, individual non-identical success probabilities,
Boolean-to-real indicator conversion, expectation, and tail comparison are
all proved here. The multiplicative half-mean Chernoff interface is also
derived from mathlib's generic MGF lower-tail theorem and the exact Bernoulli
MGF. No additional external theorem input is introduced.
-/

namespace Paper34.StandardConcentration

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

def realBool (b : Bool) : ℝ := if b = true then 1 else 0

theorem realBool_mem_Icc (b : Bool) : realBool b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [realBool]

theorem integral_realBool {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y : Ω → Bool) (hY : Measurable Y) :
    (∫ ω, realBool (Y ω) ∂P) = P.real {ω | Y ω = true} := by
  have heq : (fun ω => realBool (Y ω)) = {ω | Y ω = true}.indicator (1 : Ω → ℝ) := by
    funext ω
    simp only [realBool, Set.indicator_apply, mem_setOf_eq, Pi.one_apply]
  rw [heq]
  have hs : MeasurableSet {ω | Y ω = true} := hY (measurableSet_singleton true)
  exact integral_indicator_one hs

theorem sum_realBool_eq_count {M : ℕ} (Y : Fin M → Bool) (S : Finset (Fin M)) :
    (∑ i ∈ S, realBool (Y i)) = boolCount Y S := by
  classical
  simp [realBool, boolCount]

/-- The quarter-variance proxy for each centered actual Boolean indicator. -/
theorem centered_realBool_subGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → Bool) (hY : Measurable Y) :
    HasSubgaussianMGF (fun ω => realBool (Y ω) - P.real {ω | Y ω = true}) (1 / 4) P := by
  have hm : Measurable (fun ω => realBool (Y ω)) := (measurable_of_finite realBool).comp hY
  have h := hasSubgaussianMGF_of_mem_Icc hm.aemeasurable
    (ae_of_all P (fun ω => realBool_mem_Icc (Y ω)))
  rw [integral_realBool Y hY] at h
  norm_num at h
  exact h

/-- Producer for the stable source interface. Its full generality includes
every deterministic subset and non-identical Bernoulli rates at most `rho`. -/
theorem bernoulliSubsetHoeffdingInput
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (M : ℕ) :
    BernoulliSubsetHoeffdingInput P M := by
  intro Y hY hindep rho a hr0 hra hrate S
  classical
  by_cases hS : S = ∅
  · subst S
    simp [boolCount]
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  let Z (i : Fin M) (ω : Ω) : ℝ := realBool (Y i ω) - P.real {ω | Y i ω = true}
  have hZindep : iIndepFun Z P :=
    hindep.comp (fun i b => realBool b - P.real {ω | Y i ω = true})
      (fun _ => measurable_of_finite _)
  have hZsub : ∀ i ∈ S, HasSubgaussianMGF (Z i) (1 / 4) P :=
    fun i _ => centered_realBool_subGaussian (Y i) (hY i)
  have hmean : (∑ i ∈ S, P.real {ω | Y i ω = true}) ≤ rho * (S.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ S, rho := Finset.sum_le_sum (fun i _ => hrate i)
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  have hsub : {ω | a * (S.card : ℝ) < boolCount (fun i => Y i ω) S} ⊆
      {ω | (a - rho) * (S.card : ℝ) ≤ ∑ i ∈ S, Z i ω} := by
    intro ω hω
    change a * (S.card : ℝ) < boolCount (fun i => Y i ω) S at hω
    change (a - rho) * (S.card : ℝ) ≤ _
    simp only [Z, Finset.sum_sub_distrib, sum_realBool_eq_count]
    nlinarith
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hZindep
    (c := fun _ : Fin M => (1 / 4 : ℝ≥0)) (s := S) hZsub
    (ε := (a - rho) * (S.card : ℝ)) (mul_nonneg (sub_nonneg.mpr hra.le) hN.le)
  have hquarter : ((∑ _i ∈ S, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ) = (S.card : ℝ) / 4 := by
    simp [nsmul_eq_mul]
    <;> ring
  rw [hquarter] at ht
  have hexponent : -((a - rho) * (S.card : ℝ)) ^ 2 / (2 * ((S.card : ℝ) / 4)) =
      -2 * (a - rho) ^ 2 * (S.card : ℝ) := by
    field_simp [hN.ne']
    <;> ring
  rw [hexponent] at ht
  exact (measureReal_mono hsub).trans ht

/-- Exact MGF of a genuine Bernoulli indicator, from its actual expectation. -/
theorem mgf_realBool
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → Bool) (hY : Measurable Y) (t : ℝ) :
    mgf (fun ω => realBool (Y ω)) P t =
      1 + (Real.exp t - 1) * P.real {ω | Y ω = true} := by
  have hm : Measurable (fun ω => realBool (Y ω)) := (measurable_of_finite realBool).comp hY
  have hi : Integrable (fun ω => realBool (Y ω)) P :=
    Integrable.of_mem_Icc 0 1 hm.aemeasurable (ae_of_all P (fun ω => realBool_mem_Icc (Y ω)))
  have heq : (fun ω => Real.exp (t * realBool (Y ω))) =
      (fun ω => 1 + (Real.exp t - 1) * realBool (Y ω)) := by
    funext ω
    cases Y ω <;> simp [realBool]
  rw [mgf, heq, integral_add (integrable_const 1) (hi.const_mul _),
    integral_const_mul, integral_realBool Y hY]
  simp

/-- A checked numerical estimate sufficient for the source's `1/8` constant. -/
theorem exp_neg_one_le_three_eighths : Real.exp (-1 : ℝ) ≤ 3 / 8 := by
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos 1)).2
  nlinarith [Real.exp_one_gt_d9]

/-- The source's multiplicative half-mean Chernoff input, now derived from
mathlib's generic MGF lower tail and the exact Bernoulli MGF. -/
theorem bernoulliLowerHalfInput
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (M : ℕ) :
    BernoulliLowerHalfInput P M := by
  intro Y hY hindep p hp
  classical
  by_cases hM : M = 0
  · subst M
    simp [boolCount]
  let i0 : Fin M := ⟨0, Nat.pos_of_ne_zero hM⟩
  have hp0 : 0 ≤ p := by rw [← hp i0]; exact measureReal_nonneg
  let X (i : Fin M) (ω : Ω) : ℝ := realBool (Y i ω)
  have hXm : ∀ i, Measurable (X i) := fun i => (measurable_of_finite realBool).comp (hY i)
  have hXi : iIndepFun X P := hindep.comp (fun _ => realBool) (fun _ => measurable_of_finite _)
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin M)),
      Integrable (fun ω => Real.exp ((-1) * X i ω)) P := by
    intro i hi
    exact integrable_exp_mul_of_mem_Icc (hXm i).aemeasurable
      (ae_of_all P (fun ω => realBool_mem_Icc (Y i ω)))
  have hSumInt := hXi.integrable_exp_mul_sum hXm hInt
  have hmgf (i : Fin M) : mgf (X i) P (-1) = 1 + (Real.exp (-1) - 1) * p := by
    change mgf (fun ω => realBool (Y i ω)) P (-1) = _
    rw [mgf_realBool (Y i) (hY i), hp i]
  have hbase0 : 0 ≤ 1 + (Real.exp (-1) - 1) * p := by
    rw [← hmgf i0]
    exact mgf_nonneg
  have hbase : 1 + (Real.exp (-1) - 1) * p ≤ Real.exp ((Real.exp (-1) - 1) * p) := by
    simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (-1) - 1) * p)
  have hsumMGF : mgf (∑ i : Fin M, X i) P (-1) ≤
      Real.exp ((M : ℝ) * ((Real.exp (-1) - 1) * p)) := by
    rw [hXi.mgf_sum hXm Finset.univ]
    simp_rw [hmgf]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc
      _ ≤ Real.exp ((Real.exp (-1) - 1) * p) ^ M := pow_le_pow_left₀ hbase0 hbase M
      _ = _ := (Real.exp_nat_mul _ M).symm
  have hcount (ω : Ω) : (∑ i : Fin M, X i) ω = boolCount (fun i => Y i ω) Finset.univ := by
    simp only [Finset.sum_apply, X]
    exact sum_realBool_eq_count _ _
  have hsub : {ω | boolCount (fun i => Y i ω) Finset.univ < (M : ℝ) * p / 2} ⊆
      {ω | (∑ i : Fin M, X i) ω ≤ (M : ℝ) * p / 2} := by
    intro ω hω
    change (∑ i : Fin M, X i) ω ≤ _
    rw [hcount]
    exact le_of_lt hω
  have ht := measure_le_le_exp_mul_mgf (X := ∑ i : Fin M, X i) (μ := P)
    ((M : ℝ) * p / 2) (t := -1) (by norm_num) hSumInt
  calc
    P.real _ ≤ P.real {ω | (∑ i : Fin M, X i) ω ≤ (M : ℝ) * p / 2} := measureReal_mono hsub
    _ ≤ Real.exp (-(-1 : ℝ) * ((M : ℝ) * p / 2)) * mgf (∑ i : Fin M, X i) P (-1) := ht
    _ ≤ Real.exp ((M : ℝ) * p / 2) *
        Real.exp ((M : ℝ) * ((Real.exp (-1) - 1) * p)) := by
      simpa only [neg_neg, one_mul] using
        mul_le_mul_of_nonneg_left hsumMGF (Real.exp_pos ((M : ℝ) * p / 2)).le
    _ = Real.exp ((M : ℝ) * p / 2 + (M : ℝ) * ((Real.exp (-1) - 1) * p)) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(M : ℝ) * p / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_one_le_three_eighths
        (mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hp0)]

end

end Paper34.StandardConcentration
