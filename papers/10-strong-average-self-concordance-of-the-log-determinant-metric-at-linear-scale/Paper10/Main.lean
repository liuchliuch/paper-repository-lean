import Paper10.Basic
import Paper10.Symm
import Paper10.Metric
import Paper10.SSC
import Paper10.SASC
import Paper10.PairedTraces
import Paper10.Remainder
import Paper10.Gaussian
import Paper10.Appendix
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Quantitative ingredients for Theorem 1.3

This module proves the radius and concentration estimates. The actual main probability
theorem is in SASCProof/Proposal/Theorems; the metric derivative is in MetricCalculus/SSCFrame.
The moment hypotheses below are local inputs to concentration and are discharged in the main proof.
-/

noncomputable section
open Matrix MeasureTheory
namespace Paper10
variable {q : ℕ}

/-- Normalized time step in (8). -/
def tOf (r s : ℝ) : ℝ := r / Real.sqrt ((n q : ℕ) * s)

/-- Exact square of the admissible uniform radius. -/
theorem rEps_sq {ε : ℝ} (hε : 0 < ε) : (rEps ε) ^ 2 = ε ^ 3 / 864 := by
  unfold rEps
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 864)]
  have hh : (ε ^ (3 / 2 : ℝ)) ^ 2 = ε ^ 3 := by
    rw [← Real.rpow_mul_natCast hε.le]
    norm_num
  rw [hh]

/-- The radius condition in (5) implies the square bound used in (19)–(20). -/
theorem radius_sq_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hr' : r ≤ rEps ε) :
    r ^ 2 ≤ ε ^ 3 / 864 := by
  rw [← rEps_sq hε]
  nlinarith [rEps_pos hε]

/-- Both scaled moment bounds in (18) use this single algebraic calculation. -/
theorem eq_18_scale (hq : 0 < q) (r s M C : ℝ) (hs : c q ≤ s)
    (hC : 0 ≤ C) (hM : M ≤ C * (n q : ℝ) * c q) :
    (tOf (q := q) r s) ^ 2 * M ≤ C * r ^ 2 := by
  have hn : (0 : ℝ) < n q := Nat.cast_pos.mpr (n_pos hq)
  have hs0 := lt_of_lt_of_le (c_pos q) hs
  have hnsp : 0 < (n q : ℝ) * s := mul_pos hn hs0
  have ht : (tOf (q := q) r s) ^ 2 = r ^ 2 / ((n q : ℝ) * s) := by
    unfold tOf
    rw [div_pow, Real.sq_sqrt hnsp.le]
  rw [ht]
  calc
    _ ≤ r ^ 2 / ((n q : ℝ) * s) * (C * (n q : ℝ) * c q) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = C * r ^ 2 * c q / s := by field_simp
    _ ≤ C * r ^ 2 := by
      rw [div_le_iff₀ hs0]
      exact mul_le_mul_of_nonneg_left hs (mul_nonneg hC (sq_nonneg r))

/-- The explicit error budgets in (19)–(20). -/
theorem event_prob_bounds {ε r : ℝ} (hε : 0 < ε) (hε' : ε < 1)
    (hr : 0 < r) (hr' : r ≤ rEps ε) :
    108 * r ^ 2 / ε ^ 2 ≤ ε / 8 ∧ 48 * r ^ 2 / ε ≤ ε ^ 2 / 18 ∧
      ε / 8 + ε ^ 2 / 18 < ε := by
  have hs := radius_sq_le hε hr hr'
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hsq]
    nlinarith
  · rw [div_le_iff₀ hε]
    nlinarith
  · nlinarith [mul_pos hε (sub_pos.mpr hε')]

/-- Markov's inequality in the real-valued probability form used below. -/
theorem markov_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a < f ω} ≤ (∫ ω, f ω ∂μ) / a := by
  have hh := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hf0) hf a
  have hm : μ.real {ω | a < f ω} ≤ μ.real {ω | a ≤ f ω} :=
    measureReal_mono (fun ω h => (show a < f ω from h).le)
  rw [le_div_iff₀ ha]
  nlinarith

/-- Joint Chebyshev/Markov concentration with the paper's constants, for actual measures.
The two moment hypotheses are inputs to this concentration lemma, not to the main theorem. -/
theorem concentration_from_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (C Q : Ω → ℝ) (hC : Measurable C) (hQ : Measurable Q)
    (hC2 : Integrable (fun ω => C ω ^ 2) μ) (hQi : Integrable Q μ)
    (hQ0 : ∀ ω, 0 ≤ Q ω) {t ε r : ℝ} (ht : 0 < t)
    (hε : 0 < ε) (hε' : ε < 1) (hr : 0 < r) (hr' : r ≤ rEps ε)
    (hm3 : t ^ 2 * (∫ ω, C ω ^ 2 ∂μ) ≤ 27 * r ^ 2)
    (hm4 : t ^ 2 * (∫ ω, Q ω ∂μ) ≤ 3 * r ^ 2) :
    1 - ε ≤ μ.real {ω | t * |C ω| ≤ ε / 2 ∧ t ^ 2 * Q ω ≤ ε / 16} := by
  let E3 := {ω | t * |C ω| ≤ ε / 2}
  let E4 := {ω | t ^ 2 * Q ω ≤ ε / 16}
  have hE3 : MeasurableSet E3 := measurableSet_le (hC.abs.const_mul t) measurable_const
  have hE4 : MeasurableSet E4 := measurableSet_le (hQ.const_mul _) measurable_const
  have h3 := markov_real (hC2.const_mul (t ^ 2))
    (fun ω => mul_nonneg (sq_nonneg t) (sq_nonneg (C ω))) (show 0 < ε ^ 2 / 4 by positivity)
  have h4 := markov_real (hQi.const_mul (t ^ 2))
    (fun ω => mul_nonneg (sq_nonneg t) (hQ0 ω)) (show 0 < ε / 16 by positivity)
  have he3 : E3ᶜ = {ω | ε ^ 2 / 4 < t ^ 2 * C ω ^ 2} := by
    ext ω
    simp only [E3, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    have hpos : 0 ≤ t * |C ω| := mul_nonneg ht.le (abs_nonneg _)
    constructor
    · intro hh
      have hs := (sq_lt_sq₀ (show 0 ≤ ε / 2 by positivity) hpos).mpr hh
      simpa only [div_pow, mul_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
    · intro hh
      apply (sq_lt_sq₀ (show 0 ≤ ε / 2 by positivity) hpos).mp
      simpa only [div_pow, mul_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  have he4 : E4ᶜ = {ω | ε / 16 < t ^ 2 * Q ω} := by ext ω; simp [E4]
  rw [integral_const_mul] at h3 h4
  have hb3 : μ.real E3ᶜ ≤ 108 * r ^ 2 / ε ^ 2 := by
    rw [he3]
    apply h3.trans
    rw [div_le_iff₀ (by positivity : 0 < ε ^ 2 / 4)]
    field_simp
    nlinarith
  have hb4 : μ.real E4ᶜ ≤ 48 * r ^ 2 / ε := by
    rw [he4]
    apply h4.trans
    rw [div_le_iff₀ (by positivity : 0 < ε / 16)]
    field_simp
    nlinarith
  have hub := measureReal_union_le (μ := μ) E3ᶜ E4ᶜ
  have hcomp : μ.real (E3ᶜ ∪ E4ᶜ) = 1 - μ.real (E3 ∩ E4) := by
    rw [← Set.compl_inter, measureReal_compl (hE3.inter hE4), measureReal_univ_eq_one]
  have he := event_prob_bounds hε hε' hr hr'
  rw [hcomp] at hub
  change 1 - ε ≤ μ.real (E3 ∩ E4)
  linarith [he.1, he.2.1, he.2.2]

end Paper10
