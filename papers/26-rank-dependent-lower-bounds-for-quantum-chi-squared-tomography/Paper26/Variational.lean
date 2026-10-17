import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The scalar spectral minimization used in Appendix A and Appendix B.
The POVM posterior moment identity and minimax reduction are separate obligations;
they are not hypotheses hidden inside the definitions below.
-/
noncomputable section
open scoped BigOperators

namespace Paper26.Variational

variable {ι : Type*} [Fintype ι]

def spectralRisk (m s : ι → ℝ) : ℝ := ∑ i, m i / s i
def sqrtTrace (m : ι → ℝ) : ℝ := ∑ i, Real.sqrt (m i)
def optimalSpectrum (m : ι → ℝ) (i : ι) : ℝ := Real.sqrt (m i) / sqrtTrace m

theorem spectralRisk_lower (m s : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i = 1) :
    sqrtTrace m ^ 2 ≤ spectralRisk m s := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i => Real.sqrt (m i)) (fun i _ => hs i)
  simpa [sqrtTrace, spectralRisk, hsum, Real.sq_sqrt (hm _)] using h

theorem sqrtTrace_pos [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    0 < sqrtTrace m := by
  apply Finset.sum_pos
  · intro i _
    exact Real.sqrt_pos.2 (hm i)
  · exact Finset.univ_nonempty

theorem optimalSpectrum_pos [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) (i : ι) :
    0 < optimalSpectrum m i := by
  exact div_pos (Real.sqrt_pos.2 (hm i)) (sqrtTrace_pos m hm)

theorem optimalSpectrum_sum [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    ∑ i, optimalSpectrum m i = 1 := by
  unfold optimalSpectrum
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (sqrtTrace_pos m hm))

theorem spectralRisk_optimal [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    spectralRisk m (optimalSpectrum m) = sqrtTrace m ^ 2 := by
  unfold spectralRisk optimalSpectrum
  calc
    _ = ∑ i, Real.sqrt (m i) * sqrtTrace m := by
      apply Finset.sum_congr rfl
      intro i _
      have hroot : Real.sqrt (m i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hm i))
      have htrace : sqrtTrace m ≠ 0 := ne_of_gt (sqrtTrace_pos m hm)
      have hsq := Real.sq_sqrt (hm i).le
      field_simp
      nlinarith
    _ = sqrtTrace m ^ 2 := by rw [← Finset.sum_mul]; simp [sqrtTrace, pow_two]

/-- The infimum has an explicit feasible minimizer, in the positive spectrum case. -/
theorem spectralRisk_minimizer [Nonempty ι] (m : ι → ℝ) (hm : ∀ i, 0 < m i) :
    (∀ i, 0 < optimalSpectrum m i) ∧
    (∑ i, optimalSpectrum m i = 1) ∧
    spectralRisk m (optimalSpectrum m) = sqrtTrace m ^ 2 ∧
    ∀ s : ι → ℝ, (∀ i, 0 < s i) → (∑ i, s i = 1) →
      spectralRisk m (optimalSpectrum m) ≤ spectralRisk m s := by
  refine ⟨optimalSpectrum_pos m hm, optimalSpectrum_sum m hm,
    spectralRisk_optimal m hm, ?_⟩
  intro s hs hsum
  rw [spectralRisk_optimal m hm]
  exact spectralRisk_lower m s (fun i => (hm i).le) hs hsum

/-- The chord bound used to minimize the square-root trace over posterior spectra. -/
theorem sqrt_one_add_chord {n x : ℝ} (hn : 0 ≤ n) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 + (Real.sqrt (n + 1) - 1) * x ≤ Real.sqrt (1 + n * x) := by
  have hr0 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hr1 : 1 ≤ Real.sqrt (n + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have h := mul_nonneg (sq_nonneg (Real.sqrt (n + 1) - 1)) hxx
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- Appendix A's spectral lower bound, with all eigenvalues and normalization explicit. -/
theorem posterior_sqrtTrace_lower (n : ℝ) (hn : 0 ≤ n) (spectrum : ι → ℝ)
    (hspec : ∀ i, 0 ≤ spectrum i) (hsum : ∑ i, spectrum i = 1) :
    Real.sqrt (n + 1) + Fintype.card ι - 1 ≤
      ∑ i, Real.sqrt (1 + n * spectrum i) := by
  have hle : ∀ i, spectrum i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hspec j) (Finset.mem_univ i)
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sqrt_one_add_chord hn (hspec i) (hle i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum, hsum] at h
  linarith

/-- The elementary chord inequality in Proposition B.1. -/
theorem sqrt_one_add_ge_chord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 + (Real.sqrt 2 - 1) * x ≤ Real.sqrt (1 + x) := by
  convert sqrt_one_add_chord (n := 1) (by norm_num) hx0 hx1 using 1 <;> norm_num

/-- The average of the principal-angle terms yields the stated linear lower bound. -/
theorem common_center_scalar_lower (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (hcard : 0 < (Fintype.card ι : ℝ)) :
    (2 * (Real.sqrt 2 - 1)) * ((∑ i, x i) / Fintype.card ι) ≤
      ((∑ i, Real.sqrt (1 + x i)) / Fintype.card ι) ^ 2 - 1 := by
  have ha : 0 ≤ Real.sqrt 2 - 1 := by
    have := Real.le_sqrt_of_sq_le (x := (1 : ℝ)) (y := 2) (by norm_num)
    linarith
  have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx0 i)
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sqrt_one_add_ge_chord (hx0 i) (hx1 i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Finset.mul_sum] at h
  have hdiv : 1 + (Real.sqrt 2 - 1) * ((∑ i, x i) / Fintype.card ι) ≤
      (∑ i, Real.sqrt (1 + x i)) / Fintype.card ι := by
    apply (le_div_iff₀ hcard).2
    field_simp
    nlinarith
  have hp : 0 ≤ (Real.sqrt 2 - 1) * ((∑ i, x i) / Fintype.card ι) := by positivity
  nlinarith [sq_nonneg ((Real.sqrt 2 - 1) * ((∑ i, x i) / Fintype.card ι))]

end Paper26.Variational
