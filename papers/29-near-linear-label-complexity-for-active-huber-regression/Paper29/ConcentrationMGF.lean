import Paper29.HardDistribution
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Paper29.HardDistribution

lemma bernoulli_mgf_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (∑ b : Bool, bitMass p b * Real.exp (t * (bit b - p))) ≤ Real.exp (t ^ 2 / 8) := by
  let q : ℝ≥0 := ⟨p, hp⟩
  have hq : q ≤ 1 := hp1
  let m : PMF Bool := PMF.bernoulli q hq
  have hmean : (∫ b, bit b ∂m.toMeasure) = p := by
    have heq : bit = (fun b : Bool => cond b (1 : ℝ) 0) := by
      funext b
      cases b <;> rfl
    rw [heq]
    simpa [m, q] using PMF.bernoulli_expectation hq
  have hm : ∀ b : Bool, (m b).toReal = bitMass p b := by
    intro b
    cases b
    · change (1 - (q : ℝ≥0∞)).toReal = 1 - p
      rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hq) (by simp)]
      simp [q]
    · change (q : ℝ≥0∞).toReal = p
      simp [q]
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := m.toMeasure) (X := bit)
    ((measurable_of_countable bit).aemeasurable)
    (ae_of_all _ (fun b => (show bit b ∈ Set.Icc (0 : ℝ) 1 by cases b <;> norm_num [bit])))
  have h := hsub.mgf_le t
  rw [hmean] at h
  simp only [mgf, PMF.integral_eq_sum, hm, smul_eq_mul] at h
  convert h using 1 <;> norm_num <;> ring

end Paper29.HardDistribution
