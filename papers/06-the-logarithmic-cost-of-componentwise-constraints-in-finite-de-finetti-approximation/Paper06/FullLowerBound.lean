import Paper06.MatchingMarginals
import Paper06.UniformSlice
import Paper06.WitnessFull
import Paper06.LowerBound
import Mathlib.FieldTheory.Finite.Basic

open Real Set BigOperators MeasureTheory
open scoped Classical

namespace Paper06

/-- **Proposition 3.4.** The actual matching marginal is separated from
every Borel feasible product mixture.  Both event estimates are derived
from the explicit law and the finite-field incidence theorem. -/
theorem proposition_3_4 {F : Type*} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (β : ℝ) (hω : omegaR F ≤ β)
    (hβ : β < 3 / (4 * ((n : ℝ) - 1)))
    (μ : ProbabilityMeasure {q : FinProb (F × F) | UniformInput q}) :
    (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤
    FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k
      (by nlinarith))
      (FinProb.feasibleProductMixture {q : FinProb (F × F) | UniformInput q}
        (μ : Measure _) k) := by
  have hkn : k ≤ n := by nlinarith
  apply FinProb.kl_ge_matching_event _ _ somePairWins n k β hn hk2 hkk
    (le_trans (le_of_lt omegaR_pos) hω) hβ
  · exact Matching.matching_marginal_somePairWins_ge n k hEven hn hk2 hkn hkk
  · have hm : 0 ≤ (k : ℝ) * (k - 1) / 2 := by
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hk1) (by norm_num)
    exact (uniformInput_mixture_somePairWins_le (μ : Measure _) k).trans
      (mul_le_mul_of_nonneg_left hω hm)

/-- **Theorem 3.1**, first inequality, for the fixed matching law.  The
law is chosen before both `k` and the arbitrary Borel mixing measure. -/
theorem matching_logarithmic_lower_bound {F : Type*} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ))
    (μ : ProbabilityMeasure {q : FinProb (F × F) | UniformInput q}) :
    (((3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
      (16 * (n - 1)) : ℝ) : EReal) ≤
    FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k
      (by nlinarith))
      (FinProb.feasibleProductMixture {q : FinProb (F × F) | UniformInput q}
        (μ : Measure _) k) := by
  have hkn : k ≤ n := by nlinarith
  have hr : 1 < Fintype.card F := Fintype.one_lt_card
  apply FinProb.kl_ge_logarithmic_event _ _ somePairWins n k (Fintype.card F) θ
    hn hk2 hkk hr hθ hθhalf hparam
  · exact Matching.matching_marginal_somePairWins_ge n k hEven hn hk2 hkn hkk
  · have hm : 0 ≤ (k : ℝ) * (k - 1) / 2 := by
      have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hk1) (by norm_num)
    have hinc : omegaR F ≤ 3 / (2 * sqrt (Fintype.card F)) :=
      omegaR_le_beta.trans (betaR_le _ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)))
    exact (uniformInput_mixture_somePairWins_le (μ : Measure _) k).trans
      (mul_le_mul_of_nonneg_left hinc hm)

/-- The second inequality of (5), for the actual optimum over all μ. -/
theorem matching_constrainedError_lower {F : Type*} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ)) :
    ((((3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2))) /
      (n - k + 1) : ℝ) : EReal) ≤
      constrainedError (Matching.matchingLawFin (R := F) n hEven)
        {q : FinProb (F × F) | UniformInput q} k (by nlinarith) := by
  apply le_constrainedError
  intro μ
  have hc := thm_3_1_constants n k θ ((Fintype.card F : ℝ) ^ 2)
    hn hk2 hkk hθ (by
      have hcard : (1 : ℝ) ≤ Fintype.card F := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
      nlinarith)
  exact (EReal.coe_le_coe hc).trans
    (matching_logarithmic_lower_bound n k hEven hn hk2 hkk θ hθ hθhalf hparam μ)

/-- **Theorem 3.1**, existence form retaining both inequalities and every
quantifier over marginal size and Borel mixing measure.  The statement
holds over every finite field, and therefore over each prime field. -/
theorem theorem_3_1 {F : Type*} [Fintype F] [Field F]
    (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (n : ℕ) (hn : 6 ≤ n) (hEven : Even n)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ)) :
    ∃ P : FinProb (Fin n → F × F),
      Posterior.Exchangeable P ∧
      (∀ i, Posterior.LiftedCP (uniformInputLinear F) (uniformInputTarget F) P i) ∧
      ∀ k, 2 ≤ k → (hkk : k * k ≤ n) →
        ∀ μ : ProbabilityMeasure {q : FinProb (F × F) | UniformInput q},
          (((3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
            (16 * (n - 1)) : ℝ) : EReal) ≤
            FinProb.kl (marginal P k (by nlinarith))
              (FinProb.feasibleProductMixture {q : FinProb (F × F) | UniformInput q}
                (μ : Measure _) k) ∧
          (3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
            (n - k + 1) ≤
            (3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
              (16 * (n - 1)) := by
  refine ⟨(matchingAdmissible F n hEven).law,
    (matchingAdmissible F n hEven).exchangeable, (matchingAdmissible F n hEven).cp, ?_⟩
  intro k hk2 hkk μ
  refine ⟨matching_logarithmic_lower_bound n k hEven hn hk2 hkk θ hθ hθhalf hparam μ, ?_⟩
  exact thm_3_1_constants n k θ _ hn hk2 hkk hθ (by
    have hc : (1 : ℝ) ≤ Fintype.card F := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
    nlinarith)

/-- The source's prime-field formulation of Theorem 3.1, with d=r². -/
theorem theorem_3_1_prime (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (n : ℕ) (hn : 6 ≤ n) (hEven : Even n) (r : ℕ) (hr : Nat.Prime r)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (r : ℝ) ^ ((1 : ℝ) / 2 - θ)) :
    letI : Fact (Nat.Prime r) := ⟨hr⟩
    ∃ P : FinProb (Fin n → ZMod r × ZMod r),
      Posterior.Exchangeable P ∧
      (∀ i, Posterior.LiftedCP (uniformInputLinear (ZMod r)) (uniformInputTarget (ZMod r)) P i) ∧
      ∀ k, 2 ≤ k → (hkk : k * k ≤ n) →
        ∀ μ : ProbabilityMeasure {q : FinProb (ZMod r × ZMod r) | UniformInput q},
          (((3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) /
            (16 * (n - 1)) : ℝ) : EReal) ≤
            FinProb.kl (marginal P k (by nlinarith))
              (FinProb.feasibleProductMixture {q : FinProb (ZMod r × ZMod r) | UniformInput q}
                (μ : Measure _) k) ∧
          (3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) / (n - k + 1) ≤
            (3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) / (16 * (n - 1)) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hp : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card (ZMod r) : ℝ) ^ ((1 : ℝ) / 2 - θ) := by
    simpa only [ZMod.card] using hparam
  simpa only [ZMod.card] using theorem_3_1 (F := ZMod r) θ hθ hθhalf n hn hEven hp

end Paper06
