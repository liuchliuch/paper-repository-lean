import Paper06.FullLowerBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Real Set BigOperators MeasureTheory
open scoped Classical

namespace Paper06
namespace FinProb

/-- The finite simplex has the usual second-countable topology inherited
from its finitely many real coordinates. -/
instance simplexSecondCountable {A : Type*} [Fintype A] :
    SecondCountableTopology (FinProb A) :=
  Topology.IsInducing.secondCountableTopology
    (f := fun p : FinProb A => p.w) ⟨rfl⟩

/-- The finite tuple of feasible factors carries its Borel sigma algebra. -/
theorem independent_factors_borel {A : Type*} [Fintype A]
    (S : Set (FinProb A)) (k : ℕ) : BorelSpace (Fin k → S) := inferInstance

/-- Any Borel probability mixture of independent, not necessarily identically
distributed, feasible one-site laws.  The components in a tuple may differ
and the mixing measure may correlate their choice arbitrarily. -/
noncomputable def feasibleIndependentProductMixture {A : Type*} [Fintype A]
    (S : Set (FinProb A)) (k : ℕ) (μ : Measure (Fin k → S))
    [IsProbabilityMeasure μ] : FinProb (Fin k → A) :=
  integralMixture μ (fun q => independentFinProb (fun i => (q i).val))
    (fun z => by
      change Measurable (fun q : Fin k → S => ∏ i : Fin k, (q i).val.w (z i))
      exact Finset.measurable_prod _ (fun i _ =>
        (measurable_weight (z i)).comp
          (measurable_subtype_coe.comp (measurable_pi_apply i))))

/-- The mixture is literally the integral of the coordinatewise product. -/
theorem feasibleIndependentProductMixture_w {A : Type*} [Fintype A]
    (S : Set (FinProb A)) (k : ℕ) (μ : Measure (Fin k → S))
    [IsProbabilityMeasure μ] (z : Fin k → A) :
    (feasibleIndependentProductMixture S k μ).w z =
      ∫ q : Fin k → S, ∏ i, (q i).val.w (z i) ∂μ := rfl

end FinProb

/-- The actual event estimate survives arbitrary Borel mixing of different
feasible factors at the retained sites. -/
theorem noniid_mixture_somePairWins_le {F : Type*} [Fintype F] [Field F]
    (S : Set (FinProb (F × F))) (hS : ∀ q ∈ S, UniformInput q)
    (k : ℕ) (μ : Measure (Fin k → S)) [IsProbabilityMeasure μ] :
    (FinProb.map (FinProb.feasibleIndependentProductMixture S k μ) somePairWins).w true ≤
      ((k : ℝ) * (k - 1) / 2) * omegaR F := by
  rw [← event_somePairWins_eq_map]
  apply FinProb.integralMixture_event_le
  intro q
  rw [event_somePairWins_eq_map]
  have h := independent_somePairWins_le (fun i => (q i).val)
    (fun i => hS (q i).val (q i).property)
  rwa [Nat.cast_choose_two] at h

/-- S3.SS3.p6, the complete Proposition 3.4 witness bound for arbitrary
Borel mixtures of non-identical feasible independent factors. -/
theorem proposition_3_4_noniid {F : Type*} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (β : ℝ) (hω : omegaR F ≤ β)
    (hβ : β < 3 / (4 * ((n : ℝ) - 1)))
    (μ : ProbabilityMeasure (Fin k → {q : FinProb (F × F) | UniformInput q})) :
    (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
      log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤
    FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k (by nlinarith))
      (FinProb.feasibleIndependentProductMixture {q : FinProb (F × F) | UniformInput q}
        k (μ : Measure _)) := by
  have hkn : k ≤ n := by nlinarith
  apply FinProb.kl_ge_matching_event _ _ somePairWins n k β hn hk2 hkk
    (le_trans omegaR_nonneg hω) hβ
  · exact Matching.matching_marginal_somePairWins_ge n k hEven hn hk2 hkn hkk
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hm : 0 ≤ (k : ℝ) * (k - 1) / 2 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg k) (by linarith)) (by norm_num)
    exact (noniid_mixture_somePairWins_le {q : FinProb (F × F) | UniformInput q}
        (fun _ h => h) k
        (μ : Measure (Fin k → {q : FinProb (F × F) | UniformInput q}))).trans
      (mul_le_mul_of_nonneg_left hω hm)

/-- S3.SS3.p6, both inequalities of Theorem 3.1 against arbitrary Borel
mixtures of q₁ ⊗ ... ⊗ qₖ with each qᵢ in the original slice. -/
theorem matching_noniid_logarithmic_lower_bound {F : Type*} [Fintype F] [Field F]
    (n k : ℕ) (hEven : Even n) (hn : 6 ≤ n) (hk2 : 2 ≤ k)
    (hkk : k * k ≤ n) (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2)
    (hparam : 2 * Real.exp 1 * ((n : ℝ) - 1) ≤
      (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ))
    (μ : ProbabilityMeasure (Fin k → {q : FinProb (F × F) | UniformInput q})) :
    (((3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
      (16 * (n - 1)) : ℝ) : EReal) ≤
      FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k (by nlinarith))
        (FinProb.feasibleIndependentProductMixture {q : FinProb (F × F) | UniformInput q}
          k (μ : Measure _)) ∧
    (3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
      (n - k + 1) ≤
      (3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
        (16 * (n - 1)) := by
  constructor
  · apply FinProb.kl_ge_logarithmic_event _ _ somePairWins n k (Fintype.card F) θ
      hn hk2 hkk Fintype.one_lt_card hθ hθhalf hparam
    · exact Matching.matching_marginal_somePairWins_ge n k hEven hn hk2 (by nlinarith) hkk
    · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hm : 0 ≤ (k : ℝ) * (k - 1) / 2 :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg k) (by linarith)) (by norm_num)
      have hb : omegaR F ≤ 3 / (2 * sqrt (Fintype.card F)) :=
        omegaR_le_beta.trans (betaR_le _ (by
          exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)))
      exact (noniid_mixture_somePairWins_le {q : FinProb (F × F) | UniformInput q}
        (fun _ h => h) k
        (μ : Measure (Fin k → {q : FinProb (F × F) | UniformInput q}))).trans
        (mul_le_mul_of_nonneg_left hb hm)
  · exact thm_3_1_constants n k θ _ hn hk2 hkk hθ (by
      have hc : (1 : ℝ) ≤ Fintype.card F := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
      nlinarith)

end Paper06
