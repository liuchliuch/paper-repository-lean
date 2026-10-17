import Verification.Statements

/-!
# Negative control: extra premise

Same theorem names as `Verification.Solution`, but `lemma2_main` carries an
extra `False` hypothesis so its type differs from the challenge and the
Comparator rejects the match.
-/

noncomputable section
namespace Verification.Certificate

open PUT

theorem lemma2_main (hbad : False) : Specification.Lemma2_Main :=
  False.elim hbad

theorem lemma1_bound : Specification.Lemma1_Bound := by
  intro d a A M hd ha hA hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · rfl

theorem theorem1_constant : Specification.Theorem1_Constant :=
  PUT.c0_pos

theorem theorem1_target : Specification.Theorem1_Target := by
  refine ⟨?_, ?_, ?_⟩
  · intro d ε hd hε hε'
    exact PUT.theorem1.2 d ε hd hε hε'
  · intro d ε hd hε hε'
    exact PUT.const_acc_target d ε hd hε hε'
  · intro d ε hd hε
    exact PUT.regime_implies_target d ε hd hε

theorem cutoff_theory : Specification.Cutoff_Theory := by
  intro d k
  unfold degK degR
  refine Finset.sum_le_sum fun i _ => ?_
  have h : (k i) ≤ (k i) * (k i) := Nat.le_mul_self (k i)
  rw [pow_two]
  exact h

theorem moments_formula : Specification.Moments_Formula := by
  intro a d k
  rfl

theorem collision_tv : Specification.Collision_TV := by
  intro d hd
  exact PUT.collTV_gt_half d hd

theorem progress_lower : Specification.Progress_Lower := by
  intro A B q0 T hA hB hq0 hT h
  have hdrop : q0 * A / 8 ≤ T * B := by
    have : A * q0 / 8 ≤ T * B := by nlinarith [mul_pos hA hq0]
    nlinarith
  have h8B : 0 < 8 * B := by positivity
  have : q0 * A ≤ T * (8 * B) := by nlinarith
  exact (div_le_iff₀ h8B).2 this

theorem scale_choice : Specification.Scale_Choice := by
  intro ε hε hε'
  have h48 : 0 < 48 * ε := by positivity
  have hle : 48 * ε ≤ 1 := by nlinarith
  unfold dirichletScale
  have hz : (48 * ε) ^ (-2 : ℤ) = ((48 * ε) ^ (2 : ℕ))⁻¹ := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by omega, zpow_neg, zpow_ofNat]
  rw [hz]
  have hsq : (48 * ε) ^ (2 : ℕ) ≤ 1 := by
    have := pow_le_pow_left₀ (le_of_lt h48) hle 2
    simpa using this
  exact (one_le_inv₀ (pow_pos h48 2)).2 hsq

theorem actual_adversary_norm : Specification.ActualAdversaryNorm := @PUT.FiniteAdversary.gamma_norm
theorem actual_full_query_norm : Specification.ActualFullQueryNorm := @PUT.OperatorBridge.full_query_norm_le
theorem continuous_paley_zygmund : Specification.ContinuousPaleyZygmund := @PUT.paley_zygmund_measure
theorem actual_query_progress : Specification.ActualQueryProgress := @PUT.QueryModel.query_progress_bound
theorem actual_final_progress : Specification.ActualFinalProgress := @PUT.QueryModel.final_progress_envelope
theorem actual_reflection_preparation : Specification.ActualReflectionPreparation := @PUT.ReflectionOracle.unitary_prepares
theorem actual_prior_probability : Specification.ActualPriorProbability := @PUT.QueryModel.Circuit.prior_rejection_probability


theorem source_lemma2 (hbad : False) : Specification.SourceLemma2 := False.elim hbad


theorem source_lemma1 : Specification.SourceLemma1 := by
  intro moments d M a A hd ha hA hM
  exact PUT.FullQueryBound.query_norm_le_printed moments hd ha A hA hM


theorem source_theorem1_promised (hbad : False) : Specification.SourcePromiseTheorem1 := False.elim hbad

theorem source_theorem1_adaptive : Specification.SourceAdaptiveTheorem1 := PUT.Paper.theorem1_adaptive

theorem source_theorem1 : Specification.SourceTheorem1 := PUT.Paper.theorem1

end Verification.Certificate
