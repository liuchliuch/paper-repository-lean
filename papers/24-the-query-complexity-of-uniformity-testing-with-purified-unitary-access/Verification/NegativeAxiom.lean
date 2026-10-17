import Verification.Statements

/-!
# Negative control: illegal axiom

Same theorem names and types as `Verification.Solution`, but the proofs
route through a non-permitted axiom so the axiom audit rejects this module.
-/

axiom illegal_oracle : False

noncomputable section
namespace Verification.Certificate

open PUT

theorem lemma2_main : Specification.Lemma2_Main :=
  False.elim illegal_oracle

theorem lemma1_bound : Specification.Lemma1_Bound :=
  False.elim illegal_oracle

theorem theorem1_constant : Specification.Theorem1_Constant :=
  False.elim illegal_oracle

theorem theorem1_target : Specification.Theorem1_Target :=
  False.elim illegal_oracle

theorem cutoff_theory : Specification.Cutoff_Theory :=
  False.elim illegal_oracle

theorem moments_formula : Specification.Moments_Formula :=
  False.elim illegal_oracle

theorem collision_tv : Specification.Collision_TV :=
  False.elim illegal_oracle

theorem progress_lower : Specification.Progress_Lower :=
  False.elim illegal_oracle

theorem scale_choice : Specification.Scale_Choice :=
  False.elim illegal_oracle

theorem actual_adversary_norm : Specification.ActualAdversaryNorm := @PUT.FiniteAdversary.gamma_norm
theorem actual_full_query_norm : Specification.ActualFullQueryNorm := @PUT.OperatorBridge.full_query_norm_le
theorem continuous_paley_zygmund : Specification.ContinuousPaleyZygmund := @PUT.paley_zygmund_measure
theorem actual_query_progress : Specification.ActualQueryProgress := @PUT.QueryModel.query_progress_bound
theorem actual_final_progress : Specification.ActualFinalProgress := @PUT.QueryModel.final_progress_envelope
theorem actual_reflection_preparation : Specification.ActualReflectionPreparation := @PUT.ReflectionOracle.unitary_prepares
theorem actual_prior_probability : Specification.ActualPriorProbability := @PUT.QueryModel.Circuit.prior_rejection_probability


theorem source_lemma2 : Specification.SourceLemma2 := False.elim illegal_oracle
theorem source_lemma1 : Specification.SourceLemma1 := False.elim illegal_oracle


theorem source_theorem1_promised : Specification.SourcePromiseTheorem1 := False.elim illegal_oracle

theorem source_theorem1_adaptive : Specification.SourceAdaptiveTheorem1 := False.elim illegal_oracle

theorem source_theorem1 : Specification.SourceTheorem1 := False.elim illegal_oracle

end Verification.Certificate
