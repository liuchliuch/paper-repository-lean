import Verification.Statements

/-!
# Trusted Comparator challenge

Placeholders are obligations only: same names and types as
`Verification.Solution`, each body `by sorry`.
-/

noncomputable section
namespace Verification.Certificate

open PUT

theorem lemma2_main : Specification.Lemma2_Main := by sorry
theorem lemma1_bound : Specification.Lemma1_Bound := by sorry
theorem theorem1_constant : Specification.Theorem1_Constant := by sorry
theorem theorem1_target : Specification.Theorem1_Target := by sorry
theorem cutoff_theory : Specification.Cutoff_Theory := by sorry
theorem moments_formula : Specification.Moments_Formula := by sorry
theorem collision_tv : Specification.Collision_TV := by sorry
theorem progress_lower : Specification.Progress_Lower := by sorry
theorem scale_choice : Specification.Scale_Choice := by sorry

theorem actual_adversary_norm : Specification.ActualAdversaryNorm := by sorry
theorem actual_full_query_norm : Specification.ActualFullQueryNorm := by sorry
theorem continuous_paley_zygmund : Specification.ContinuousPaleyZygmund := by sorry
theorem actual_query_progress : Specification.ActualQueryProgress := by sorry
theorem actual_final_progress : Specification.ActualFinalProgress := by sorry
theorem actual_reflection_preparation : Specification.ActualReflectionPreparation := by sorry
theorem actual_prior_probability : Specification.ActualPriorProbability := by sorry


theorem source_lemma2 : Specification.SourceLemma2 := by sorry
theorem source_lemma1 : Specification.SourceLemma1 := by sorry


theorem source_theorem1_promised : Specification.SourcePromiseTheorem1 := by sorry

theorem source_theorem1_adaptive : Specification.SourceAdaptiveTheorem1 := by sorry

theorem source_theorem1 : Specification.SourceTheorem1 := by sorry

end Verification.Certificate
