import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion
import Paper22.OneShot
import Paper.Statements

/-!
# Comparator specification

Intentional proof holes for the independent Comparator challenge.
This module is excluded from the default build and must never be
imported by the proof library.
-/

namespace Paper22.Paper

/-- **Lemma 1 (Effect completion).** -/
theorem lemma_1_effect_completion : Paper22.PaperStatements.lemma_1_effect_completion := by
  sorry

/-- **Theorem 1 (One-shot comparison).** -/
theorem theorem_1_one_shot : Paper22.PaperStatements.theorem_1_one_shot := by
  sorry

/-- **Theorem 2 (Reliability without activation).** -/
theorem theorem_2_reliability : Paper22.PaperStatements.theorem_2_reliability := by
  sorry

end Paper22.Paper
