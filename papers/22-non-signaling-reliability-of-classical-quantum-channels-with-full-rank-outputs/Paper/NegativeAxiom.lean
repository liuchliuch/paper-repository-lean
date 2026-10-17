import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion
import Paper22.OneShot
import Paper.Statements

/-!
# Negative control: unauthorized axiom
-/

axiom unauthorized_axiom : False

namespace Paper22.Paper

theorem lemma_1_effect_completion : Paper22.PaperStatements.lemma_1_effect_completion := by
  intro n d M hM K hK q hq0 hq1 T hT hA
  exact False.elim unauthorized_axiom

end Paper22.Paper
