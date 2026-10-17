import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion
import Paper22.OneShot
import Paper.Statements

/-!
# Negative control: extra premise

The theorem statement carries an extra premise so its type does not match
the challenge statement. Official Comparator must reject it.
-/

namespace Paper22.Paper

theorem lemma_1_effect_completion
    (cheat : True) : Paper22.PaperStatements.lemma_1_effect_completion := by
  intro n d M hM K hK q hq0 hq1 T hT hA
  exact Paper22.lemma_effect_completion M hM K hK q hq0 hq1 T hT hA

end Paper22.Paper
