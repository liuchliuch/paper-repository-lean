import Paper22.Basic
import Paper22.Programs
import Paper22.EffectCompletion
import Paper22.OneShot
import Paper.Statements

/-!
# Solution proofs for official Comparator

These are the real production proofs of the paper's numbered results.
They must match the statements in `Paper.Challenge` exactly.
-/

namespace Paper22.Paper

/-- **Lemma 1 (Effect completion).** -/
theorem lemma_1_effect_completion : Paper22.PaperStatements.lemma_1_effect_completion :=
  fun n d M hM K hK q hq0 hq1 T hT hA =>
    Paper22.lemma_effect_completion M hM K hK q hq0 hq1 T hT hA

/-- **Theorem 1 (One-shot comparison).** -/
theorem theorem_1_one_shot : Paper22.PaperStatements.theorem_1_one_shot :=
  fun n d V M hM => Paper22.theorem_one_shot V M hM

/-- **Theorem 2 (Reliability without activation).** -/
theorem theorem_2_reliability : Paper22.PaperStatements.theorem_2_reliability :=
  fun extMeta n d W hW R hR0 hRC =>
    Paper22.theorem_2_reliability_source_of_meta extMeta W hW hR0 hRC

/-- Preserved earlier transfer theorem with both cited inputs quantified. -/
theorem theorem_2_reliability_legacy_two_inputs :
    Paper22.PaperStatements.theorem_2_reliability_legacy_two_inputs :=
  fun extMeta extAct n d W hW R hR0 hRC =>
    Paper22.theorem_2_reliability_source extMeta extAct W hW hR0 hRC

end Paper22.Paper
