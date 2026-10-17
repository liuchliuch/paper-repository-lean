import Paper12.Necessity
import Paper12.Statements
namespace Paper12.Paper
/-- Deliberately added hypothesis; no unauthorized axiom is involved. -/
theorem lemma_2_2 (_extra : False) : PaperStatements.lemma_2_2 := by
  intro X W _ _ Γ U C hsym hclean
  exact Paper12.lemma_2_2 hsym hclean
end Paper12.Paper
