import Paper12.Statements
namespace Paper12.NegativeControl
axiom injectedFalse : False
end Paper12.NegativeControl
namespace Paper12.Paper
/-- Exact challenge type, with a forbidden axiom in its proof closure. -/
theorem lemma_2_2 : PaperStatements.lemma_2_2 := False.elim NegativeControl.injectedFalse
end Paper12.Paper
