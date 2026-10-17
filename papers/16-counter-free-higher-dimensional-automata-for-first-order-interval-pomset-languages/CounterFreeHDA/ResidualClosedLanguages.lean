import CounterFreeHDA.UnaryLanguageCore

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem residual_C0_explicit : residualLanguage Completion.emptyCube (2 : Fin 4) =
    {Q : Tail Completion.emptyCube | 0 < Q.pom.n ∨
      IntervalPomIso Q.pom (identityPom Unit 0 Fin.elim0)} := by
  rw [residual_C0]
  ext Q
  constructor
  · intro _
    by_cases h : 0 < Q.pom.n
    · exact Or.inl h
    · right
      let E : EndoPom (cubeInterface Completion.emptyCube) := { pom := Q.pom,source := Q.source,target := Q.target }
      exact ⟨E.isoIdentityOfSizeEq (by change Q.pom.n = 0; omega)⟩
  · intro _; trivial

end CounterFreeHDA.Appendix.Residual
