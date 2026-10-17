import CounterFreeHDA.Realization
import CounterFreeHDA.RecognizerFromCategory

namespace CounterFreeHDA.Cubical
universe u v w
variable {Lab : Type u} [Fintype Lab] {k h : ℕ} {L : Set (IntervalPom Lab)} {O : Type v}

/-- Original paper input: an actual bounded-pomset functor into an arbitrary
finite recognizing category, whose object map may identify interface types. -/
theorem theorem_1_1_fromFunctor (D : FinCat.{v,w} O)
    (G : Recognition.Functor (PomsetCategory.category Lab k) (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ G.map (PomsetCategory.mk A) ∈ K)
    (hD : D.AperiodicExponent h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧
      X.toPrecubical.CounterFreePom ∧
      ∀ n, 2*k+h ≤ n → ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U)),
        X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom :=
  theorem_1_1 (FinitePomsetRecognizer.ofFunctor D G K recognises hD) hh downward withinWidth

end CounterFreeHDA.Cubical
