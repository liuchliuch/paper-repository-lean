import CounterFreeHDA.InterfaceCounterFree
import CounterFreeHDA.OriginalFunctorRealization
import CounterFreeHDA.EffectiveHDA

namespace CounterFreeHDA.Cubical.FinitePomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)

/-- The refined bound applies to exactly the same constructed HDA used in
Theorem 1.1; the environment remains Cube Lab k. -/
theorem interface_uniform_bound (hh : 1 ≤ h) (U : Cube Lab k)
    (x : (G.ordered downward).hda.Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    (G.ordered downward).hda.toPrecubical.dPom (V := U) x (P.pow n).pom =
      (G.ordered downward).hda.toPrecubical.dPom x (P.pow (n+1)).pom :=
  (G.ordered downward).interface_endpoint_stable hh U x P n hn

variable [Fintype Lab] [DecidableEq Lab]
    (image : ∀ {U V}, Step U V → G.D.Hom U V)
    (himage : ∀ {U V} (s : Step U V), image s = G.stepImage s)
    (K : ∀ {U V}, Finset (G.D.Hom U V))
    (hK : ∀ {U V} (a : G.D.Hom U V), a ∈ K ↔ a ∈ G.K)

include himage hK downward in
/-- The identical finite-table output also has the interface-specific bound;
there is no new construction and no width-by-interface premise. -/
theorem effective_interface_uniform_bound (hh : 1 ≤ h) (U : Cube Lab k)
    (x : (Effective.tableHDA G.D image K).Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    (Effective.tableHDA G.D image K).toPrecubical.dPom (V := U) x (P.pow n).pom =
      (Effective.tableHDA G.D image K).toPrecubical.dPom x (P.pow (n+1)).pom := by
  revert x
  rw [← G.effective_hda_eq_table image himage K hK downward]
  intro x
  exact (G.effectiveOrdered image himage K hK downward).interface_endpoint_stable hh U x P n hn

end CounterFreeHDA.Cubical.FinitePomsetRecognizer

namespace CounterFreeHDA.Cubical
universe u v w
variable {Lab : Type u} [Fintype Lab] {k h : ℕ} {L : Set (IntervalPom Lab)} {O : Type v}

/-- Original functor input, with the ambient width retained and the sharper
bound simultaneously at every interface of the same ideal-diagram HDA. -/
theorem theorem_1_1_fromFunctor_interface (D : FinCat.{v,w} O)
    (G : Recognition.Functor (PomsetCategory.category Lab k) (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ G.map (PomsetCategory.mk A) ∈ K)
    (hD : D.AperiodicExponent h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧
      X.toPrecubical.CounterFreePom ∧
      ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U))
        (n : ℕ), 2*U.dim+h ≤ n →
        X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom := by
  let R := FinitePomsetRecognizer.ofFunctor D G K recognises hD
  let F := R.ordered downward
  have hf : Finite (Σ U, F.hda.Cell U) := by
    change Finite (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram F.C F.order F.stepImage S U)
    infer_instance
  exact ⟨F.hda,hf,F.language_eq withinWidth,F.counterFreePom,fun U x P n hn =>
    F.interface_endpoint_stable hh U x P n hn⟩

end CounterFreeHDA.Cubical
