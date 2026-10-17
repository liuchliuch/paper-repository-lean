import CounterFreeHDA.CoproductCounterFree
import CounterFreeHDA.Size

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} [Fintype Lab] {k h : ℕ} {L : Set (IntervalPom Lab)}

/-- **Theorem 1.1, mathematical realization.** From the original finite
aperiodic recognizer, construct a finite actual HDA with exactly L and with
uniform full pomset endpoint stabilization. None of these conclusions is a
premise. The separate effective implementation is recorded independently. -/
theorem theorem_1_1_core (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom := by
  let F := G.ordered downward
  have hf : Finite (Σ U, F.hda.Cell U) := by
    change Finite (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram F.C F.order F.stepImage S U)
    infer_instance
  exact ⟨F.hda,hf,F.language_eq withinWidth,F.counterFreePom⟩

/-- Theorem 1.1 with the paper's explicit uniform bound at every greater
exponent. The original assumption h >= 1 also covers dimension zero. -/
theorem theorem_1_1 (G : FinitePomsetRecognizer.{u,v} (k := k) L h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧
      X.toPrecubical.CounterFreePom ∧
      ∀ n, 2*k+h ≤ n → ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U)),
        X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom := by
  let F := G.ordered downward
  have hf : Finite (Σ U, F.hda.Cell U) := by
    change Finite (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram F.C F.order F.stepImage S U)
    infer_instance
  refine ⟨F.hda,hf,F.language_eq withinWidth,F.counterFreePom,?_⟩
  intro n hn U x P
  ext y
  exact F.full_power_stable P x y n hn (by omega)

end CounterFreeHDA.Cubical
