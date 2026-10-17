import CounterFreeHDA.EffectiveRecognizer

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))

def tableLanguage {U V : Cube Lab k} (p : Word U V) : Prop := wordImage C image p ∈ K

/-- The effective construction takes precisely finite multiplication tables,
finite elementary-image tables and finite accepting tables. No source language,
ST representative, or unbounded context decision is a runtime input. -/
def tableHDA : HDA.{u,max u v} Lab k :=
  idealHDA (canonicalCategory C image K (tableLanguage C image K) (fun _ => Iff.rfl))
    (canonicalOrder C image K (tableLanguage C image K) (fun _ => Iff.rfl))
    (fun s => wordClass C image K (.cons s (.nil _)))
    {I | canonicalAccept C image K I}

end CounterFreeHDA.Cubical.Effective

namespace CounterFreeHDA.Cubical.FinitePomsetRecognizer
universe u v
open Effective
variable {Lab : Type u} {k h : ℕ} [Fintype Lab] [DecidableEq Lab] {L : Set (IntervalPom Lab)}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (image : ∀ {U V}, Step U V → G.D.Hom U V)
    (himage : ∀ {U V} (s : Step U V), image s = G.stepImage s)
    (K : ∀ {U V}, Finset (G.D.Hom U V))
    (hK : ∀ {U V} (a : G.D.Hom U V), a ∈ K ↔ a ∈ G.K)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)

theorem effective_hda_eq_table : (G.effectiveOrdered image himage K hK downward).hda = tableHDA G.D image K := by
  let F := G.effectiveOrdered image himage K hK downward
  have he : (fun {U V} (s : Step U V) => F.stepImage s) =
      (fun {U V} (s : Step U V) => wordClass G.D image K (.cons s (.nil V))) := by
    funext U V s
    exact G.effective_step image himage K hK downward s
  change idealHDA F.C F.order F.stepImage F.J = _
  rw [he]
  rfl

include himage hK downward in
/-- Correctness of the finite-table algorithm, not just classical finiteness
of an abstract construction. Cells and face restrictions can be enumerated by
Effective.diagramEnum and Effective.restrictRaw; the multiplication/order data
are the executable canonical class tables. -/
theorem effective_realization (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    Finite (Σ U, (tableHDA G.D image K).Cell U) ∧
    (tableHDA G.D image K).LangPom = L ∧
    (tableHDA G.D image K).toPrecubical.CounterFreePom := by
  rw [← G.effective_hda_eq_table image himage K hK downward]
  let F := G.effectiveOrdered image himage K hK downward
  have hf : Finite (Σ U, F.hda.Cell U) := by
    change Finite (Σ U : Cube Lab k, Σ S : Cube Lab k, IdealDiagram F.C F.order F.stepImage S U)
    infer_instance
  exact ⟨hf,F.language_eq withinWidth,F.counterFreePom⟩

include himage hK downward in
/-- The effective finite-table output also has the paper's explicit bound. -/
theorem effective_uniform_bound (hh : 1 ≤ h) (n : ℕ) (hn : 2*k+h ≤ n)
    (U : Cube Lab k) (x : (tableHDA G.D image K).Cell U) (P : EndoPom (cubeInterface U)) :
    (tableHDA G.D image K).toPrecubical.dPom (V := U) x (P.pow n).pom =
      (tableHDA G.D image K).toPrecubical.dPom x (P.pow (n+1)).pom := by
  revert x
  rw [← G.effective_hda_eq_table image himage K hK downward]
  intro x
  ext y
  exact (G.effectiveOrdered image himage K hK downward).full_power_stable P x y n hn (by omega)

end CounterFreeHDA.Cubical.FinitePomsetRecognizer
