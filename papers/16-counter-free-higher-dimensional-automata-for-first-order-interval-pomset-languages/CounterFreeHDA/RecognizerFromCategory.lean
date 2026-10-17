import CounterFreeHDA.ActualCategory

namespace CounterFreeHDA.FinCat
universe u v w
variable {O : Type u} {O' : Type w}

/-- Pull back a finite category along an object map; objects need not be
preserved or mapped injectively by the original recognizing functor. -/
def pullback (D : FinCat.{u,v} O) (obj : O' → O) : FinCat O' where
  Hom U V := D.Hom (obj U) (obj V)
  id U := D.id (obj U)
  comp := D.comp
  id_comp := D.id_comp
  comp_id := D.comp_id
  assoc := D.assoc

theorem pullback_pow (D : FinCat.{u,v} O) (obj : O' → O) (U : O')
    (c : D.Hom (obj U) (obj U)) (n : ℕ) :
    FinCat.pow (C := D.pullback obj) c n = FinCat.pow (C := D) c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change D.comp (FinCat.pow (C := D.pullback obj) c n) c = D.comp (FinCat.pow (C := D) c n) c
    exact congrArg (fun a => D.comp a c) ih

theorem pullback_aperiodic (D : FinCat.{u,v} O) (obj : O' → O) {h : ℕ}
    (hD : D.AperiodicExponent h) : (D.pullback obj).AperiodicExponent h := by
  intro U c
  exact (pullback_pow D obj U c h).trans ((hD (obj U) c).trans (pullback_pow D obj U c (h+1)).symm)

end CounterFreeHDA.FinCat

namespace CounterFreeHDA.Cubical.FinitePomsetRecognizer
universe u v w
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)} {O : Type v}

/-- Adapt the original paper hypothesis, a functor from the actual bounded
pomset category into any finite category, to the concrete construction API. -/
noncomputable def ofFunctor (D : FinCat.{v,w} O)
    (G : Recognition.Functor (PomsetCategory.category Lab k) (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ G.map (PomsetCategory.mk A) ∈ K)
    (hD : D.AperiodicExponent h) : FinitePomsetRecognizer.{u,w} (k := k) L h where
  D := D.pullback G.obj
  map A := G.map (PomsetCategory.mk A)
  map_id := G.map_id
  map_comp A B := G.map_comp (PomsetCategory.mk A) (PomsetCategory.mk B)
  map_iso A B φ := congrArg G.map (Quotient.sound ⟨φ⟩)
  K := K
  recognises := recognises
  aperiodic := D.pullback_aperiodic G.obj hD

end CounterFreeHDA.Cubical.FinitePomsetRecognizer
