import CounterFreeHDA.SeedColoring

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V) (J : ∀ {S U}, Set (C.Hom S U))

def componentInclusion (S : Cube Lab k) : Map (ideal C ord image S) (idealHDA C ord image J).toPrecubical where
  app x := ⟨S,x⟩
  natural _ _ := rfl

/-- The actual coproduct face graph never changes its coefficient component. -/
theorem run_component {U V S T : Cube Lab k} (p : Word U V)
    (x : IdealDiagram C ord image S U) (y : IdealDiagram C ord image T V)
    (hr : (idealHDA C ord image J).Run p ⟨S,x⟩ ⟨T,y⟩) :
    ∃ h : S = T, (ideal C ord image S).Run p x (h.symm ▸ y) := by
  induction p generalizing S T with
  | nil U =>
    have hh := ((idealHDA C ord image J).toPrecubical.run_nil_iff _ _).mp hr
    have hs : S = T := congrArg Sigma.fst hh
    subst T
    change (⟨S,x⟩ : Σ R, IdealDiagram C ord image R U) = ⟨S,y⟩ at hh
    have hx : x = y := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    subst y
    refine ⟨rfl,?_⟩
    change (ideal C ord image S).Run (.nil U) x x
    exact ((ideal C ord image S).run_nil_iff x x).mpr rfl
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨⟨R,z⟩,hx,hr'⟩ := ((idealHDA C ord image J).toPrecubical.run_start_iff f hl hd p _ _).mp hr
      have hs : S = R := congrArg Sigma.fst hx
      subst R
      have hx' : x = z.restrict f := by simpa only [idealHDA,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hx
      subst x
      obtain ⟨ht,hrest⟩ := ih z y hr'
      subst T
      exact ⟨rfl,.start f hl hd hrest⟩
    | stop f hu hd =>
      have hr' := ((idealHDA C ord image J).toPrecubical.run_stop_iff f hu hd p _ _).mp hr
      obtain ⟨ht,hrest⟩ := ih (x.restrict f) y hr'
      subst T
      exact ⟨rfl,.stop f hu hd hrest⟩

end CounterFreeHDA.Cubical
