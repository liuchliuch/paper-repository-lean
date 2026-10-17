import CounterFreeHDA.StableCornerImages

namespace CounterFreeHDA.Cubical.Arrow
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U V S : Cube Lab k}

def EndpointCriterion (A : Arrow U V) (hw : A.pom.val.WidthLE k)
    (x : IdealDiagram F.C F.order F.stepImage S U) (y : IdealDiagram F.C F.order F.stepImage S V) : Prop :=
  ∀ (T W : Cube Lab k) (α : Face T U) (β : Face W V) (hc : A.Compatible α β),
    LowerSetAction.act F.order (x.val α) (F.map (A.corner hw α β hc)) ⊆ y.val β

/-- Proposition 3.6 with arbitrary named, fully labeled source and target
cubes, retaining the entire endpoint diagrams. -/
theorem endpoint_iff (A : Arrow U V) (hw : A.pom.val.WidthLE k)
    (x : IdealDiagram F.C F.order F.stepImage S U) (y : IdealDiagram F.C F.order F.stepImage S V)
    (hint : ∃ e, ¬ A.pom.val.inSrc e ∧ ¬ A.pom.val.inTgt e) :
    y ∈ (ideal F.C F.order F.stepImage S).dPom x A.pom ↔ A.EndpointCriterion F hw x y := by
  rcases A with ⟨P,hS,hT⟩
  change P.val.WidthLE k at hw
  change (∃ e : Fin P.n, ¬ P.val.inSrc e ∧ ¬ P.val.inTgt e) at hint
  have hs : sourceCube P.val (hw.source_bound P.property) = U := Cube.interface_injective hS
  have ht : targetCube P.val (hw.target_bound P.property) = V := Cube.interface_injective hT
  subst U
  subst V
  exact Endpoint.lemma_3_6 F P.val P.property hw (hw.source_bound P.property) (hw.target_bound P.property) x y hint

end CounterFreeHDA.Cubical.Arrow
