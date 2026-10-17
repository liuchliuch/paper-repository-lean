import CounterFreeHDA.BoundedPowers

namespace CounterFreeHDA.Cubical.Precubical
universe u v
variable {Lab : Type u} {k : ℕ} (X : Precubical.{u,v} Lab k)
    {U V W : Cube Lab k}

/-- Isomorphic actual interval-pomset labels have identical full endpoint
relations, independently of the chosen ST word. -/
theorem dPom_iso {P Q : IntervalPom Lab} (φ : PomsetIso P.val Q.val) (x : X.Cell U) :
    X.dPom (V := V) x P = X.dPom x Q := by
  ext y
  constructor
  · rintro ⟨p,hr,⟨ψ⟩⟩; exact ⟨p,hr,⟨ψ.trans φ⟩⟩
  · rintro ⟨p,hr,⟨ψ⟩⟩; exact ⟨p,hr,⟨ψ.trans φ.symm⟩⟩

/-- Every reachable actual label has width bounded by the HDA dimension. -/
theorem reachable_width {P : IntervalPom Lab} {x : X.Cell U} {y : X.Cell V}
    (hr : y ∈ X.dPom x P) : P.val.WidthLE k := by
  obtain ⟨p,_,⟨φ⟩⟩ := hr
  apply p.label_width.ofEmbedding φ.toEquiv.symm.toEmbedding
  intro e f hef
  exact (φ.symm.prec_iff e f).mp hef

/-- Genuine pomset gluing composes the full endpoint relations, with all
nondeterministic intermediate cells retained. -/
theorem dPom_comp (A : BoundedArrow U V) (B : BoundedArrow V W) (x : X.Cell U) (z : X.Cell W) :
    z ∈ X.dPom x (A.comp B).pom ↔ ∃ y : X.Cell V, y ∈ X.dPom x A.pom ∧ z ∈ X.dPom y B.pom := by
  constructor
  · intro hr
    obtain ⟨m,hx,hz⟩ := (A.comp B).toArrow.map_of_dPom x z hr
    let l := (Arrow.leftInclusion A.toArrow B.toArrow).comp m
    let r := (Arrow.rightInclusion A.toArrow B.toArrow).comp m
    let y := l.app A.toArrow.targetCell
    have hy : r.app B.toArrow.sourceCell = y := congrArg m.app (Arrow.inclusion_seam A.toArrow B.toArrow).symm
    refine ⟨y,(A.toArrow.lemma_3_1_b (Y := X) A.width x y).mpr ⟨l,?_,rfl⟩,
      (B.toArrow.lemma_3_1_b (Y := X) B.width y z).mpr ⟨r,hy,?_⟩⟩
    · exact (congrArg m.app (Arrow.leftInclusion_source A.toArrow B.toArrow)).trans hx
    · exact (congrArg m.app (Arrow.rightInclusion_target A.toArrow B.toArrow)).trans hz
  · rintro ⟨y,ha,hb⟩
    obtain ⟨l,hx,hy⟩ := A.toArrow.map_of_dPom x y ha
    obtain ⟨r,hy',hz⟩ := B.toArrow.map_of_dPom y z hb
    have hs := hy.trans hy'.symm
    let m := A.toArrow.glueMap B.toArrow l r hs
    apply ((A.comp B).toArrow.lemma_3_1_b (Y := X) (A.comp B).width x z).mpr
    exact ⟨m,(A.toArrow.glueMap_source B.toArrow l r hs).trans hx,
      (A.toArrow.glueMap_target B.toArrow l r hs).trans hz⟩

end CounterFreeHDA.Cubical.Precubical
