import CounterFreeHDA.EffectiveFaces

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
attribute [local instance] faceFintype faceDecidableEq

instance lowerDecidable {U V : Cube Lab k} (f : Face U V) : Decidable f.Lower := by
  unfold Face.Lower
  infer_instance
instance upperDecidable {U V : Cube Lab k} (f : Face U V) : Decidable f.Upper := by
  unfold Face.Upper
  infer_instance

variable (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V)
    [decLE : ∀ {U V} (a b : C.Hom U V), Decidable (ord.homLE a b)]

abbrev RawDiagram (S U : Cube Lab k) := ∀ V : Cube Lab k, Face V U → Finset (C.Hom S V)

def Admissible {S U : Cube Lab k} (d : RawDiagram C S U) : Prop :=
  (∀ V (f : Face V U) a b, a ∈ d V f → ord.homLE b a → b ∈ d V f) ∧
  (∀ V W (f : Face V W) (g : Face W U),
    if hf : f.Lower ∧ W.dim = V.dim+1 then
      ∀ a b, a ∈ d V (f.comp g) → ord.homLE b (C.comp a (image (.start f hf.1 hf.2))) → b ∈ d W g
    else True) ∧
  (∀ V W (f : Face V W) (g : Face W U),
    if hf : f.Upper ∧ W.dim = V.dim+1 then
      ∀ a b, a ∈ d W g → ord.homLE b (C.comp a (image (.stop f hf.1 hf.2))) → b ∈ d V (f.comp g)
    else True)

instance admissibleDecidable {S U : Cube Lab k} (d : RawDiagram C S U) :
    Decidable (Admissible C ord image d) := by
  unfold Admissible
  infer_instance

/-- Executable exhaustive enumeration of admissible finite coefficient
arrays, using only finite tables, equality and the supplied order decider. -/
def diagramEnum (S U : Cube Lab k) : Finset (RawDiagram C S U) :=
  Finset.univ.filter (Admissible C ord image)

def toDiagram {S U : Cube Lab k} (d : RawDiagram C S U) (hd : Admissible C ord image d) :
    IdealDiagram C ord image S U where
  val f := ↑(d _ f)
  lower f := fun {a b} ha hba => hd.1 _ f _ _ ha hba
  start f hl hdim g := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := (LowerSetAction.mem_act ord).mp hb
    exact (dif_pos (show f.Lower ∧ _ from ⟨hl,hdim⟩) ▸ hd.2.1 _ _ f g) a b ha hab
  stop f hu hdim g := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := (LowerSetAction.mem_act ord).mp hb
    exact (dif_pos (show f.Upper ∧ _ from ⟨hu,hdim⟩) ▸ hd.2.2 _ _ f g) a b ha hab

theorem diagramEnum_sound {S U : Cube Lab k} {d : RawDiagram C S U}
    (hd : d ∈ diagramEnum C ord image S U) : Admissible C ord image d := (Finset.mem_filter.mp hd).2

/-- Completeness is a proof about the executable enumeration. Choice is used
only here to encode an arbitrary set-valued semantic diagram as finite data. -/
theorem diagramEnum_complete {S U : Cube Lab k} (z : IdealDiagram C ord image S U) :
    ∃ (d : RawDiagram C S U) (hd : Admissible C ord image d),
      d ∈ diagramEnum C ord image S U ∧ toDiagram C ord image d hd = z := by
  classical
  let d : RawDiagram C S U := fun V f => (z.val f).toFinset
  have hd : Admissible C ord image d := by
    refine ⟨?_,?_,?_⟩
    · intro V f a b ha hab
      exact Set.mem_toFinset.mpr (z.lower f (Set.mem_toFinset.mp ha) hab)
    · intro V W f g
      split_ifs with hf
      · intro a b ha hab
        exact Set.mem_toFinset.mpr (z.start f hf.1 hf.2 g
          ((LowerSetAction.mem_act ord).mpr ⟨a,Set.mem_toFinset.mp ha,hab⟩))
    · intro V W f g
      split_ifs with hf
      · intro a b ha hab
        exact Set.mem_toFinset.mpr (z.stop f hf.1 hf.2 g
          ((LowerSetAction.mem_act ord).mpr ⟨a,Set.mem_toFinset.mp ha,hab⟩))
  refine ⟨d,hd,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩,?_⟩
  apply IdealDiagram.ext
  funext V f
  change ↑((z.val f).toFinset) = z.val f
  exact Set.coe_toFinset _

/-- Every face restriction is an explicit reindexing of a finite array. -/
def restrictRaw {S U V : Cube Lab k} (f : Face U V) (d : RawDiagram C S V) : RawDiagram C S U :=
  fun W g => d W (g.comp f)

theorem restrictRaw_correct {S U V : Cube Lab k} (f : Face U V) (d : RawDiagram C S V)
    (hd : Admissible C ord image d) (hr : Admissible C ord image (restrictRaw C f d)) :
    toDiagram C ord image (restrictRaw C f d) hr = (toDiagram C ord image d hd).restrict f := by
  apply IdealDiagram.ext
  funext W g
  rfl

theorem restrictRaw_admissible {S U V : Cube Lab k} (f : Face U V) (d : RawDiagram C S V)
    (hd : Admissible C ord image d) : Admissible C ord image (restrictRaw C f d) := by
  obtain ⟨d',hd',_,hz⟩ := diagramEnum_complete C ord image ((toDiagram C ord image d hd).restrict f)
  have he : d' = restrictRaw C f d := by
    funext W g
    apply Finset.coe_injective
    change (toDiagram C ord image d' hd').val g = ((toDiagram C ord image d hd).restrict f).val g
    exact congrArg (fun z : IdealDiagram C ord image S U => z.val g) hz
  exact he ▸ hd'

end CounterFreeHDA.Cubical.Effective
