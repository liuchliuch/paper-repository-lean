import CounterFreeHDA.EffectiveHDA

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
attribute [local instance] faceFintype faceDecidableEq lowerDecidable upperDecidable
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))

abbrev TableCategory := canonicalCategory C image K (tableLanguage C image K) (fun _ => Iff.rfl)
abbrev TableOrder := canonicalOrder C image K (tableLanguage C image K) (fun _ => Iff.rfl)
def tableImage {U V : Cube Lab k} (s : Step U V) : (TableCategory C image K).Hom U V :=
  wordClass C image K (.cons s (.nil V))

instance tableOrderDecidable {U V : Cube Lab k} (a b : (TableCategory C image K).Hom U V) :
    Decidable ((TableOrder C image K).homLE a b) := canonicalLEDecidable C image K a b

/-- All actual cells are encoded by finite arrays in this computably finite
type, with admissibility decided from the computed finite class tables. -/
abbrev CellCode (U : Cube Lab k) := Σ S : Cube Lab k,
  {d : RawDiagram (TableCategory C image K) S U //
    d ∈ diagramEnum (TableCategory C image K) (TableOrder C image K) (tableImage C image K) S U}

def decodeCell {U : Cube Lab k} (c : CellCode C image K U) : (tableHDA C image K).Cell U :=
  ⟨c.1,toDiagram (TableCategory C image K) (TableOrder C image K) (tableImage C image K) c.2.val
    (diagramEnum_sound (TableCategory C image K) (TableOrder C image K) (tableImage C image K) c.2.property)⟩

theorem decodeCell_bijective (U : Cube Lab k) : Function.Bijective (decodeCell C image K (U := U)) := by
  constructor
  · rintro ⟨S,d,hd⟩ ⟨T,e,he⟩ h
    have hST : S = T := congrArg Sigma.fst h
    subst T
    have hz : toDiagram (TableCategory C image K) (TableOrder C image K) (tableImage C image K) d
        (diagramEnum_sound _ _ _ hd) =
      toDiagram (TableCategory C image K) (TableOrder C image K) (tableImage C image K) e
        (diagramEnum_sound _ _ _ he) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hde : d = e := by
      funext V f
      apply Finset.coe_injective
      exact congrArg (fun z : IdealDiagram (TableCategory C image K) (TableOrder C image K) (tableImage C image K) S U => z.val f) hz
    subst e
    rfl
  · rintro ⟨S,z⟩
    obtain ⟨d,hd,hm,hz⟩ := diagramEnum_complete (TableCategory C image K) (TableOrder C image K) (tableImage C image K) z
    exact ⟨⟨S,d,hm⟩,congrArg (fun z => (⟨S,z⟩ : (tableHDA C image K).Cell U)) hz⟩

def restrictCode {U V : Cube Lab k} (f : Face U V) (c : CellCode C image K V) : CellCode C image K U :=
  ⟨c.1,restrictRaw (TableCategory C image K) f c.2.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    restrictRaw_admissible (TableCategory C image K) (TableOrder C image K) (tableImage C image K) f c.2.val
      (diagramEnum_sound _ _ _ c.2.property)⟩⟩

/-- Every computed face restriction decodes to the actual presheaf face map. -/
theorem restrictCode_correct {U V : Cube Lab k} (f : Face U V) (c : CellCode C image K V) :
    decodeCell C image K (restrictCode C image K f c) = (tableHDA C image K).face f (decodeCell C image K c) := by
  apply congrArg (fun z => (⟨c.1,z⟩ : (tableHDA C image K).Cell U))
  apply IdealDiagram.ext
  funext W g
  rfl

end CounterFreeHDA.Cubical.Effective
