import Paper18.Category.DrinfeldEquivalenceMapEquivalence

/-! # Actual unit and composition coherence of the center transport -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Functor
universe v u v' u' v'' u'' v''' u'''
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {E : Type u''} [Category.{v''} E] [MonoidalCategory E]
  {K : Type u'''} [Category.{v'''} K] [MonoidalCategory K]
  (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]
  (G : D ⥤ E) [G.Monoidal] [G.IsEquivalence]
  (H : E ⥤ K) [H.Monoidal] [H.IsEquivalence]

/-- Composition of center lifts satisfies the actual associativity
comparison, with no additional coherence data. -/
theorem compositionIso_assoc :
    isoWhiskerRight (compositionIso F G) (map H) ≪≫
      compositionIso (F ⋙ G) H ≪≫ mapNatIso (Functor.associator F G H) =
    Functor.associator (map F) (map G) (map H) ≪≫
      isoWhiskerLeft (map F) (compositionIso G H) ≪≫ compositionIso F (G ⋙ H) := by
  apply Iso.ext
  ext Z
  simp [compositionIso, centralIso, mapNatIso]

theorem compositionIso_leftUnit :
    compositionIso (𝟭 C) F ≪≫ mapNatIso F.leftUnitor =
      isoWhiskerRight (identityIso C) (map F) ≪≫ (map F).leftUnitor := by
  apply Iso.ext
  ext Z
  simp [compositionIso, identityIso, centralIso, mapNatIso]

theorem compositionIso_rightUnit :
    compositionIso F (𝟭 D) ≪≫ mapNatIso F.rightUnitor =
      isoWhiskerLeft (map F) (identityIso D) ≪≫ (map F).rightUnitor := by
  apply Iso.ext
  ext Z
  simp [compositionIso, identityIso, centralIso, mapNatIso]

end Paper18.Category.DrinfeldEquivalence
