import Paper18.Category.DrinfeldEquivalenceMapComposition

/-! # The actual induced braided equivalence of Drinfeld centers -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

/-- The inverse tensor equivalence, together with actual transported
unit and counit comparisons, supplies an inverse to the center lift. -/
instance map_isEquivalence : (map F).IsEquivalence := by
  let E := F.asEquivalence
  letI : E.inverse.Monoidal := E.inverseMonoidal
  let G := E.inverse
  haveI : NatTrans.IsMonoidal E.unitIso.symm.hom := by
    change NatTrans.IsMonoidal E.unitIso.inv
    infer_instance
  haveI : NatTrans.IsMonoidal E.counitIso.hom := by
    change NatTrans.IsMonoidal E.counit
    infer_instance
  let a : map F ⋙ map G ≅ 𝟭 (Center C) :=
    compositionIso F G ≪≫ mapNatIso E.unitIso.symm ≪≫ identityIso C
  let b : map G ⋙ map F ≅ 𝟭 (Center D) :=
    compositionIso G F ≪≫ mapNatIso E.counitIso ≪≫ identityIso D
  exact Functor.IsEquivalence.mk' (map G) a.symm b

/-- The induced equivalence retains the actual strong monoidal braided
functor constructed from inverse-and-counit transport. -/
def equivalence : Center C ≌ Center D := (map F).asEquivalence

instance equivalence_monoidal : (equivalence F).functor.Monoidal :=
  inferInstanceAs (map F).Monoidal

instance equivalence_braided : (equivalence F).functor.Braided :=
  inferInstanceAs (map F).Braided

end Paper18.Category.DrinfeldEquivalence
