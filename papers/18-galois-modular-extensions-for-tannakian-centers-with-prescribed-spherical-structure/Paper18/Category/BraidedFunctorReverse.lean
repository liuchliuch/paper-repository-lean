import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Actual braided functors with both braidings reversed -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [bC : BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [bD : BraidedCategory D]
  (F : C ⥤ D) [F.Braided]

/-- Reversing source and target braidings retains the actual tensor
structure and actual braided functor. -/
def braidedFunctorReverse :
    letI : BraidedCategory C := reverseBraiding C
    letI : BraidedCategory D := reverseBraiding D
    F.Braided := by
  let hf : F.Braided := inferInstance
  have hb (X Y : C) := Functor.LaxBraided.braided (F := F) X Y
  letI : BraidedCategory C := reverseBraiding C
  letI : BraidedCategory D := reverseBraiding D
  refine { toMonoidal := hf.toMonoidal, braided := ?_ }
  intro X Y
  change Functor.LaxMonoidal.μ F X Y ≫ F.map (@BraidedCategory.braiding C _ _ bC Y X).inv =
    (@BraidedCategory.braiding D _ _ bD (F.obj Y) (F.obj X)).inv ≫
      Functor.LaxMonoidal.μ F Y X
  apply (cancel_mono (F.map (@BraidedCategory.braiding C _ _ bC Y X).hom)).mp
  rw [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  rw [Category.assoc, hb Y X, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Paper18.Category
