import Paper18.Category.FixedBoundaryRegularAction
import Paper18.Category.RepresentationFunctionAverage
import Paper18.Category.RelativeTensorFree

/-! # Actual faithfulness of free extension by a regular algebra -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u
namespace Paper18.Category
namespace InternalModule
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- A split actual algebra unit makes the actual free-module functor
faithful, by inserting the unit and then applying its retraction. -/
def freeFunctorFaithfulOfSplitUnit (a : A ⟶ 𝟙_ C) (ha : η[A] ≫ a = 𝟙 _) :
    (freeFunctor (A := A)).Faithful where
  map_injective {X Y} {f g} h := by
    let r : A ⊗ Y ⟶ Y := a ▷ Y ≫ (λ_ Y).hom
    have hr : RelativeTensor.freeUnit Y ≫ r = 𝟙 Y := by
      dsimp only [RelativeTensor.freeUnit, r]
      simp only [Category.assoc]
      rw [← comp_whiskerRight_assoc, ha, id_whiskerRight, Category.id_comp,
        Iso.inv_hom_id]
    have hh := congrArg (fun k : free A X ⟶ free A Y =>
      RelativeTensor.freeUnit X ≫ k.hom ≫ r) h
    change RelativeTensor.freeUnit X ≫ (freeMap f).hom ≫ r =
      RelativeTensor.freeUnit X ≫ (freeMap g).hom ≫ r at hh
    rw [RelativeTensor.freeUnit_naturality_assoc,
      RelativeTensor.freeUnit_naturality_assoc, hr, Category.comp_id, Category.comp_id] at hh
    exact hh

end InternalModule
namespace FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type} [Group G] [Fintype G] (F : FDRep ℂ G ⥤ C) [F.Monoidal]

/-- The actual finite-group mean retracts the transported regular unit. -/
def regularAugmentation : regularAlgebra F ⟶ 𝟙_ C :=
  F.map Representation.functionsAverage ≫ (Functor.Monoidal.εIso F).inv

@[reassoc (attr := simp)]
theorem regular_one_augmentation : η[regularAlgebra F] ≫ regularAugmentation F = 𝟙 _ := by
  change ((Functor.Monoidal.εIso F).hom ≫ F.map Representation.functionsOne) ≫
    (F.map Representation.functionsAverage ≫ (Functor.Monoidal.εIso F).inv) = 𝟙 _
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, Representation.functionsOne_average, F.map_id,
    Category.id_comp, Iso.hom_inv_id]

/-- Free extension by the actual regular algebra is faithful, whether
or not that algebra is transparent. -/
instance regularFreeFaithful : (InternalModule.freeFunctor (A := regularAlgebra F)).Faithful :=
  InternalModule.freeFunctorFaithfulOfSplitUnit (regularAugmentation F)
    (regular_one_augmentation F)

end FixedBoundary
end Paper18.Category
