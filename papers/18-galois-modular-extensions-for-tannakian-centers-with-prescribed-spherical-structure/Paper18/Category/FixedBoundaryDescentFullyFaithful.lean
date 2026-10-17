import Paper18.Category.FixedBoundaryDescentAverage
import Paper18.Category.RepresentationFunctionAverage

/-! # Actual regular descent without a transparency hypothesis -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj Obj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [CategoryTheory.Limits.HasCoequalizers C]
  {G : Type} [Group G] [Fintype G]
  (F : FDRep ℂ G ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]

@[reassoc (attr := simp)]
theorem freeUnit_augmentation (X : C) :
    RelativeTensor.freeUnit (A := (regularAlgebra F)) X ≫
      ((regularAugmentation F) ▷ X) ≫ (λ_ X).hom = 𝟙 X := by
  unfold RelativeTensor.freeUnit
  rw [Category.assoc, ← comp_whiskerRight_assoc, (regular_one_augmentation F),
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

/-- The actual map on free generators associated to an equivariant module
intertwiner is invariant under every actual regular translation. -/
theorem descentGenerator_invariant {X Y : C}
    (f : (descentComparison F).obj X ⟶ (descentComparison F).obj Y) (g : G) :
    (RelativeTensor.freeUnit X ≫ f.hom.hom) ≫ ((regularTranslation F) g ▷ Y) =
      RelativeTensor.freeUnit X ≫ f.hom.hom := by
  have h := congrArg (fun k => k.hom) (f.comm g)
  change f.hom.hom ≫ ((regularTranslation F) g ▷ Y) =
    ((regularTranslation F) g ▷ X) ≫ f.hom.hom at h
  rw [Category.assoc, h, ← Category.assoc, (freeUnit_translation F)]

/-- Recover an actual ambient map from an actual equivariant free-module
intertwiner by the regular-algebra augmentation. -/
def descentUnderlyingMap {X Y : C}
    (f : (descentComparison F).obj X ⟶ (descentComparison F).obj Y) : X ⟶ Y :=
  RelativeTensor.freeUnit X ≫ f.hom.hom ≫ ((regularAugmentation F) ▷ Y) ≫ (λ_ Y).hom

@[reassoc]
theorem descentUnderlyingMap_generator {X Y : C}
    (f : (descentComparison F).obj X ⟶ (descentComparison F).obj Y) :
    (descentUnderlyingMap F) f ≫ RelativeTensor.freeUnit Y =
      RelativeTensor.freeUnit X ≫ f.hom.hom := by
  have h := (invariant_factors_unit F) (RelativeTensor.freeUnit X ≫ f.hom.hom)
    ((descentGenerator_invariant F) f)
  simpa only [descentUnderlyingMap, RelativeTensor.freeUnit,
    Category.assoc, Iso.hom_inv_id_assoc] using h

@[simp]
theorem descentUnderlyingMap_map {X Y : C} (f : X ⟶ Y) :
    (descentUnderlyingMap F) ((descentComparison F).map f) = f := by
  change RelativeTensor.freeUnit X ≫ (InternalModule.freeMap f).hom ≫
    ((regularAugmentation F) ▷ Y) ≫ (λ_ Y).hom = f
  rw [RelativeTensor.freeUnit_naturality_assoc, (freeUnit_augmentation F), Category.comp_id]

@[simp]
theorem descentComparison_map_underlying {X Y : C}
    (f : (descentComparison F).obj X ⟶ (descentComparison F).obj Y) :
    (descentComparison F).map ((descentUnderlyingMap F) f) = f := by
  apply WeakAction.Equivariant.Hom.ext
  apply RelativeTensor.free_hom_ext
  change RelativeTensor.freeUnit X ≫ (InternalModule.freeMap ((descentUnderlyingMap F) f)).hom =
    RelativeTensor.freeUnit X ≫ f.hom.hom
  rw [RelativeTensor.freeUnit_naturality]
  exact (descentUnderlyingMap_generator F) f

/-- The actual descent comparison is full: every equivariant free-module
map is the free extension of the recovered ambient map. -/
instance descentComparisonFull : (descentComparison F).Full where
  map_surjective f := ⟨(descentUnderlyingMap F) f, (descentComparison_map_underlying F) f⟩

/-- The actual descent comparison is faithful, using the actual split
unit of the regular algebra. -/
instance descentComparisonFaithful : (descentComparison F).Faithful where
  map_injective h := by
    have e := congrArg (fun f => (descentUnderlyingMap F) f) h
    simpa only [(descentUnderlyingMap_map F)] using e


end Paper18.Category.FixedBoundary
