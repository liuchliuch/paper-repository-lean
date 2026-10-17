import Paper18.Category.TannakianDescentAverage

/-! # Full faithfulness of the actual Tannakian descent comparison -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

@[reassoc (attr := simp)]
theorem TannakianCenter.freeUnit_augmentation (X : C) :
    RelativeTensor.freeUnit (A := T.regularAlgebra) X ≫
      (T.regularAugmentation ▷ X) ≫ (λ_ X).hom = 𝟙 X := by
  unfold RelativeTensor.freeUnit
  rw [Category.assoc, ← comp_whiskerRight_assoc, T.regular_one_augmentation,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

/-- The actual map on free generators associated to an equivariant module
intertwiner is invariant under every actual regular translation. -/
theorem TannakianCenter.descentGenerator_invariant {X Y : C}
    (f : T.descentComparison.obj X ⟶ T.descentComparison.obj Y) (g : G) :
    (RelativeTensor.freeUnit X ≫ f.hom.hom) ≫ (T.regularTranslation g ▷ Y) =
      RelativeTensor.freeUnit X ≫ f.hom.hom := by
  have h := congrArg (fun k => k.hom) (f.comm g)
  change f.hom.hom ≫ (T.regularTranslation g ▷ Y) =
    (T.regularTranslation g ▷ X) ≫ f.hom.hom at h
  rw [Category.assoc, h, ← Category.assoc, T.freeUnit_translation]

/-- Recover an actual ambient map from an actual equivariant free-module
intertwiner by the regular-algebra augmentation. -/
def TannakianCenter.descentUnderlyingMap {X Y : C}
    (f : T.descentComparison.obj X ⟶ T.descentComparison.obj Y) : X ⟶ Y :=
  RelativeTensor.freeUnit X ≫ f.hom.hom ≫ (T.regularAugmentation ▷ Y) ≫ (λ_ Y).hom

@[reassoc]
theorem TannakianCenter.descentUnderlyingMap_generator {X Y : C}
    (f : T.descentComparison.obj X ⟶ T.descentComparison.obj Y) :
    T.descentUnderlyingMap f ≫ RelativeTensor.freeUnit Y =
      RelativeTensor.freeUnit X ≫ f.hom.hom := by
  have h := T.invariant_factors_unit (RelativeTensor.freeUnit X ≫ f.hom.hom)
    (T.descentGenerator_invariant f)
  simpa only [TannakianCenter.descentUnderlyingMap, RelativeTensor.freeUnit,
    Category.assoc, Iso.hom_inv_id_assoc] using h

@[simp]
theorem TannakianCenter.descentUnderlyingMap_map {X Y : C} (f : X ⟶ Y) :
    T.descentUnderlyingMap (T.descentComparison.map f) = f := by
  change RelativeTensor.freeUnit X ≫ (InternalModule.freeMap f).hom ≫
    (T.regularAugmentation ▷ Y) ≫ (λ_ Y).hom = f
  rw [RelativeTensor.freeUnit_naturality_assoc, T.freeUnit_augmentation, Category.comp_id]

@[simp]
theorem TannakianCenter.descentComparison_map_underlying {X Y : C}
    (f : T.descentComparison.obj X ⟶ T.descentComparison.obj Y) :
    T.descentComparison.map (T.descentUnderlyingMap f) = f := by
  apply WeakAction.Equivariant.Hom.ext
  apply RelativeTensor.free_hom_ext
  change RelativeTensor.freeUnit X ≫ (InternalModule.freeMap (T.descentUnderlyingMap f)).hom =
    RelativeTensor.freeUnit X ≫ f.hom.hom
  rw [RelativeTensor.freeUnit_naturality]
  exact T.descentUnderlyingMap_generator f

/-- The actual descent comparison is full: every equivariant free-module
map is the free extension of the recovered ambient map. -/
instance TannakianCenter.descentComparisonFull : T.descentComparison.Full where
  map_surjective f := ⟨T.descentUnderlyingMap f, T.descentComparison_map_underlying f⟩

/-- The actual descent comparison is faithful, using the actual split
unit of the regular algebra. -/
instance TannakianCenter.descentComparisonFaithful : T.descentComparison.Faithful where
  map_injective h := by
    have e := congrArg (fun f => T.descentUnderlyingMap f) h
    simpa only [T.descentUnderlyingMap_map] using e

end Paper18.Category
